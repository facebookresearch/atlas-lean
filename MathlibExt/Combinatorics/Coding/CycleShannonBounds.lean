/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.CycleCode
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.Basic

/-!
# Bounds for the 7-cycle capacity

For the lower bound we use the packing in Baumert et al., *A combinatorial packing problem*
(1971), Theorem 7, p. 105: words are parameterized by their first three
coordinates, and the last two are linear combinations modulo 7.

For the upper bound, adding binary offsets to distinct codewords gives disjoint sets of words.
-/

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- The encoder in Baumert et al., Theorem 7. -/
private def encode (u : Fin 3 → ZMod 7) : Fin 5 → ZMod 7 :=
  ![u 0, u 1, u 2, 2 * u 0 + 2 * u 1 + 2 * u 2, 2 * u 0 + 4 * u 1 + 6 * u 2]

private theorem encode_injective : Function.Injective encode := by
  intro u v h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

private theorem encode_sub (u v : Fin 3 → ZMod 7) :
    encode (u - v) = encode u - encode v := by
  funext i
  fin_cases i <;> simp [encode, Pi.sub_apply] <;> ring

private abbrev NearZero (a : ZMod 7) : Prop := a = -1 ∨ a = 0 ∨ a = 1

/-- Of the triples with all entries in `{-1, 0, 1}`, only the zero triple
also has both parity coordinates in `{-1, 0, 1}`. -/
private theorem parity_certificate (a b c : ZMod 7)
    (ha : NearZero a) (hb : NearZero b) (hc : NearZero c) :
    NearZero (2 * a + 2 * b + 2 * c) → NearZero (2 * a + 4 * b + 6 * c) →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> decide

private theorem encode_eq_zero_of_small (u : Fin 3 → ZMod 7)
    (h : ∀ i, NearZero (encode u i)) : u = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := parity_certificate (u 0) (u 1) (u 2) (h 0) (h 1) (h 2) (h 3) (h 4)
  funext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

/-- **Baumert et al. lower bound for the capacity of the 7-cycle.** The Shannon capacity of the
$7$-cycle is at least $343^{1/5}$, as an inequality in $[0, \infty]$.

Source: Baumert--McEliece--Rodemich--Rumsey--Stanley--Taylor (1971), exact rate row. -/
public theorem bmrrst1971LowerBound :
    ENNReal.rpow 343 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 := by
  apply cycleConstruction_implies_lowerBound 7 5 343 (by decide)
  let A := Finset.univ.map ⟨encode, encode_injective⟩
  refine ⟨A, ?_, ?_⟩
  · intro x hx hsmall
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hb
    simp only [Function.Embedding.coeFn_mk] at hsmall ⊢
    rw [← encode_sub] at hsmall ⊢
    rw [encode_eq_zero_of_small (u - v) hsmall]
    decide
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl

private def bitOffset (b : Bool) : ZMod 7 := if b then 1 else 0

private theorem bitOffset_injective : Function.Injective bitOffset := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact ((by decide : (0 : ZMod 7) ≠ 1) h).elim
  · exact ((by decide : (1 : ZMod 7) ≠ 0) h).elim
  · rfl

/-- The binary translates of the codewords are disjoint, giving a packing in all words. -/
private theorem cycleSeven_card_mul_two_pow_le {n : ℕ} {A : Finset (Fin n → ZMod 7)}
    (hA : IsCycleCode 7 A) : A.card * 2 ^ n ≤ 7 ^ n := by
  classical
  let translate : A × (Fin n → Bool) → (Fin n → ZMod 7) :=
    fun (a, ε) i ↦ a.val i + bitOffset (ε i)
  have hinj : Function.Injective translate := by
    rintro ⟨a, ε⟩ ⟨b, δ⟩ h
    have hsmall (i : Fin n) :
        (a.val - b.val) i = -1 ∨ (a.val - b.val) i = 0 ∨ (a.val - b.val) i = 1 := by
      have hi : a.val i + bitOffset (ε i) = b.val i + bitOffset (δ i) := congrFun h i
      have hdiff : (a.val - b.val) i = bitOffset (δ i) - bitOffset (ε i) :=
        sub_eq_sub_iff_add_eq_add.mpr (hi.trans (add_comm _ _))
      rw [hdiff]
      cases ε i <;> cases δ i <;> simp [bitOffset]
    have hzero := hA (a.val - b.val) ⟨a.val, a.property, b.val, b.property, rfl⟩ hsmall
    have hab : a = b := Subtype.ext (sub_eq_zero.mp hzero)
    subst b
    refine Prod.ext rfl (funext fun i ↦ ?_)
    have hi : a.val i + bitOffset (ε i) = a.val i + bitOffset (δ i) := congrFun h i
    exact bitOffset_injective (add_left_cancel hi)
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, ZMod.card] using Fintype.card_le_of_injective translate hinj

/-- **Shannon's upper bound for the capacity of the 7-cycle.** The Shannon capacity of the
$7$-cycle is at most $7/2$.

Source: Shannon (1956), the fractional-clique-cover upper bound. -/
public theorem shannon1956UpperBound :
    shannonCapacityCycle 7 ≤ (7 : ENNReal) / 2 := by
  unfold shannonCapacityCycle
  refine iSup_le fun n ↦ iSup_le fun A ↦ ?_
  have hn : 0 < (n.1 : ℝ) := Nat.cast_pos.mpr n.property
  have hcard : (A.1.card : ENNReal) * 2 ^ n.1 ≤ 7 ^ n.1 := by
    exact_mod_cast cycleSeven_card_mul_two_pow_le A.property
  change (A.1.card : ENNReal) ^ ((n.1 : ℝ)⁻¹) ≤ _
  rw [ENNReal.rpow_inv_le_iff hn, ENNReal.rpow_natCast]
  have hdiv : (A.1.card : ENNReal) ≤ (7 : ENNReal) ^ n.1 / 2 ^ n.1 :=
    (ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))).2 hcard
  simpa only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow] using hdiv

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
