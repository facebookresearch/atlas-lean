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
# The 343-word lower bound for the 7-cycle capacity

We use the packing in Baumert et al., *A combinatorial packing problem*
(1971), Theorem 7, p. 105: words are parameterized by their first three
coordinates, and the last two are linear combinations modulo 7.
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

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
