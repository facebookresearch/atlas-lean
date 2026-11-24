/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Sum-product covering over a prime field

We count incidences with nonvertical affine lines. A point lies on one line for each slope,
and distinct points share at most one line. The resulting variance bound limits the number
of lines missing a given point set.
-/

namespace MetaMathlibExt

open scoped BigOperators Pointwise

/-- The line with parameters `(d, b)` consists of the points `(x, y)` with `x * d + y = b`. -/
private def onLine {p : ℕ} (l x : ZMod p × ZMod p) : Prop :=
  x.1 * l.1 + x.2 = l.2

private instance {p : ℕ} (l x : ZMod p × ZMod p) : Decidable (onLine l x) :=
  inferInstanceAs (Decidable (x.1 * l.1 + x.2 = l.2))

private theorem card_lines_through {p : ℕ} [Fact p.Prime] (x : ZMod p × ZMod p) :
    (Finset.univ.filter fun l => onLine l x).card = p := by
  classical
  let through : ZMod p ↪ ZMod p × ZMod p :=
    ⟨fun d => (d, x.1 * d + x.2), fun _ _ h => congrArg Prod.fst h⟩
  have heq : (Finset.univ.filter fun l => onLine l x) = Finset.univ.map through := by
    apply Finset.ext
    intro l
    constructor
    · intro hl
      exact Finset.mem_map.mpr ⟨l.1, Finset.mem_univ _, Prod.ext rfl (Finset.mem_filter.mp hl).2⟩
    · intro hl
      obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rw [heq, Finset.card_map, Finset.card_univ, ZMod.card]

private theorem line_eq_of_two_points {p : ℕ} [Fact p.Prime] {x y l m : ZMod p × ZMod p}
    (hxy : x ≠ y) (hlx : onLine l x) (hly : onLine l y) (hmx : onLine m x) (hmy : onLine m y) :
    l = m := by
  unfold onLine at hlx hly hmx hmy
  have hx : x.1 ≠ y.1 := by
    intro heq
    apply hxy
    exact Prod.ext heq (add_left_cancel (by simpa only [heq] using hlx.trans hly.symm))
  have hzero : (x.1 - y.1) * (l.1 - m.1) = 0 := by
    linear_combination hlx - hly - hmx + hmy
  have hSlope : l.1 = m.1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hx))
  refine Prod.ext hSlope ?_
  calc
    l.2 = x.1 * l.1 + x.2 := hlx.symm
    _ = x.1 * m.1 + x.2 := by rw [hSlope]
    _ = m.2 := hmx

private theorem card_empty_lines_mul_le {p : ℕ} [Fact p.Prime]
    (P E : Finset (ZMod p × ZMod p)) (hP : 0 < P.card)
    (hE : ∀ l ∈ E, ∀ x ∈ P, ¬ onLine l x) : E.card * P.card ≤ p ^ 3 := by
  classical
  let L : Finset (ZMod p × ZMod p) := Finset.univ
  let w (l x : ZMod p × ZMod p) : ℤ := if onLine l x then 1 else 0
  let n (l : ZMod p × ZMod p) : ℤ := ∑ x ∈ P, w l x
  let q : ℤ := p
  let N : ℤ := P.card
  have hL : (L.card : ℤ) = q ^ 2 := by
    simp [L, q, Fintype.card_prod, ZMod.card, pow_two]
  have hpoint (x : ZMod p × ZMod p) : ∑ l ∈ L, w l x = q := by
    rw [show q = ((L.filter fun l => onLine l x).card : ℤ) from
      congrArg (fun k : ℕ => (k : ℤ)) (card_lines_through x).symm]
    simp only [w, ← Finset.sum_filter, Finset.sum_const, nsmul_one]
  have h₁ : ∑ l ∈ L, n l = q * N := by
    rw [show (∑ l ∈ L, n l) = ∑ x ∈ P, ∑ l ∈ L, w l x from Finset.sum_comm]
    simp [hpoint, N, mul_comm]
  have hpair (x y : ZMod p × ZMod p) :
      ∑ l ∈ L, w l x * w l y ≤ (if x = y then q else 0) + 1 := by
    have hcount : ∑ l ∈ L, w l x * w l y =
        ((L.filter fun l => onLine l x ∧ onLine l y).card : ℤ) := by
      rw [← nsmul_one, ← Finset.sum_const, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hx : onLine l x <;> by_cases hy : onLine l y <;> simp [w, hx, hy]
    rw [hcount]
    by_cases hxy : x = y
    · subst y
      simp only [and_self, L, card_lines_through]
      exact le_add_of_nonneg_right zero_le_one
    · simp only [ite_eq_right hxy, zero_add]
      have hcard : (L.filter fun l => onLine l x ∧ onLine l y).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro l hl m hm
        have hl' := (Finset.mem_filter.mp hl).2
        have hm' := (Finset.mem_filter.mp hm).2
        exact line_eq_of_two_points hxy hl'.1 hl'.2 hm'.1 hm'.2
      exact_mod_cast hcard
  have h₂ : ∑ l ∈ L, n l ^ 2 ≤ q * N + N ^ 2 := by
    calc
      ∑ l ∈ L, n l ^ 2 = ∑ x ∈ P, ∑ y ∈ P, ∑ l ∈ L, w l x * w l y := by
        simp_rw [n, pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm (s := L) (t := P)]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ ≤ ∑ x ∈ P, ∑ y ∈ P, ((if x = y then q else 0) + 1) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
      _ = q * N + N ^ 2 := by
        calc
          _ = ∑ _ ∈ P, (q + N) := Finset.sum_congr rfl fun x hx => by
            simp [Finset.sum_add_distrib, hx, N]
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, N]; ring
  -- The variance about the mean `N / p`, scaled by `p²` to stay integral.
  have hvar : ∑ l ∈ L, (q * n l - N) ^ 2 ≤ q ^ 3 * N := by
    calc
      _ = q ^ 2 * (∑ l ∈ L, n l ^ 2) - 2 * q * N * (∑ l ∈ L, n l) +
          (L.card : ℤ) * N ^ 2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
          ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ q ^ 2 * (q * N + N ^ 2) - 2 * q * N * (∑ l ∈ L, n l) +
          (L.card : ℤ) * N ^ 2 := by
        exact add_le_add_left
          (sub_le_sub_right (mul_le_mul_of_nonneg_left h₂ (sq_nonneg q)) _) _
      _ = q ^ 3 * N := by rw [h₁, hL]; ring
  have hmiss : (E.card : ℤ) * N ^ 2 ≤ ∑ l ∈ L, (q * n l - N) ^ 2 := by
    calc
      _ = ∑ l ∈ E, (q * n l - N) ^ 2 := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro l hl
        have hn : n l = 0 := Finset.sum_eq_zero fun x hx => ite_eq_right (hE l hl x hx)
        rw [hn, mul_zero, zero_sub, neg_sq]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ => sq_nonneg _
  have hN : 0 < N := by
    change (0 : ℤ) < (P.card : ℤ)
    exact_mod_cast hP
  have hend : (E.card : ℤ) * N ≤ q ^ 3 := by
    apply le_of_mul_le_mul_right ?_ hN
    calc
      _ = (E.card : ℤ) * N ^ 2 := by ring
      _ ≤ q ^ 3 * N := hmiss.trans hvar
  change (E.card : ℤ) * (P.card : ℤ) ≤ (p : ℤ) ^ 3 at hend
  exact_mod_cast hend

/-- **Sum-product sets cover the integers modulo a prime.** Let $p$ be a prime and let
$A_1, A_2, A_3, D$ be subsets of $\mathbb{Z}/p\mathbb{Z}$ with $|A_1| |A_2| |A_3| |D| > p^3$.
Then every residue class modulo $p$ can be written as $a_1 d + a_2 + a_3$ with $a_1 \in A_1$,
$d \in D$, $a_2 \in A_2$ and $a_3 \in A_3$; that is, $A_1 D + A_2 + A_3 = \mathbb{Z}/p\mathbb{Z}$.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 3
(`integers-2026-A14-lem-3`), quoting Lemma 8.3 of their reference [5] (a consequence of
Sárközy's Corollary A). -/
public theorem product_add_add_eq_univ_of_card_mul_gt (p : ℕ) [Fact p.Prime]
    (A₁ A₂ A₃ D : Finset (ZMod p))
    (h : p ^ 3 < A₁.card * A₂.card * A₃.card * D.card) :
    A₁ * D + A₂ + A₃ = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro t
  by_contra ht
  let lines : ZMod p × ZMod p ↪ ZMod p × ZMod p :=
    ⟨fun z => (z.1, t - z.2), fun v w hvw => by
      have hs := congrArg Prod.fst hvw
      have hb := congrArg Prod.snd hvw
      exact Prod.ext hs (sub_right_injective hb)⟩
  have hP : 0 < (A₁ ×ˢ A₂).card := by
    rw [Finset.card_product]
    by_contra! hzero
    rw [Nat.eq_zero_of_le_zero hzero, zero_mul, zero_mul] at h
    exact Nat.not_lt_zero _ h
  have hbound := card_empty_lines_mul_le (A₁ ×ˢ A₂) ((D ×ˢ A₃).map lines) hP (by
    intro l hl x hx hinc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hl
    obtain ⟨hd, h₃⟩ := Finset.mem_product.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hx
    change x.1 * z.1 + x.2 = t - z.2 at hinc
    exact ht (Finset.mem_add.mpr ⟨_, Finset.mem_add.mpr
      ⟨_, Finset.mul_mem_mul h₁ hd, _, h₂, rfl⟩, _, h₃, eq_sub_iff_add_eq.mp hinc⟩))
  rw [Finset.card_map, Finset.card_product, Finset.card_product] at hbound
  exact (not_le_of_gt h) (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound)

end MetaMathlibExt
