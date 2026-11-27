/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Exchange formula for interpolation polynomials

For `f : ℤ → ℤ` and a finite set `Y ⊆ ℤ`, `interpolationPoly Y f` is the interpolation polynomial
`f_Y ∈ ℚ[x]` of `f` on `Y`. The main result, `MetaMathlibExt.interpolationPoly_exchange`, is
Borisov's exchange formula (Lemma 6 of *Locally Integer Polynomial Functions*): for a finite set
`X ⊆ ℤ` and `a, b ∉ X`,
`f_{X ∪ {a}} = f_{X ∪ {b}} + c (a - b) ∏_{z ∈ X} (x - z)`,
where `c` is the coefficient of `x^{|X|+1}` in `f_{X ∪ {a, b}}`.

The proof follows the source. A polynomial of degree at most `|S|` that vanishes on a finite set
`S` is its coefficient of `x^{|S|}` times `∏_{z ∈ S} (x - z)`. Hence
`f_{X ∪ {a, b}} = f_{X ∪ {d}} + c (x - d) ∏_{z ∈ X} (x - z)` for `d = a` and for `d = b`, and
subtracting these two identities gives the formula. The source writes disjoint unions, so it
assumes `a ≠ b`; the statement here also allows `a = b`, where both sides agree trivially.
-/

open Polynomial

namespace MetaMathlibExt

/-- A rational polynomial of degree at most `|S|` that vanishes on a finite set `S` of integers
is its coefficient of `x^{|S|}` times `∏_{z ∈ S} (x - z)`. -/
private theorem eq_C_coeff_mul_nodal_of_eval_eq_zero (S : Finset ℤ) {q : ℚ[X]}
    (hq : q.degree < ↑(S.card + 1)) (hS : ∀ z ∈ S, q.eval (z : ℚ) = 0) :
    q = C (q.coeff S.card) * Lagrange.nodal S (fun z : ℤ => (z : ℚ)) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero S (v := fun z : ℤ => (z : ℚ))
    Int.cast_injective.injOn ?_ fun z hz => ?_
  · rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sub, coeff_C_mul]
    rcases hm.eq_or_lt with rfl | hlt
    · -- `∏_{z ∈ S} (x - z)` is monic of degree `|S|`.
      have h1 : (Lagrange.nodal S fun z : ℤ => (z : ℚ)).coeff S.card = 1 := by
        simpa only [Lagrange.natDegree_nodal] using
          (Lagrange.nodal_monic (s := S) (v := fun z : ℤ => (z : ℚ))).coeff_natDegree
      rw [h1, mul_one, sub_self]
    · have h2 : (Lagrange.nodal S fun z : ℤ => (z : ℚ)).coeff m = 0 := by
        apply coeff_eq_zero_of_degree_lt
        rw [Lagrange.degree_nodal]
        exact_mod_cast hlt
      have h3 : q.coeff m = 0 := by
        apply coeff_eq_zero_of_degree_lt
        exact hq.trans_le (by exact_mod_cast hlt)
      rw [h2, h3, mul_zero, sub_zero]
  · rw [eval_sub, eval_mul, eval_C, Lagrange.eval_nodal_at_node hz, mul_zero, sub_zero]
    exact hS z hz

/-- **Exchange formula for interpolation polynomials.** Let $f : \mathbb{Z} \to \mathbb{Z}$, and for
a finite set $Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation polynomial
of $f$ on $Y$. Let $X \subseteq \mathbb{Z}$ be finite and $a, b \in \mathbb{Z} \setminus X$, and let
$c$ be the coefficient of $x^{|X|+1}$ in $f_{X \cup \{a, b\}}$. Then
$$f_{X \cup \{a\}} = f_{X \cup \{b\}} + c\,(a - b) \prod_{z \in X} (x - z).$$

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 6 (`integers-2025-A41-lem-6`). -/
public theorem interpolationPoly_exchange (X : Finset ℤ) {a b : ℤ} (ha : a ∉ X)
    (hb : b ∉ X) (f : ℤ → ℤ) :
    interpolationPoly (insert a X) f = interpolationPoly (insert b X) f +
      C ((interpolationPoly (insert a (insert b X)) f).coeff (X.card + 1) * ((a : ℚ) - b)) *
        ∏ z ∈ X, (Polynomial.X - C (z : ℚ)) := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  set P := interpolationPoly (insert a (insert b X)) f with hP
  set c := P.coeff (X.card + 1)
  have hcard : (insert a (insert b X)).card = X.card + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]
  -- For `d = a, b`: `f_{X ∪ {a, b}} = f_{X ∪ {d}} + c (x - d) ∏_{z ∈ X} (x - z)`.
  have key : ∀ d, d ∈ insert a (insert b X) → d ∉ X →
      P = interpolationPoly (insert d X) f +
        C c * ((Polynomial.X - C (d : ℚ)) * ∏ z ∈ X, (Polynomial.X - C (z : ℚ))) := by
    intro d hd hdX
    have hdeg_d := degree_interpolationPoly_lt (insert d X) f
    rw [Finset.card_insert_of_notMem hdX] at hdeg_d
    have hdeg_P := degree_interpolationPoly_lt (insert a (insert b X)) f
    rw [hcard] at hdeg_P
    have h := eq_C_coeff_mul_nodal_of_eval_eq_zero (insert d X)
      (q := P - interpolationPoly (insert d X) f) ?_ ?_
    · rw [Finset.card_insert_of_notMem hdX, coeff_sub,
        coeff_eq_zero_of_degree_lt hdeg_d, sub_zero, Lagrange.nodal_insert_eq_nodal hdX] at h
      rw [sub_eq_iff_eq_add'] at h
      exact h
    · rw [Finset.card_insert_of_notMem hdX]
      rw [← mem_degreeLT] at hdeg_d hdeg_P ⊢
      exact Submodule.sub_mem _ hdeg_P (degreeLT_mono (Nat.le_succ _) hdeg_d)
    · intro z hz
      rw [eval_sub, hP, eval_interpolationPoly f (Finset.mem_of_subset ?_ hz),
        eval_interpolationPoly f hz, sub_self]
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hd
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)
  have hA := key a (Finset.mem_insert_self _ _) ha
  have hB := key b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hb
  rw [C_mul, C_sub]
  linear_combination hB - hA

end MetaMathlibExt
