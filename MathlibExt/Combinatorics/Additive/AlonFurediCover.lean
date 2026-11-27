/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Nullstellensatz

/-!
# Covering the cube minus one vertex by hyperplanes (Alon–Füredi)

If finitely many hyperplanes cover all vertices of the cube `{0, 1}^n` but one, there are at least
`n` of them (N. Alon and Z. Füredi, "Covering the cube by affine hyperplanes", European J. Combin.
14 (1993) 79–83; Theorem 6.3 of N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput.
8 (1999) 7–29, whose proof is formalized here). The bound is tight: the `n` hyperplanes
`x_j = 1` cover every vertex except `0`.

## Proof

With `v` the uncovered vertex and `Hᵢ = {x : aᵢ · x = bᵢ}`, the polynomial
`P = ∏ᵢ (aᵢ · x - bᵢ) - δ ∏_j (x_j - (1 - v_j))`, with `δ` chosen so that `P(v) = 0`, vanishes on
the whole cube. If there were fewer than `n` hyperplanes, the coefficient of `x₁ ⋯ x_n` in `P`
would be `-δ ≠ 0` and `P` would have degree `n`, so the Combinatorial Nullstellensatz would give a
vertex where `P ≠ 0`.
-/

@[expose] public section

open Finset MvPolynomial

namespace MathlibExt.Combinatorics.Additive.AlonFurediCover

variable {F : Type*} [Field F] {n : ℕ}

/-- The product `∏_j (X_j - C c_j)` minus `∏_j X_j` has total degree less than `n`. -/
private theorem totalDegree_prod_X_sub_C_sub_lt (hn : 0 < n) (c : Fin n → F) :
    (∏ j, (X j - C (c j)) - ∏ j, (X j : MvPolynomial (Fin n) F)).totalDegree < n := by
  classical
  have hexp : ∏ j, (X j - C (c j) : MvPolynomial (Fin n) F) - ∏ j, X j =
      ∑ t ∈ (univ : Finset (Fin n)).powerset.erase univ,
        (∏ j ∈ t, (X j : MvPolynomial (Fin n) F)) * ∏ j ∈ univ \ t, (-C (c j)) := by
    simp_rw [sub_eq_add_neg (X _)]
    rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (mem_powerset_self univ)]
    simp
  rw [hexp]
  refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_lt_iff (by omega)]
  intro t ht
  have htlt : t.card < n := by
    have hsub : t ⊂ univ := lt_of_le_of_ne (mem_powerset.1 (mem_of_mem_erase ht))
      (ne_of_mem_erase ht)
    simpa using card_lt_card hsub
  refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
  have h1 : (∏ j ∈ t, (X j : MvPolynomial (Fin n) F)).totalDegree ≤ t.card := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ j ∈ t, (X j : MvPolynomial (Fin n) F).totalDegree ≤ ∑ _j ∈ t, 1 :=
          Finset.sum_le_sum fun j _ => by simp [totalDegree_X]
      _ = t.card := by simp
  have h2 : (∏ j ∈ univ \ t, (-C (c j)) : MvPolynomial (Fin n) F).totalDegree = 0 := by
    have : (∏ j ∈ univ \ t, (-C (c j)) : MvPolynomial (Fin n) F) = C (∏ j ∈ univ \ t, -c j) := by
      simp [map_prod]
    rw [this, totalDegree_C]
  omega

/-- The monomial `x₁ x₂ ⋯ x_n`. -/
private theorem prod_X_eq_monomial :
    ∏ j, (X j : MvPolynomial (Fin n) F) = monomial (∑ j, Finsupp.single j 1) 1 := by
  classical
  induction (univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj, ih, X, monomial_mul_monomial, mul_one]

/-- **Covering the cube minus a vertex by hyperplanes (Alon–Füredi).** Let `F` be a field and
`Hᵢ = {x : ∑_j aᵢⱼ xⱼ = bᵢ}`, `i < m`, finitely many affine hyperplanes of `Fⁿ`. If every vertex of
the cube `{0, 1}ⁿ` other than a vertex `v` lies on some `Hᵢ` and `v` lies on none, then `n ≤ m`
(N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999), Theorem 6.3, stated
there in `ℝⁿ`; N. Alon and Z. Füredi, European J. Combin. 14 (1993)). The coefficient vectors
`aᵢ` are not required to be nonzero: a degenerate "hyperplane" `0 = bᵢ` with `bᵢ ≠ 0` is empty
and does not help. -/
theorem le_card_of_covers {m : ℕ} (a : Fin m → Fin n → F) (b : Fin m → F) (v : Fin n → F)
    (hv : ∀ j, v j = 0 ∨ v j = 1)
    (hcover : ∀ x : Fin n → F, (∀ j, x j = 0 ∨ x j = 1) → x ≠ v → ∃ i, ∑ j, a i j * x j = b i)
    (hmiss : ∀ i, ∑ j, a i j * v j ≠ b i) : n ≤ m := by
  classical
  by_contra hlt
  push Not at hlt
  have hn : 0 < n := by omega
  -- The two products.
  set L : MvPolynomial (Fin n) F := ∏ i, ((∑ j, C (a i j) * X j) - C (b i)) with hL
  set c : Fin n → F := fun j => 1 - v j with hc
  set V : MvPolynomial (Fin n) F := ∏ j, (X j - C (c j)) with hV
  have hLv : eval v L ≠ 0 := by
    simp only [hL, map_prod, map_sub, map_sum, map_mul, eval_C, eval_X]
    exact Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (hmiss i)
  have hVv : eval v V ≠ 0 := by
    simp only [hV, map_prod, map_sub, eval_C, eval_X, hc]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rcases hv j with h | h <;> simp [h]
  set δ : F := eval v L / eval v V with hδ
  have hδ0 : δ ≠ 0 := div_ne_zero hLv hVv
  set P : MvPolynomial (Fin n) F := L - C δ * V with hP
  -- `P` vanishes on the cube.
  have hvanish : ∀ x : Fin n → F, (∀ j, x j ∈ ({0, 1} : Finset F)) → eval x P = 0 := by
    intro x hx
    have hx' : ∀ j, x j = 0 ∨ x j = 1 := fun j => by simpa using hx j
    by_cases hxv : x = v
    · rw [hxv]
      simp only [hP, map_sub, map_mul, eval_C, hδ]
      rw [div_mul_cancel₀ _ hVv, sub_self]
    · obtain ⟨i, hi⟩ := hcover x hx' hxv
      have hL0 : eval x L = 0 := by
        simp only [hL, map_prod, map_sub, map_sum, map_mul, eval_C, eval_X]
        exact Finset.prod_eq_zero (mem_univ i) (sub_eq_zero.2 hi)
      have hV0 : eval x V = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, x j ≠ v j := by
          by_contra h; push Not at h; exact hxv (funext h)
        simp only [hV, map_prod, map_sub, eval_C, eval_X]
        refine Finset.prod_eq_zero (mem_univ j) (sub_eq_zero.2 ?_)
        simp only [hc]
        rcases hx' j with h1 | h1 <;> rcases hv j with h2 | h2 <;> rw [h1, h2] at hj ⊢ <;>
          simp_all
      simp [hP, hL0, hV0]
  -- Degrees and the coefficient of `x₁ ⋯ x_n`.
  set t : Fin n →₀ ℕ := ∑ j, Finsupp.single j 1 with ht
  have htdeg : t.degree = n := by
    rw [ht, map_sum]
    simp [Finsupp.degree_single]
  have hLdeg : L.totalDegree ≤ m := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, ((∑ j, C (a i j) * X j) - C (b i) : MvPolynomial (Fin n) F).totalDegree
        ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => by
          refine (totalDegree_sub _ _).trans (max_le ?_ (by simp [totalDegree_C]))
          refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
          exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])
      _ = m := by simp
  have hLcoeff : L.coeff t = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    have : t.degree = ∑ i ∈ t.support, t i := rfl
    rw [← this, htdeg]; omega
  have hVcoeff : V.coeff t = 1 := by
    have hsplit : V = ∏ j, (X j : MvPolynomial (Fin n) F) + (V - ∏ j, X j) := by ring
    rw [hsplit, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, prod_X_eq_monomial,
      coeff_monomial, ite_eq_left rfl]
    rw [coeff_eq_zero_of_totalDegree_lt, add_zero]
    have : t.degree = ∑ i ∈ t.support, t i := rfl
    rw [← this, htdeg]
    have hrest := totalDegree_prod_X_sub_C_sub_lt hn c
    rw [prod_X_eq_monomial] at hrest
    exact hrest
  have hPcoeff : P.coeff t = -δ := by
    rw [hP, sub_eq_add_neg, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hLcoeff, zero_add,
      ← neg_mul, ← map_neg, coeff_C_mul, hVcoeff, mul_one]
  have hPne : P.coeff t ≠ 0 := by rw [hPcoeff]; exact neg_ne_zero.2 hδ0
  have hPdeg : P.totalDegree = t.degree := by
    refine le_antisymm ?_ ?_
    · rw [htdeg, hP]
      refine (totalDegree_sub _ _).trans (max_le (by omega) ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_finsetProd _ _).trans ?_
      calc ∑ j, (X j - C (c j) : MvPolynomial (Fin n) F).totalDegree ≤ ∑ _j : Fin n, 1 :=
            Finset.sum_le_sum fun j _ =>
              (totalDegree_sub _ _).trans (max_le (by simp [totalDegree_X]) (by simp))
        _ = n := by simp
    · have : t.degree = ∑ i ∈ t.support, t i := rfl
      rw [this]
      exact le_totalDegree (mem_support_iff.2 hPne)
  obtain ⟨x, hx, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero P t hPne hPdeg
    (fun _ => {0, 1}) fun j => by
      have : t j = 1 := by simp [ht, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [this]
      simp
  exact hne (hvanish x hx)

end MathlibExt.Combinatorics.Additive.AlonFurediCover
