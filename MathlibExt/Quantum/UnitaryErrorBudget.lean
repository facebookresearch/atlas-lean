/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Star.StarProjection

/-!
# Unitary error budgets

Telescoping operator-norm bounds for products of unitary matrices and the
induced perturbation bound for a quadratic form determined by an orthogonal
projection. The statements follow Kitaev, Shen and Vyalyi, Classical and
Quantum Computation, Section 8.2 and Problem 9.2 with its solution.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

namespace MathlibExt.Quantum.UnitaryErrorBudget

/-- A nonempty list product of elements of norm at most one has norm at
most one. -/
private theorem norm_list_prod_le_one_of_ne_nil {R : Type*} [NormedRing R]
    {l : List R} (h : ∀ x ∈ l, ‖x‖ ≤ 1) (hne : l ≠ []) : ‖l.prod‖ ≤ 1 := by
  revert h hne
  induction l with
  | nil => intro h hne; exact absurd rfl hne
  | cons a l ih =>
    intro h hne
    by_cases hl : l = []
    · subst hl
      rw [List.prod_cons, List.prod_nil, mul_one]
      exact h a (by simp)
    · have ha : ‖a‖ ≤ 1 := h a (by simp)
      have hl' : ∀ x ∈ l, ‖x‖ ≤ 1 := fun x hx => h x (by simp [hx])
      rw [List.prod_cons]
      calc ‖a * l.prod‖ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul ha (ih hl' hl) (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1

/-- A unitary matrix has operator norm at most one. -/
private theorem norm_mem_unitaryGroup_le_one {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ‖U‖ ≤ 1 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · have hU0 : U = 0 := Matrix.ext fun i _ => IsEmpty.elim hn i
    rw [hU0, norm_zero]
    exact zero_le_one
  · have hnt : Nontrivial (Matrix n n ℂ) := @Matrix.nonempty _ _ _ hn hn _
    exact (@CStarRing.norm_of_mem_unitary _ _ _ _ hnt _ hU).le

/-- The operator norm is invariant under `star` for complex matrices. -/
private theorem norm_star_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ‖star X‖ = ‖X‖ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]

/-- Telescoping bound for two products in a normed ring. -/
theorem norm_list_ofFn_prod_sub_le {R : Type*} [NormedRing R] {T : ℕ}
    (u v : Fin T → R) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖(List.ofFn u).prod - (List.ofFn v).prod‖ ≤ ∑ i, ‖u i - v i‖ := by
  suffices h : ∀ (T : ℕ) (u v : Fin T → R), (∀ i, ‖u i‖ ≤ 1) →
      (∀ i, ‖v i‖ ≤ 1) →
      ‖(List.ofFn u).prod - (List.ofFn v).prod‖ ≤ ∑ i, ‖u i - v i‖ from
    h T u v hu hv
  intro T
  induction T with
  | zero =>
    intro u v _ _
    simp only [List.ofFn_zero, List.prod_nil, sub_self, norm_zero]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  | succ T ih =>
    intro u v hu hv
    by_cases hT : T = 0
    · subst hT
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
        Fin.sum_univ_succ, List.ofFn_zero, List.ofFn_zero, List.prod_nil,
        mul_one, mul_one]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun i _ => norm_nonneg _)
    · rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
        Fin.sum_univ_succ]
      have hPne : (List.ofFn fun i : Fin T => u i.succ) ≠ [] := by
        intro hcon
        rw [List.ofFn_eq_nil_iff] at hcon
        exact hT hcon
      have hQne : (List.ofFn fun i : Fin T => v i.succ) ≠ [] := by
        intro hcon
        rw [List.ofFn_eq_nil_iff] at hcon
        exact hT hcon
      have hP : ‖(List.ofFn fun i : Fin T => u i.succ).prod‖ ≤ 1 :=
        norm_list_prod_le_one_of_ne_nil (fun x hx => by
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
          rw [← hi]
          exact hu _) hPne
      have hQ : ‖(List.ofFn fun i : Fin T => v i.succ).prod‖ ≤ 1 :=
        norm_list_prod_le_one_of_ne_nil (fun x hx => by
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
          rw [← hi]
          exact hv _) hQne
      have ih' := ih (fun i : Fin T => u i.succ) (fun i : Fin T => v i.succ)
        (fun i => hu _) (fun i => hv _)
      have hdecomp : ∀ a b P Q : R, a * P - b * Q = (a - b) * P + b * (P - Q) := by
        intro a b P Q
        simp only [sub_mul, mul_sub]
        abel
      rw [hdecomp]
      have g1 : ‖(u 0 - v 0) * (List.ofFn fun i : Fin T => u i.succ).prod‖ ≤
          ‖u 0 - v 0‖ :=
        le_trans (norm_mul_le _ _) (mul_le_of_le_one_right (norm_nonneg _) hP)
      have g2 : ‖v 0 * ((List.ofFn fun i : Fin T => u i.succ).prod -
          (List.ofFn fun i : Fin T => v i.succ).prod)‖ ≤
          ∑ i : Fin T, ‖u i.succ - v i.succ‖ :=
        le_trans (norm_mul_le _ _)
          (le_trans (mul_le_of_le_one_left (norm_nonneg _) (hv 0)) ih')
      calc ‖(u 0 - v 0) * (List.ofFn fun i : Fin T => u i.succ).prod +
            v 0 * ((List.ofFn fun i : Fin T => u i.succ).prod -
              (List.ofFn fun i : Fin T => v i.succ).prod)‖
          ≤ ‖(u 0 - v 0) * (List.ofFn fun i : Fin T => u i.succ).prod‖ +
            ‖v 0 * ((List.ofFn fun i : Fin T => u i.succ).prod -
              (List.ofFn fun i : Fin T => v i.succ).prod)‖ := norm_add_le _ _
        _ ≤ ‖u 0 - v 0‖ + ∑ i : Fin T, ‖u i.succ - v i.succ‖ :=
          add_le_add g1 g2

/-- Chronological product of a gate family: index `0` is the first gate applied
to the state, so the total operator is `U (T - 1) * ... * U 1 * U 0`. -/
def circuitProd {R : Type*} [Monoid R] {T : ℕ} (U : Fin T → R) : R :=
  (List.ofFn U).reverse.prod

/-- Telescoping bound for two chronological circuit products in a normed
ring. -/
private theorem norm_circuitProd_sub_le {R : Type*} [NormedRing R] {T : ℕ}
    (u v : Fin T → R) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖circuitProd u - circuitProd v‖ ≤ ∑ i, ‖u i - v i‖ := by
  suffices h : ∀ (T : ℕ) (u v : Fin T → R), (∀ i, ‖u i‖ ≤ 1) →
      (∀ i, ‖v i‖ ≤ 1) →
      ‖circuitProd u - circuitProd v‖ ≤ ∑ i, ‖u i - v i‖ from
    h T u v hu hv
  intro T
  induction T with
  | zero =>
    intro u v _ _
    simp only [circuitProd, List.ofFn_zero, List.reverse_nil, List.prod_nil,
      sub_self, norm_zero]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  | succ T ih =>
    intro u v hu hv
    by_cases hT : T = 0
    · subst hT
      have hu0 : circuitProd u = u 0 := by
        simp [circuitProd, List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
          List.reverse_nil, List.prod_append, List.prod_cons, List.prod_nil]
      have hv0 : circuitProd v = v 0 := by
        simp [circuitProd, List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
          List.reverse_nil, List.prod_append, List.prod_cons, List.prod_nil]
      rw [hu0, hv0, Fin.sum_univ_succ]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun i _ => norm_nonneg _)
    · have hunfold : circuitProd u
          = circuitProd (fun i : Fin T => u i.succ) * u 0 := by
        simp only [circuitProd, List.ofFn_succ, List.reverse_cons,
          List.prod_append, List.prod_cons, List.prod_nil, mul_one]
      have hvnfold : circuitProd v
          = circuitProd (fun i : Fin T => v i.succ) * v 0 := by
        simp only [circuitProd, List.ofFn_succ, List.reverse_cons,
          List.prod_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hunfold, hvnfold, Fin.sum_univ_succ]
      have hPne : (List.ofFn fun i : Fin T => u i.succ) ≠ [] := by
        intro hcon
        rw [List.ofFn_eq_nil_iff] at hcon
        exact hT hcon
      have hQne : (List.ofFn fun i : Fin T => v i.succ) ≠ [] := by
        intro hcon
        rw [List.ofFn_eq_nil_iff] at hcon
        exact hT hcon
      have hPrev_ne : (List.ofFn fun i : Fin T => u i.succ).reverse ≠ [] := by
        intro hcon
        have h := congrArg List.reverse hcon
        simp only [List.reverse_reverse, List.reverse_nil] at h
        exact hPne h
      have hQrev_ne : (List.ofFn fun i : Fin T => v i.succ).reverse ≠ [] := by
        intro hcon
        have h := congrArg List.reverse hcon
        simp only [List.reverse_reverse, List.reverse_nil] at h
        exact hQne h
      have hP : ‖circuitProd (fun i : Fin T => u i.succ)‖ ≤ 1 := by
        show ‖(List.ofFn fun i : Fin T => u i.succ).reverse.prod‖ ≤ 1
        exact norm_list_prod_le_one_of_ne_nil (fun x hx => by
          rw [List.mem_reverse] at hx
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
          rw [← hi]
          exact hu _) hPrev_ne
      have hQ : ‖circuitProd (fun i : Fin T => v i.succ)‖ ≤ 1 := by
        show ‖(List.ofFn fun i : Fin T => v i.succ).reverse.prod‖ ≤ 1
        exact norm_list_prod_le_one_of_ne_nil (fun x hx => by
          rw [List.mem_reverse] at hx
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
          rw [← hi]
          exact hv _) hQrev_ne
      have ih' := ih (fun i : Fin T => u i.succ) (fun i : Fin T => v i.succ)
        (fun i => hu _) (fun i => hv _)
      have hdecomp : ∀ P Q a b : R,
          P * a - Q * b = Q * (a - b) + (P - Q) * a := by
        intro P Q a b
        simp only [sub_mul, mul_sub]
        abel
      rw [hdecomp]
      have g1 : ‖circuitProd (fun i : Fin T => v i.succ) * (u 0 - v 0)‖ ≤
          ‖u 0 - v 0‖ :=
        le_trans (norm_mul_le _ _) (mul_le_of_le_one_left (norm_nonneg _) hQ)
      have g2 : ‖(circuitProd (fun i : Fin T => u i.succ) -
          circuitProd (fun i : Fin T => v i.succ)) * u 0‖ ≤
          ∑ i : Fin T, ‖u i.succ - v i.succ‖ :=
        le_trans (norm_mul_le _ _)
          (le_trans (mul_le_of_le_one_right (norm_nonneg _) (hu 0)) ih')
      calc ‖circuitProd (fun i : Fin T => v i.succ) * (u 0 - v 0) +
            (circuitProd (fun i : Fin T => u i.succ) -
              circuitProd (fun i : Fin T => v i.succ)) * u 0‖
          ≤ ‖circuitProd (fun i : Fin T => v i.succ) * (u 0 - v 0)‖ +
            ‖(circuitProd (fun i : Fin T => u i.succ) -
              circuitProd (fun i : Fin T => v i.succ)) * u 0‖ :=
            norm_add_le _ _
        _ ≤ ‖u 0 - v 0‖ + ∑ i : Fin T, ‖u i.succ - v i.succ‖ :=
          add_le_add g1 g2

/-- Operator-norm errors from replacing unitary gates add at most linearly. -/
theorem norm_circuit_sub_le {n : Type*} [Fintype n] [DecidableEq n] {T : ℕ}
    (U V : Fin T → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup n ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup n ℂ)
    (ε : Fin T → ℝ) (hε : ∀ i, ‖U i - V i‖ ≤ ε i) :
    ‖circuitProd U - circuitProd V‖ ≤ ∑ i, ε i := by
  have h := norm_circuitProd_sub_le U V
    (fun i => norm_mem_unitaryGroup_le_one (hU i))
    (fun i => norm_mem_unitaryGroup_le_one (hV i))
  exact le_trans h (Finset.sum_le_sum fun i _ => hε i)

/-- Perturbation bound for one projection quadratic form under conjugation. -/
theorem norm_inner_conj_sub_le {n : Type*} [Fintype n] [DecidableEq n]
    {U V P : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (hP : IsStarProjection P) (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) :
    ‖⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star U * P * U) ψ⟫_ℂ -
      ⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star V * P * V) ψ⟫_ℂ‖ ≤
        2 * ‖U - V‖ := by
  have hsub : ⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star U * P * U) ψ⟫_ℂ -
      ⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star V * P * V) ψ⟫_ℂ =
      ⟪ψ, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star U * P * U) -
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star V * P * V)) ψ⟫_ℂ := by
    rw [sub_apply, inner_sub_right]
  rw [hsub]
  have hmap : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star U * P * U) -
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star V * P * V) =
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
        ((star U * P * U) - (star V * P * V)) := by
    rw [← map_sub]
  rw [hmap]
  set T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      ((star U * P * U) - (star V * P * V)) with hT
  have e1 := norm_inner_le_norm (𝕜 := ℂ) ψ (T ψ)
  have e2 := ContinuousLinearMap.le_opNorm T ψ
  rw [hψ] at e1 e2
  have hTop : ‖T‖ = ‖(star U * P * U) - (star V * P * V)‖ := by
    rw [hT, Matrix.l2_opNorm_toEuclideanCLM]
  rw [hTop] at e2
  have hU1 : ‖U‖ ≤ 1 := norm_mem_unitaryGroup_le_one hU
  have hV1 : ‖V‖ ≤ 1 := norm_mem_unitaryGroup_le_one hV
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  have hdecomp : (star U * P * U) - (star V * P * V)
      = (star U - star V) * P * U + star V * P * (U - V) := by
    simp only [sub_mul, mul_sub]
    abel
  have hmat : ‖(star U * P * U) - (star V * P * V)‖ ≤ 2 * ‖U - V‖ := by
    rw [hdecomp]
    have g1 : ‖(star U - star V) * P * U‖ ≤ ‖U - V‖ := by
      have e1 : ‖(star U - star V) * P * U‖ ≤
          ‖star U - star V‖ * ‖P‖ * ‖U‖ := by
        calc ‖(star U - star V) * P * U‖
            ≤ ‖(star U - star V) * P‖ * ‖U‖ := norm_mul_le _ _
          _ ≤ ‖star U - star V‖ * ‖P‖ * ‖U‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      have e2 : ‖star U - star V‖ = ‖U - V‖ := by
        rw [← star_sub, norm_star_matrix]
      rw [e2] at e1
      calc ‖(star U - star V) * P * U‖ ≤ ‖U - V‖ * ‖P‖ * ‖U‖ := e1
        _ ≤ ‖U - V‖ * 1 * 1 := by gcongr
        _ = ‖U - V‖ := by rw [mul_one, mul_one]
    have g2 : ‖star V * P * (U - V)‖ ≤ ‖U - V‖ := by
      have e1 : ‖star V * P * (U - V)‖ ≤ ‖star V‖ * ‖P‖ * ‖U - V‖ := by
        calc ‖star V * P * (U - V)‖ ≤ ‖star V * P‖ * ‖U - V‖ := norm_mul_le _ _
          _ ≤ ‖star V‖ * ‖P‖ * ‖U - V‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      rw [norm_star_matrix] at e1
      calc ‖star V * P * (U - V)‖ ≤ ‖V‖ * ‖P‖ * ‖U - V‖ := e1
        _ ≤ 1 * 1 * ‖U - V‖ := by gcongr
        _ = ‖U - V‖ := by rw [one_mul, one_mul]
    calc ‖(star U - star V) * P * U + star V * P * (U - V)‖
        ≤ ‖(star U - star V) * P * U‖ + ‖star V * P * (U - V)‖ :=
          norm_add_le _ _
      _ ≤ ‖U - V‖ + ‖U - V‖ := add_le_add g1 g2
      _ = 2 * ‖U - V‖ := (two_mul _).symm
  calc ‖⟪ψ, T ψ⟫_ℂ‖ ≤ 1 * ‖T ψ‖ := e1
    _ ≤ 1 * (‖(star U * P * U) - (star V * P * V)‖ * 1) := by gcongr
    _ ≤ 1 * ((2 * ‖U - V‖) * 1) := by gcongr
    _ = 2 * ‖U - V‖ := by rw [mul_one, one_mul]

/-- The projection-form error for two unitary circuits is at most twice the
sum of the individual gate errors. -/
theorem norm_inner_circuit_conj_sub_le {n : Type*} [Fintype n] [DecidableEq n]
    {T : ℕ} (U V : Fin T → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup n ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup n ℂ)
    (ε : Fin T → ℝ) (hε : ∀ i, ‖U i - V i‖ ≤ ε i)
    {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) :
    ‖⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
        (star (circuitProd U) * P * (circuitProd U)) ψ⟫_ℂ -
      ⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
        (star (circuitProd V) * P * (circuitProd V)) ψ⟫_ℂ‖ ≤
        2 * ∑ i, ε i := by
  have hUprod : circuitProd U ∈ Matrix.unitaryGroup n ℂ := by
    show (List.ofFn U).reverse.prod ∈ Matrix.unitaryGroup n ℂ
    exact Submonoid.list_prod_mem _ fun x hx => by
      rw [List.mem_reverse] at hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hU i
  have hVprod : circuitProd V ∈ Matrix.unitaryGroup n ℂ := by
    show (List.ofFn V).reverse.prod ∈ Matrix.unitaryGroup n ℂ
    exact Submonoid.list_prod_mem _ fun x hx => by
      rw [List.mem_reverse] at hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hV i
  have h3 := norm_inner_conj_sub_le hUprod hVprod hP ψ hψ
  have h2 := norm_circuit_sub_le U V hU hV ε hε
  calc ‖⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
          (star (circuitProd U) * P * (circuitProd U)) ψ⟫_ℂ -
        ⟪ψ, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
          (star (circuitProd V) * P * (circuitProd V)) ψ⟫_ℂ‖
      ≤ 2 * ‖circuitProd U - circuitProd V‖ := h3
    _ ≤ 2 * ∑ i, ε i := by gcongr

end MathlibExt.Quantum.UnitaryErrorBudget
