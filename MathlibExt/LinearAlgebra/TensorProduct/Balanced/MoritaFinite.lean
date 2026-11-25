/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaNormalization
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Finiteness
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Finite dual frames from invertible bimodule contractions

The contractions u and v determine the normalization u′. Finite expressions
for u′⁻¹(1) and v⁻¹(1) give four dual-frame expansions. These projective
frames give finite generation and projectivity in all four variances,
without asserting freeness.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe r s p q a

namespace TensorProduct.Balanced.Morita

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P : Type p) (Q : Type q) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (u : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced ℤ S P Q), u (r • b) = r * u b)

include u in
/-- Select a native finite pure expression for the actual inverse image of 1. -/
def unitSupport : Finset (P × Q) :=
  Classical.choose (exists_finset ℤ S P Q (u.symm 1))

set_option linter.unusedSectionVars false in
/-- The selected ordered sum is the actual inverse image of the scalar unit. -/
@[nolint unusedArguments] -- omitting them cascades via `unitSupport_sum` into the frame lemmas
theorem unitSupport_eq :
    u.symm 1 = ∑ a ∈ unitSupport R S P Q u, mk ℤ S P Q a.1 a.2 :=
  Classical.choose_spec (exists_finset ℤ S P Q (u.symm 1))

/-- The selected actual pure expression maps to the scalar unit. -/
theorem unitSupport_sum :
    u (∑ a ∈ unitSupport R S P Q u, mk ℤ S P Q a.1 a.2) = 1 := by
  rw [← unitSupport_eq R S P Q u]
  exact u.apply_symm_apply 1

/-- The same unit equation indexed by the actual finite support type. -/
theorem unitSupport_sum_fintype :
    (∑ a : unitSupport R S P Q u, u (mk ℤ S P Q a.val.1 a.val.2)) = 1 := by
  let := rightModule ℤ S R P Q
  calc
    _ = ∑ a ∈ unitSupport R S P Q u, u (mk ℤ S P Q a.1 a.2) :=
      Finset.sum_coe_sort (unitSupport R S P Q u)
        (fun a : P × Q => u (mk ℤ S P Q a.1 a.2))
    _ = u (∑ a ∈ unitSupport R S P Q u, mk ℤ S P Q a.1 a.2) := by
      rw [map_sum]
    _ = 1 := unitSupport_sum R S P Q u

include u hu in
/-- The first-factor coefficient is linear for the original left R action. -/
def leftCoefficient (q : Q) : P →ₗ[R] R := by
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  exact
    { toFun := fun p => u (mk ℤ S P Q p q)
      map_add' := by
        intro p p'
        rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := by
        intro r p
        rw [← leftModule_smul_mk ℤ S R P Q]
        exact hu r (mk ℤ S P Q p q) }

@[simp]
theorem leftCoefficient_apply (q : Q) (p : P) :
    leftCoefficient R S P Q u hu q p = u (mk ℤ S P Q p q) := rfl

include u in
/-- The second-factor coefficient is linear over Rop, with its actual reversed order. -/
def rightCoefficient (p : P) : Q →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := by
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  exact
    { toFun := fun q => op (u (mk ℤ S P Q p q))
      map_add' := by
        intro q q'
        rw [map_add, map_add, op_add]
      map_smul' := by
        intro t q
        have ht : u (mk ℤ S P Q p (t • q)) = u (mk ℤ S P Q p q) * t.unop := by
          rw [← rightModule_smul_mk ℤ S R P Q]
          exact u.map_smul t (mk ℤ S P Q p q)
        change op (u (mk ℤ S P Q p (t • q))) = t * op (u (mk ℤ S P Q p q))
        rw [ht, op_mul, op_unop] }

omit [Module R P] [SMulCommClass R Sᵐᵒᵖ P] in
@[simp]
theorem rightCoefficient_apply (p : P) (q : Q) :
    rightCoefficient R S P Q u p q = op (u (mk ℤ S P Q p q)) := rfl

variable
  (w : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced ℤ R Q P), w (s • b) = s * w b)

include u hu w hw in
/-- The selected v-unit expression gives a finite left R dual frame on the original P. -/
theorem p_left_frame (p : P) :
    ∑ i : unitSupport S R Q P w,
      leftCoefficient R S P Q (normalizedContraction R S P Q u w hw)
        (normalizedContraction_left R S P Q u hu w hw) i.1.1 p • i.1.2 = p := by
  classical
  let f : Q × P → P := fun i =>
    leftCoefficient R S P Q (normalizedContraction R S P Q u w hw)
      (normalizedContraction_left R S P Q u hu w hw) i.1 p • i.2
  change (∑ i : unitSupport S R Q P w, f (i : Q × P)) = p
  refine (Finset.sum_coe_sort (unitSupport S R Q P w) f).trans ?_
  simp only [f, leftCoefficient_apply]
  calc
    (∑ i ∈ unitSupport S R Q P w,
        normalizedContraction R S P Q u w hw (mk ℤ S P Q p i.1) • i.2) =
        ∑ i ∈ unitSupport S R Q P w, op (w (mk ℤ R Q P i.1 i.2)) • p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (normalized_p R S P Q u hu w hw p i.1 i.2).symm
    _ = op (w (∑ i ∈ unitSupport S R Q P w, mk ℤ R Q P i.1 i.2)) • p := by
      rw [map_sum, Finset.op_sum, Finset.sum_smul]
    _ = p := by rw [unitSupport_sum S R Q P w, op_one, one_smul]

include u hu w hw in
/-- The selected u′-unit expression gives a finite right S dual frame on the original P. -/
theorem p_right_frame (p : P) :
    ∑ i : unitSupport R S P Q (normalizedContraction R S P Q u w hw),
      rightCoefficient S R Q P w i.1.2 p • i.1.1 = p := by
  classical
  let f : P × Q → P := fun i => rightCoefficient S R Q P w i.2 p • i.1
  change (∑ i : unitSupport R S P Q (normalizedContraction R S P Q u w hw),
    f (i : P × Q)) = p
  refine (Finset.sum_coe_sort
    (unitSupport R S P Q (normalizedContraction R S P Q u w hw)) f).trans ?_
  simp only [f, rightCoefficient_apply]
  calc
    (∑ i ∈ unitSupport R S P Q (normalizedContraction R S P Q u w hw),
        op (w (mk ℤ R Q P i.2 p)) • i.1) =
        ∑ i ∈ unitSupport R S P Q (normalizedContraction R S P Q u w hw),
          normalizedContraction R S P Q u w hw (mk ℤ S P Q i.1 i.2) • p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact normalized_p R S P Q u hu w hw i.1 i.2 p
    _ = normalizedContraction R S P Q u w hw
        (∑ i ∈ unitSupport R S P Q (normalizedContraction R S P Q u w hw),
          mk ℤ S P Q i.1 i.2) • p := by
      rw [map_sum, Finset.sum_smul]
    _ = p := by
      rw [unitSupport_sum R S P Q (normalizedContraction R S P Q u w hw), one_smul]

include u hu w hw in
/-- The same u′-unit expression gives a finite left S dual frame on the original Q. -/
theorem q_left_frame (q : Q) :
    ∑ i : unitSupport R S P Q (normalizedContraction R S P Q u w hw),
      leftCoefficient S R Q P w hw i.1.1 q • i.1.2 = q := by
  classical
  let f : P × Q → Q := fun i => leftCoefficient S R Q P w hw i.1 q • i.2
  change (∑ i : unitSupport R S P Q (normalizedContraction R S P Q u w hw),
    f (i : P × Q)) = q
  refine (Finset.sum_coe_sort
    (unitSupport R S P Q (normalizedContraction R S P Q u w hw)) f).trans ?_
  simp only [f, leftCoefficient_apply]
  calc
    (∑ i ∈ unitSupport R S P Q (normalizedContraction R S P Q u w hw),
        w (mk ℤ R Q P q i.1) • i.2) =
        ∑ i ∈ unitSupport R S P Q (normalizedContraction R S P Q u w hw),
          op (normalizedContraction R S P Q u w hw (mk ℤ S P Q i.1 i.2)) • q := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (normalized_q R S P Q u hu w hw i.1 q i.2).symm
    _ = op (normalizedContraction R S P Q u w hw
        (∑ i ∈ unitSupport R S P Q (normalizedContraction R S P Q u w hw),
          mk ℤ S P Q i.1 i.2)) • q := by
      rw [map_sum, Finset.op_sum, Finset.sum_smul]
    _ = q := by
      rw [unitSupport_sum R S P Q (normalizedContraction R S P Q u w hw), op_one, one_smul]

include u hu w hw in
/-- The same v-unit expression gives a finite right R dual frame on the original Q. -/
theorem q_right_frame (q : Q) :
    ∑ i : unitSupport S R Q P w,
      rightCoefficient R S P Q (normalizedContraction R S P Q u w hw) i.1.2 q • i.1.1 = q := by
  classical
  let f : Q × P → Q := fun i =>
    rightCoefficient R S P Q (normalizedContraction R S P Q u w hw) i.2 q • i.1
  change (∑ i : unitSupport S R Q P w, f (i : Q × P)) = q
  refine (Finset.sum_coe_sort (unitSupport S R Q P w) f).trans ?_
  simp only [f, rightCoefficient_apply]
  calc
    (∑ i ∈ unitSupport S R Q P w,
        op (normalizedContraction R S P Q u w hw (mk ℤ S P Q i.2 q)) • i.1) =
        ∑ i ∈ unitSupport S R Q P w, w (mk ℤ R Q P i.1 i.2) • q := by
      apply Finset.sum_congr rfl
      intro i hi
      exact normalized_q R S P Q u hu w hw i.2 i.1 q
    _ = w (∑ i ∈ unitSupport S R Q P w, mk ℤ R Q P i.1 i.2) • q := by
      rw [map_sum, Finset.sum_smul]
    _ = q := by rw [unitSupport_sum S R Q P w, one_smul]

include u hu w hw in
/-- Native finite-free reconstruction splits the actual P left-coordinate map. -/
theorem p_left_split :
    (Fintype.linearCombination R (fun i : unitSupport S R Q P w => i.1.2)).comp
      (LinearMap.pi (fun i : unitSupport S R Q P w =>
        leftCoefficient R S P Q (normalizedContraction R S P Q u w hw)
          (normalizedContraction_left R S P Q u hu w hw) i.1.1)) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  exact p_left_frame R S P Q u hu w hw p

include u hu w hw in
/-- Native finite-free reconstruction splits the actual P right-coordinate map. -/
theorem p_right_split :
    (Fintype.linearCombination Sᵐᵒᵖ
      (fun i : unitSupport R S P Q (normalizedContraction R S P Q u w hw) => i.1.1)).comp
      (LinearMap.pi
        (fun i : unitSupport R S P Q (normalizedContraction R S P Q u w hw) =>
          rightCoefficient S R Q P w i.1.2)) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  exact p_right_frame R S P Q u hu w hw p

include u hu w hw in
/-- The same selected coordinates split the native finite-free reconstruction onto Q on the left. -/
theorem q_left_split :
    (Fintype.linearCombination S
      (fun i : unitSupport R S P Q (normalizedContraction R S P Q u w hw) => i.1.2)).comp
      (LinearMap.pi
        (fun i : unitSupport R S P Q (normalizedContraction R S P Q u w hw) =>
          leftCoefficient S R Q P w hw i.1.1)) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  exact q_left_frame R S P Q u hu w hw q

include u hu w hw in
/-- The v-unit coordinates split finite-free reconstruction onto Q on the right. -/
theorem q_right_split :
    (Fintype.linearCombination Rᵐᵒᵖ (fun i : unitSupport S R Q P w => i.1.1)).comp
      (LinearMap.pi (fun i : unitSupport S R Q P w =>
        rightCoefficient R S P Q (normalizedContraction R S P Q u w hw) i.1.2)) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  exact q_right_frame R S P Q u hu w hw q

private theorem finite_projective_of_split {T : Type r} [Semiring T]
    {M : Type p} [AddCommMonoid M] [Module T M] {ι : Type a} [Finite ι]
    (i : M →ₗ[T] (ι → T)) (s : (ι → T) →ₗ[T] M)
    (h : s.comp i = LinearMap.id) : Module.Finite T M ∧ Module.Projective T M := by
  let : Module.Projective T (ι → T) := Module.Projective.of_basis (Pi.basisFun T ι)
  have hs : Function.Surjective s := by
    intro m
    refine ⟨i m, ?_⟩
    exact LinearMap.congr_fun h m
  exact ⟨Module.Finite.of_surjective s hs, Module.Projective.of_split i s h⟩

include u hu w hw in
/-- P is finite and projective for its original left R module, without a supplied frame. -/
theorem p_left_finite_projective : Module.Finite R P ∧ Module.Projective R P := by
  exact finite_projective_of_split _ _ (p_left_split R S P Q u hu w hw)

include u hu w hw in
/-- P is finite and projective for its original right S module. -/
theorem p_right_finite_projective : Module.Finite Sᵐᵒᵖ P ∧ Module.Projective Sᵐᵒᵖ P := by
  exact finite_projective_of_split _ _ (p_right_split R S P Q u hu w hw)

include u hu w hw in
/-- Q is finite and projective for its original left S module. -/
theorem q_left_finite_projective : Module.Finite S Q ∧ Module.Projective S Q := by
  exact finite_projective_of_split _ _ (q_left_split R S P Q u hu w hw)

include u hu w hw in
/-- Q is finite and projective for its original right R module. -/
theorem q_right_finite_projective : Module.Finite Rᵐᵒᵖ Q ∧ Module.Projective Rᵐᵒᵖ Q := by
  exact finite_projective_of_split _ _ (q_right_split R S P Q u hu w hw)

end TensorProduct.Balanced.Morita
