/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Exactness at an augmentation and its first kernel-tail row

For a map from a nonnegative chain complex to a complex concentrated in degree
zero, a quasi-isomorphism in degree zero gives exactness at the augmentation and
an epimorphic augmentation. Its native kernel lift is then epimorphic. A
quasi-isomorphism in degree one separately gives the first exact kernel-tail row.

These results use the actual differential and the actual degree-zero component
of the given chain map. They require no projectivity or choice of resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Q : ChainComplex C ℕ} {M : C}

/-- A quasi-isomorphism in degree zero is precisely exactness at the
augmentation together with the epimorphism property of its degree-zero map. -/
lemma quasiIsoAt_zero_iff_exact_and_epi_augmentation
    (π : Q ⟶ (single₀ C).obj M) :
    QuasiIsoAt π 0 ↔
      (ShortComplex.mk (Q.d 1 0) (π.f 0)
        (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])).Exact ∧
      Epi (π.f 0) := by
  rw [quasiIsoAt₀_iff]
  exact ShortComplex.quasiIso_iff_of_zeros' _
    (Q.shape 0 0 (by simp [ComplexShape.down_Rel]))
    (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 M 1 0)
    (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 M 0 0)

/-- The incoming differential and the augmentation form an exact short
complex if the augmentation is a quasi-isomorphism in degree zero. -/
lemma exact_augmentation (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0] :
    (ShortComplex.mk (Q.d 1 0) (π.f 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])).Exact :=
  ((quasiIsoAt_zero_iff_exact_and_epi_augmentation π).mp inferInstance).1

/-- The degree-zero map of an augmentation that is a quasi-isomorphism in
degree zero is epimorphic. This lemma does not add a global instance. -/
lemma epi_augmentation_f_zero (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0] :
    Epi (π.f 0) :=
  ((quasiIsoAt_zero_iff_exact_and_epi_augmentation π).mp inferInstance).2

/-- The incoming differential maps epimorphically onto the native kernel of
an augmentation that is a quasi-isomorphism in degree zero. -/
lemma epi_kernelLift_augmentation (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0] :
    Epi (kernel.lift (π.f 0) (Q.d 1 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])) :=
  (exact_augmentation π).epi_kernelLift

/-- Factoring the first differential through the augmentation kernel leaves
the row in degree one exact. Only a quasi-isomorphism in degree one is needed. -/
lemma exact_kernelLift_augmentation (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 1] :
    (ShortComplex.mk (Q.d 2 1)
      (kernel.lift (π.f 0) (Q.d 1 0)
        (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]))
      (by
        rw [← cancel_mono (kernel.ι (π.f 0)), Category.assoc, kernel.lift_ι,
          Q.d_comp_d, zero_comp])).Exact := by
  have hQ : Q.ExactAt 1 :=
    (exactAt_iff_of_quasiIsoAt π 1).mpr
      (exactAt_succ_single_obj M 0)
  have h : (Q.sc' 2 1 0).Exact :=
    (HomologicalComplex.exactAt_iff' Q 2 1 0 (by simp) (by simp)).mp hQ
  let S : ShortComplex C := ShortComplex.mk (Q.d 2 1)
    (kernel.lift (π.f 0) (Q.d 1 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])) (by
      rw [← cancel_mono (kernel.ι (π.f 0)), Category.assoc, kernel.lift_ι,
        Q.d_comp_d, zero_comp])
  let φ : S ⟶ Q.sc' 2 1 0 :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (π.f 0)
      comm₁₂ := by simp only [S, HomologicalComplex.sc',
        HomologicalComplex.shortComplexFunctor', Category.id_comp, Category.comp_id]
      comm₂₃ := by
        dsimp [S, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
        rw [Category.id_comp]
        exact (kernel.lift_ι _ _ _).symm }
  change S.Exact
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr h

end ChainComplex
