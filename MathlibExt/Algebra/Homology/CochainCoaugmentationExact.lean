/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
## Source exactness of a coaugmentation that is a quasi-isomorphism
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A degree-zero quasi-isomorphic coaugmentation gives its exact first row and mono. -/
theorem coaugmentation_exact_and_mono {X : C} {I : CochainComplex C ℕ}
    (ι : (single₀ C).obj X ⟶ I) [QuasiIsoAt ι 0] :
    (ShortComplex.mk (ι.f 0) (I.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact ∧
      Mono (ι.f 0) := by
  have h := (quasiIsoAt₀_iff ι).mp inferInstance
  exact (ShortComplex.quasiIso_iff_of_zeros _
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 0)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 1)
    (I.shape 0 0 (by simp [ComplexShape.up_Rel]))).mp h

/-- Positive rows of an original quasi-isomorphic coaugmentation are exact. -/
theorem coaugmentation_exact_succ {X : C} {I : CochainComplex C ℕ}
    (ι : (single₀ C).obj X ⟶ I) [QuasiIso ι] (n : ℕ) :
    (ShortComplex.mk (I.d n (n + 1)) (I.d (n + 1) (n + 2))
      (I.d_comp_d n (n + 1) (n + 2))).Exact := by
  have hI : I.ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt ι (n + 1)).mp
      (exactAt_succ_single_obj X n)
  exact (HomologicalComplex.exactAt_iff' I n (n + 1) (n + 2)
    (by simp) (by simp)).mp hI

/--
A cochain map's degree-zero augmentation equation determines the whole coaugmentation equation
from the original single object.
-/
theorem coaugmentation_comp_eq_of_f_zero {X : C} {I J : CochainComplex C ℕ}
    (ι : (single₀ C).obj X ⟶ I) (κ : (single₀ C).obj X ⟶ J) (a : I ⟶ J)
    (h : ι.f 0 ≫ a.f 0 = κ.f 0) : ι ≫ a = κ := by
  apply (fromSingle₀Equiv J X).injective
  apply Subtype.ext
  exact h

end CochainComplex
