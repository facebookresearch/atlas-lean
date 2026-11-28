/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Componentwise properties of short complexes

In an abelian category C, a short complex whose three objects are zero is a zero object of the
category of short complexes. A map is a monomorphism if all three component maps are
monomorphisms.

For a short complex in the abelian category of short complexes, exactness of its three
coefficient rows implies exactness of the whole short complex.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be abelian and S a short complex in C. If S₁,S₂,S₃ are zero objects, then S is a zero
object in the category of short complexes. -/
theorem isZero_of_components (S : ShortComplex C)
    (h₁ : IsZero S.X₁) (h₂ : IsZero S.X₂) (h₃ : IsZero S.X₃) : IsZero S := by
  apply (IsZero.iff_id_eq_zero S).mpr
  apply ShortComplex.hom_ext
  · exact h₁.eq_of_src _ _
  · exact h₂.eq_of_src _ _
  · exact h₃.eq_of_src _ _

/-- Let C be abelian and f : S → T a short-complex map. If f₁ : S₁ → T₁, f₂ : S₂ → T₂ and f₃ : S₃ →
T₃ are monomorphisms, then f is a monomorphism in the category of short complexes. -/
theorem mono_of_components {S T : ShortComplex C} (f : S ⟶ T)
    [Mono f.τ₁] [Mono f.τ₂] [Mono f.τ₃] : Mono f where
  right_cancellation {X} a b h := by
    apply ShortComplex.hom_ext
    · exact (cancel_mono f.τ₁).mp (congrArg ShortComplex.Hom.τ₁ h)
    · exact (cancel_mono f.τ₂).mp (congrArg ShortComplex.Hom.τ₂ h)
    · exact (cancel_mono f.τ₃).mp (congrArg ShortComplex.Hom.τ₃ h)

/-- Let C be abelian and S a short complex in the abelian category of short complexes over C. If the
rows obtained by taking the first, second and third coefficient objects are all exact in C, then
S is exact as a short complex of short complexes. -/
theorem exact_of_components (S : ShortComplex (ShortComplex C))
    (h₁ : (S.map (ShortComplex.π₁ : ShortComplex C ⥤ C)).Exact)
    (h₂ : (S.map (ShortComplex.π₂ : ShortComplex C ⥤ C)).Exact)
    (h₃ : (S.map (ShortComplex.π₃ : ShortComplex C ⥤ C)).Exact) : S.Exact := by
  have hz₁ : IsZero ((ShortComplex.π₁ : ShortComplex C ⥤ C).obj S.homology) :=
    IsZero.of_iso ((S.map _).exact_iff_isZero_homology.mp h₁)
      (S.mapHomologyIso (ShortComplex.π₁ : ShortComplex C ⥤ C)).symm
  have hz₂ : IsZero ((ShortComplex.π₂ : ShortComplex C ⥤ C).obj S.homology) :=
    IsZero.of_iso ((S.map _).exact_iff_isZero_homology.mp h₂)
      (S.mapHomologyIso (ShortComplex.π₂ : ShortComplex C ⥤ C)).symm
  have hz₃ : IsZero ((ShortComplex.π₃ : ShortComplex C ⥤ C).obj S.homology) :=
    IsZero.of_iso ((S.map _).exact_iff_isZero_homology.mp h₃)
      (S.mapHomologyIso (ShortComplex.π₃ : ShortComplex C ⥤ C)).symm
  exact S.exact_iff_isZero_homology.mpr (isZero_of_components S.homology hz₁ hz₂ hz₃)

end CategoryTheory.ShortComplex
