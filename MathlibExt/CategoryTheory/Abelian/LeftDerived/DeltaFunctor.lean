/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.LongExact
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Effaceable

/-!
# The universal homological δ-functor of the left-derived family

The degree functors are exactly `F.leftDerived n`. Connecting maps on the category of short exact
sequences are the canonical mapped-horseshoe maps. Positive coeffaceability uses the degree-zero
projective object and epi augmentation of the chosen resolution. No global reverse instance for
enough projectives is introduced.

This construction concerns `L₀F` itself. Identifying `L₀F` with `F` additionally requires
finite-colimit preservation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The horseshoe boundary is a natural transformation on short exact sequences. -/
def leftDerivedConnecting (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (ShortComplex.isShortExact C).ι ⋙ ShortComplex.π₃ ⋙ F.leftDerived (n + 1) ⟶
      (ShortComplex.isShortExact C).ι ⋙ ShortComplex.π₁ ⋙ F.leftDerived n where
  app S := LeftDerivedDelta.LDdelta F n S.obj S.property
  naturality {S S'} φ := by
    change (F.leftDerived (n + 1)).map φ.hom.τ₃ ≫
        LeftDerivedDelta.LDdelta F n S'.obj S'.property =
      LeftDerivedDelta.LDdelta F n S.obj S.property ≫ (F.leftDerived n).map φ.hom.τ₁
    exact LeftDerivedDelta.LDdelta_natural F n S'.obj S.obj φ.hom
      S'.property S.property

/-- The homological δ-functor with the left-derived degree functors and boundaries. -/
def leftDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] : HomologicalDeltaFunctor C D where
  T n := F.leftDerived n
  additive _ := inferInstance
  connecting := F.leftDerivedConnecting
  exactLeft n S := LeftDerivedDelta.LDexact_A F n S.obj S.property
  exactMiddle n S := LeftDerivedDelta.LDexact_B F n S.obj S.property
  exactRight n S := LeftDerivedDelta.LDexact_C F n S.obj S.property
  epiZero S := LeftDerivedDelta.LDepi_zero F S.obj S.property

/-- Every degree of the bundle is the derived functor. -/
@[simp]
theorem leftDerivedDeltaFunctor_T (F : C ⥤ D) [F.Additive] (n : ℕ) :
    F.leftDerivedDeltaFunctor.T n = F.leftDerived n := rfl

/-- The bundle's boundary is the canonical horseshoe connecting map. -/
theorem leftDerivedDeltaFunctor_connecting_app (F : C ⥤ D) [F.Additive]
    (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (F.leftDerivedDeltaFunctor.connecting n).app S =
      LeftDerivedDelta.LDdelta F n S.obj S.property := rfl

/-- Every positive left-derived functor is coeffaceable using a resolution augmentation. -/
theorem isCoeffaceable_leftDerived_succ (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived (n + 1)).IsCoeffaceable := by
  intro X
  let P : C := (projectiveResolution X).complex.X 0
  let p : P ⟶ X := (projectiveResolution X).π.f 0
  have : Projective P := by
    dsimp [P]
    infer_instance
  have hp : Epi p := by
    dsimp [p]
    exact epi_of_isColimit_cofork (projectiveResolution X).isColimitCokernelCofork
  have hP : IsZero ((F.leftDerived (n + 1)).obj P) :=
    F.isZero_leftDerived_obj_projective_succ n P
  exact ⟨P, p, hp, hP.eq_of_src _ _⟩

/-- The derived bundle is universal in the homological, receiving direction. -/
theorem isUniversal_leftDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] :
    HomologicalDeltaFunctor.IsUniversal C D F.leftDerivedDeltaFunctor := by
  apply HomologicalDeltaFunctor.isUniversal_of_coeffaceable
  intro n
  change (F.leftDerived (n + 1)).IsCoeffaceable
  exact F.isCoeffaceable_leftDerived_succ n

end CategoryTheory.Functor

end
