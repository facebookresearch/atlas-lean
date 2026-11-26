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
# Universal homological delta-functor of left derivation

Let `C,D` be abelian, with projective resolutions in `C`, and
`F : C → D` additive. The degree functors `L_nF` and horseshoe
boundaries `L_(n+1)F(X₃) → L_nF(X₁)` form a homological delta-functor.
Every positive degree is coeffaceable by a projective-resolution
augmentation, so a transformation into degree zero extends uniquely
into this delta-functor. Identifying `L₀F` with `F` additionally
requires preservation of finite colimits.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. The horseshoe boundaries give a natural transformation
`L_(n+1)F(X₃) → L_nF(X₁)` on the category of short exact
sequences `X₁ → X₂ → X₃`. -/
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

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. The degree functors `L_nF` and canonical horseshoe connecting
maps form a homological delta-functor from `C` to `D`. -/
def leftDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] : HomologicalDeltaFunctor C D where
  T n := F.leftDerived n
  additive _ := inferInstance
  connecting := F.leftDerivedConnecting
  exactLeft n S := LeftDerivedDelta.LDexact_A F n S.obj S.property
  exactMiddle n S := LeftDerivedDelta.LDexact_B F n S.obj S.property
  exactRight n S := LeftDerivedDelta.LDexact_C F n S.obj S.property
  epiZero S := LeftDerivedDelta.LDepi_zero F S.obj S.property

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. The degree-`n` functor of its homological delta-functor is
exactly `L_nF`. -/
@[simp]
theorem leftDerivedDeltaFunctor_T (F : C ⥤ D) [F.Additive] (n : ℕ) :
    F.leftDerivedDeltaFunctor.T n = F.leftDerived n := rfl

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. On a short exact sequence `S`, the connecting map of its
derived delta-functor is the canonical horseshoe boundary
`L_(n+1)F(S.X₃) → L_nF(S.X₁)`. -/
theorem leftDerivedDeltaFunctor_connecting_app (F : C ⥤ D) [F.Additive]
    (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (F.leftDerivedDeltaFunctor.connecting n).app S =
      LeftDerivedDelta.LDdelta F n S.obj S.property := rfl

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. For every `n`, `L_(n+1)F` is coeffaceable: the epi
augmentation `P(X)₀ → X` from a projective resolution kills its
induced degree-`n+1` map for each object `X`. -/
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

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. Its homological delta-functor is universal in the receiving
direction: for any homological delta-functor `T`, every natural
transformation `T₀ → L₀F` extends uniquely to a morphism `T → L_*F`. -/
theorem isUniversal_leftDerivedDeltaFunctor (F : C ⥤ D) [F.Additive] :
    HomologicalDeltaFunctor.IsUniversal C D F.leftDerivedDeltaFunctor := by
  apply HomologicalDeltaFunctor.isUniversal_of_coeffaceable
  intro n
  change (F.leftDerived (n + 1)).IsCoeffaceable
  exact F.isCoeffaceable_leftDerived_succ n

end CategoryTheory.Functor

end
