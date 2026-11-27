/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.Injective.HorseshoeComparison

/-!
# Endpoint choices in right-derived connecting maps

For a short exact sequence in an abelian category, endpoint injective
resolutions give compatible horseshoe data. Maps of short exact
sequences lift to maps between these data for any endpoint choices.
For an additive functor into an abelian category, the resulting
right-derived boundaries commute with the sequence maps and equal
the canonical connecting transformation for every endpoint choice.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'

namespace CategoryTheory.Functor.RightDerived
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C` be abelian, `S,T` short exact sequences and `α : S → T`.
Choose injective resolutions of the left and right endpoints of each.
The endpoint comparison lifts `α` to a morphism of the two compatible
injective horseshoes. -/
def HorseshoeData.endpointComparison
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)
    (J₁ : InjectiveResolution T.X₁) (J₃ : InjectiveResolution T.X₃) (α : S ⟶ T) :
    HorseshoeData.Hom (HorseshoeData.ofEndpoints S hS I₁ I₃)
      (HorseshoeData.ofEndpoints T hT J₁ J₃) α :=
  (HorseshoeData.nonempty_hom_ofEndpoints hS hT I₁ I₃ J₁ J₃ α
    (InjectiveResolution.descHom α.τ₁ I₁ J₁)
    (InjectiveResolution.descHom α.τ₃ I₃ J₃)).some.val

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For `α : S → T` between short exact sequences
and any endpoint injective resolutions, their boundaries satisfy
`δ_S,n ≫ R^(n+1)F(α₁) = R^nF(α₃) ≫ δ_T,n`. -/
theorem endpointDelta_naturality (F : C ⥤ D) [F.Additive]
    (n : ℕ) {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)
    (J₁ : InjectiveResolution T.X₁) (J₃ : InjectiveResolution T.X₃) (α : S ⟶ T) :
    RightDerivedDelta.RDdelta F n S hS I₁ I₃ ≫ (F.rightDerived (n + 1)).map α.τ₁ =
      (F.rightDerived n).map α.τ₃ ≫ RightDerivedDelta.RDdelta F n T hT J₁ J₃ :=
  (HorseshoeData.endpointComparison hS hT I₁ I₃ J₁ J₃ α).delta_naturality
    F n (n + 1) rfl

theorem endpointDelta_eq (F : C ⥤ D) [F.Additive]
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact)
    (I₁ J₁ : InjectiveResolution S.X₁) (I₃ J₃ : InjectiveResolution S.X₃) :
    RightDerivedDelta.RDdelta F n S hS I₁ I₃ = RightDerivedDelta.RDdelta F n S hS J₁ J₃ := by
  have h := endpointDelta_naturality F n hS hS I₁ I₃ J₁ J₃ (𝟙 S)
  change RightDerivedDelta.RDdelta F n S hS I₁ I₃ ≫ (F.rightDerived (n + 1)).map (𝟙 S.X₁) =
    (F.rightDerived n).map (𝟙 S.X₃) ≫ RightDerivedDelta.RDdelta F n S hS J₁ J₃ at h
  simpa only [Functor.map_id, Category.comp_id, Category.id_comp] using h

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The canonical connecting transformation on `S` equals the
horseshoe boundary computed from `I₁,I₃` in every degree `n`. -/
theorem rightDerivedConnecting_eq_endpoints (F : C ⥤ D) [F.Additive]
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃) :
    (F.rightDerivedConnecting n).app ⟨S, hS⟩ = RightDerivedDelta.RDdelta F n S hS I₁ I₃ :=
  endpointDelta_eq F n S hS (injectiveResolution S.X₁) I₁
    (injectiveResolution S.X₃) I₃

end CategoryTheory.Functor.RightDerived
