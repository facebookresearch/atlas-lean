/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.LongExact

/-!
# Independence of the projective horseshoe boundary

For an additive functor between abelian categories with projective
resolutions in the source, every compatible projective horseshoe with
endpoint coordinates computes the canonical left-derived connecting
map, regardless of its endpoint and middle-resolution choices.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution.HorseshoeData
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact,
`P₁,P₃` any endpoint projective resolutions, and `H` horseshoe data
with endpoint coordinates. Its boundary `L_(n+1)F(X₃) → L_nF(X₁)`
equals the canonical left-derived boundary of `S`. -/
theorem delta_eq_native {S : ShortComplex C} {hS : S.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    (H : HorseshoeData hS P₁ P₃) (sH : H.Spec)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    H.delta sH F (n + 1) n rfl = LeftDerivedDelta.LDdelta F n S hS := by
  let H' := LeftDerivedDelta.LDhorseshoe S hS
  let sH' := ProjectiveResolution.horseshoe_spec hS (projectiveResolution S.X₁)
    (projectiveResolution S.X₃)
  let u := ProjectiveResolution.liftHom (𝟙 S.X₁) P₁ (projectiveResolution S.X₁)
  let w := ProjectiveResolution.liftHom (𝟙 S.X₃) P₃ (projectiveResolution S.X₃)
  obtain ⟨a⟩ := ProjectiveResolution.HorseshoeData.nonempty_hom
    (H := H) (H' := H') (sH := sH) (sH' := sH') (φ := 𝟙 S) (u := u) (w := w)
  have h := a.delta_naturality sH sH' F (n + 1) n rfl
  change H.delta sH F (n + 1) n rfl ≫ (F.leftDerived n).map (𝟙 S.X₁) =
    (F.leftDerived (n + 1)).map (𝟙 S.X₃) ≫ LeftDerivedDelta.LDdelta F n S hS at h
  simpa only [Functor.map_id, Category.comp_id, Category.id_comp] using h

end CategoryTheory.ProjectiveResolution.HorseshoeData
