/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeData
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import Mathlib.CategoryTheory.CommSq

/- ShortComplex.mapNatTrans gives the mapped diagram square; CommSq.horiz_comp pastes its boundary square with resolution-comparison squares. -/

/-!
# Coefficient naturality of a horseshoe connecting map

Let `C,D` be abelian, with injective resolutions in `C`, and let
`F,G : C → D` be additive. For compatible injective horseshoe data
over a short exact sequence and any transformation `α : F → G`,
the connecting maps in adjacent degrees commute with `R^nα`.
The result applies to every compatible middle-resolution and splitting
choice.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace Functor.RightDerived

variable {S : ShortComplex C} {hS : S.ShortExact}

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`H` compatible injective horseshoe data for short exact
`S : X₁ → X₂ → X₃`. For additive `F,G : C → D`, `α : F → G`,
and `n₁=n₀+1`, the boundary square is
`δ_H,F ≫ R^n₁α_(X₁) = R^n₀α_(X₃) ≫ δ_H,G`. -/
theorem HorseshoeData.delta_naturality_functor (H : HorseshoeData S hS)
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    H.delta F n₀ n₁ h ≫ (NatTrans.rightDerived α n₁).app S.X₁ =
      (NatTrans.rightDerived α n₀).app S.X₃ ≫ H.delta G n₀ n₁ h := by
  let φ : H.mapped F ⟶ H.mapped G :=
    H.diagram.mapNatTrans (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ))
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ
    (H.mapped_shortExact F) (H.mapped_shortExact G) n₀ n₁ h
  change (H.mapped_shortExact F).δ n₀ n₁ h ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app H.res₁.cocomplex)
          n₁ =
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app H.res₃.cocomplex)
          n₀ ≫
      (H.mapped_shortExact G).δ n₀ n₁ h at hδ
  let a := (H.res₃.isoRightDerivedObj F n₀).hom
  let a' := (H.res₃.isoRightDerivedObj G n₀).hom
  let t := (H.res₁.isoRightDerivedObj F n₁).inv
  let t' := (H.res₁.isoRightDerivedObj G n₁).inv
  let d := (H.mapped_shortExact F).δ n₀ n₁ h
  let d' := (H.mapped_shortExact G).δ n₀ n₁ h
  let f := (NatTrans.rightDerived α n₀).app S.X₃
  let g := (NatTrans.rightDerived α n₁).app S.X₁
  let hm₁ := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app H.res₁.cocomplex) n₁
  let hm₃ := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app H.res₃.cocomplex) n₀
  have hs : CommSq a f hm₃ a' :=
    ⟨(H.res₃.isoRightDerivedObj_hom_naturality_functor α n₀).symm⟩
  have hd : CommSq d hm₃ hm₁ d' := ⟨hδ⟩
  have ht : CommSq t hm₁ g t' :=
    ⟨(H.res₁.isoRightDerivedObj_inv_naturality_functor α n₁).symm⟩
  have hc := hs.horiz_comp (hd.horiz_comp ht)
  change (a ≫ d ≫ t) ≫ g = f ≫ (a' ≫ d' ≫ t')
  exact hc.w

end Functor.RightDerived
end CategoryTheory

end
