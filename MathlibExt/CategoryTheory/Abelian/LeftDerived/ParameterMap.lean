/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.LongExact
public import Mathlib.CategoryTheory.CommSq

/-!
# Naturality of left-derived boundaries in the additive functor

The maps in both derived degrees are the `NatTrans.leftDerived` components.
`ShortComplex.mapNatTrans` maps the fixed split horseshoe, and `CommSq.horiz_comp` combines its
boundary square with the existing resolution-comparison squares. No additional
mapped-natural-transformation or endpoint comparison wrapper is introduced.

Neither additive functor is required to preserve arbitrary exact sequences.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace ProjectiveResolution.HorseshoeData

variable {S : ShortComplex C} {hS : S.ShortExact}
variable {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
variable (H : ProjectiveResolution.HorseshoeData hS P₁ P₃)

/--
The supplied horseshoe boundary commutes with the left-derived components of a natural
transformation between additive functors.
-/
theorem delta_naturality_functor (sH : H.Spec)
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    H.delta sH F i j hij ≫ (NatTrans.leftDerived α j).app S.X₁ =
      (NatTrans.leftDerived α i).app S.X₃ ≫ H.delta sH G i j hij := by
  let φ : H.mapped F ⟶ H.mapped G :=
    (ShortComplex.mk H.i H.p H.zero).mapNatTrans
      (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ))
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ
    (H.mapped_shortExact sH F) (H.mapped_shortExact sH G) i j hij
  change (H.mapped_shortExact sH F).δ i j hij ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P₁.complex) j =
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P₃.complex) i ≫
      (H.mapped_shortExact sH G).δ i j hij at hδ
  let a := (P₃.isoLeftDerivedObj F i).hom
  let a' := (P₃.isoLeftDerivedObj G i).hom
  let t := (P₁.isoLeftDerivedObj F j).inv
  let t' := (P₁.isoLeftDerivedObj G j).inv
  let d := (H.mapped_shortExact sH F).δ i j hij
  let d' := (H.mapped_shortExact sH G).δ i j hij
  let f := (NatTrans.leftDerived α i).app S.X₃
  let g := (NatTrans.leftDerived α j).app S.X₁
  let hm₁ := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P₁.complex) j
  let hm₃ := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P₃.complex) i
  have hs : CommSq a f hm₃ a' :=
    ⟨(P₃.isoLeftDerivedObj_hom_naturality_functor α i).symm⟩
  have hd : CommSq d hm₃ hm₁ d' := ⟨hδ⟩
  have ht : CommSq t hm₁ g t' :=
    ⟨(P₁.isoLeftDerivedObj_inv_naturality_functor α j).symm⟩
  have hc := hs.horiz_comp (hd.horiz_comp ht)
  change (a ≫ d ≫ t) ≫ g = f ≫ (a' ≫ d' ≫ t')
  exact hc.w

end ProjectiveResolution.HorseshoeData

namespace LeftDerivedDelta

/-- The canonical `LDdelta` commutes with the literal left-derived parameter maps. -/
theorem LDdelta_natural_functor {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (NatTrans.leftDerived α (n + 1)).app S.X₃ ≫ LDdelta G n S hS =
      LDdelta F n S hS ≫ (NatTrans.leftDerived α n).app S.X₁ := by
  exact ((LDhorseshoe S hS).delta_naturality_functor
    (ProjectiveResolution.horseshoe_spec hS _ _) α (n + 1) n
    (ComplexShape.down_mk _ _ rfl)).symm

end LeftDerivedDelta
end CategoryTheory

end
