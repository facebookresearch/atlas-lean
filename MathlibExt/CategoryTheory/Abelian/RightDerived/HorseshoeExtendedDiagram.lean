/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import MathlibExt.Algebra.Homology.HomologicalComplex.ConeBoundary
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeData

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {S : ShortComplex C} {hS : S.ShortExact}

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. The left cochain lift, together with its coaugmentation
square, is a map of injective resolutions of `S.f : X₁ → X₂`. -/
def HorseshoeData.leftResolutionHom (H : HorseshoeData S hS) :
    InjectiveResolution.Hom H.res₁ H.res₂ S.f :=
  InjectiveResolution.Hom.mk H.φf
    (H.lift_f.trans (congrArg (· ≫ H.res₂.ι.f 0)
      (CochainComplex.single₀_map_f_zero S.f).symm))

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. The right cochain lift, together with its coaugmentation
square, is a map of injective resolutions of `S.g : X₂ → X₃`. -/
def HorseshoeData.rightResolutionHom (H : HorseshoeData S hS) :
    InjectiveResolution.Hom H.res₂ H.res₃ S.g :=
  InjectiveResolution.Hom.mk H.φg
    (H.lift_g.trans (congrArg (· ≫ H.res₃.ι.f 0)
      (CochainComplex.single₀_map_f_zero S.g).symm))

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Extending all three nonnegative cochain resolutions and their
maps by zero in negative degrees gives a short complex of integer
cochain complexes. -/
def HorseshoeData.extendedDiagram (H : HorseshoeData S hS) :
    ShortComplex (CochainComplex C ℤ) :=
  H.diagram.map (ComplexShape.embeddingUpNat.extendFunctor C)

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. In every integer degree `q`, the extended resolution row is
split: for `q≥0` use the original row splitting, and for `q<0` use
the row of zero objects. -/
def HorseshoeData.extendedSplitting (H : HorseshoeData S hS) (q : ℤ) :
    (H.extendedDiagram.map (HomologicalComplex.eval C (.up ℤ) q)).Splitting :=
  HomologicalComplex.extendDiagramSplitting H.diagram H.split ComplexShape.embeddingUpNat q

omit [HasInjectiveResolutions C] in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. The zero-extended diagram is a short exact sequence of integer
cochain complexes, by its splitting in every degree. -/
theorem HorseshoeData.extended_shortExact (H : HorseshoeData S hS) :
    H.extendedDiagram.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  exact fun q => (H.extendedSplitting q).shortExact

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. The three zero-extended coaugmentations give a morphism from
`S` concentrated at cochain degree zero to the extended horseshoe
diagram. -/
def HorseshoeData.extendedAugmentation (H : HorseshoeData S hS) :
    S.map (CochainComplex.singleFunctor C 0) ⟶ H.extendedDiagram where
  τ₁ := H.res₁.ι'
  τ₂ := H.res₂.ι'
  τ₃ := H.res₃.ι'
  comm₁₂ := H.leftResolutionHom.ι'_comp_hom'
  comm₂₃ := H.rightResolutionHom.ι'_comp_hom'

set_option backward.isDefEq.respectTransparency false in
omit [HasInjectiveResolutions C] in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Suppose `C` has a derived category and write `ε_k` for the
image of the `k`-th coaugmentation there. The triangle boundary of
`S[0]` satisfies `δ_(S[0]) ≫ ε₁[1] = ε₃ ≫ δ_(H_extended)`. -/
theorem HorseshoeData.original_single_boundary [HasDerivedCategory C]
    (H : HorseshoeData S hS) :
    DerivedCategory.triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0)) ≫
      (DerivedCategory.Q.map H.res₁.ι')⟦(1 : ℤ)⟧' =
    DerivedCategory.Q.map H.res₃.ι' ≫ DerivedCategory.triangleOfSESδ H.extended_shortExact :=
  DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0)) H.extended_shortExact H.extendedAugmentation

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasExt.{v} C] [HasDerivedCategory C]
variable {S : ShortComplex C} {hS : S.ShortExact}

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Suppose `C` has a derived category and Ext at its hom-set
universe. Writing `ξ` for the derived morphism of the Yoneda extension
class of `S` and `ε_k` for the coaugmentations, one has
`ξ ≫ ε₁[1] = ε₃ ≫ δ_(H_extended)`. -/
theorem HorseshoeData.original_extClass_boundary (H : HorseshoeData S hS) :
    hS.extClass.hom ≫ (DerivedCategory.Q.map H.res₁.ι')⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map H.res₃.ι' ≫
        DerivedCategory.triangleOfSESδ H.extended_shortExact := by
  rw [hS.extClass_hom]
  exact H.original_single_boundary

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Suppose `C` has a derived category and Ext at its hom-set
universe. For the derived extension morphism `ξ` and coaugmentation
isomorphisms `ε_k`, the extended horseshoe boundary is
`ε₃⁻¹ ≫ ξ ≫ ε₁[1]`. -/
theorem HorseshoeData.original_extClass_normalized (H : HorseshoeData S hS) :
    CategoryTheory.inv (DerivedCategory.Q.map H.res₃.ι') ≫ hS.extClass.hom ≫
      (DerivedCategory.Q.map H.res₁.ι')⟦(1 : ℤ)⟧' =
      DerivedCategory.triangleOfSESδ H.extended_shortExact := by
  rw [H.original_extClass_boundary, IsIso.inv_hom_id_assoc]

end CategoryTheory.Functor.RightDerived

end
