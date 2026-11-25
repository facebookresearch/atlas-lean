/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import MathlibExt.Algebra.Homology.HomologyMapSquare
public import MathlibExt.Algebra.Homology.HomotopyCofiberSplitting

/-!
# Homology of a mapping cone with zero source

The mapping cone of a map out of a zero cochain complex has the homology of
the target.  The comparison is natural in commuting squares.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical short complex `F ⟶ G ⟶ G` associated to a map whose
source is zero.  This is implementation data for the mapping-cone comparison. -/
noncomputable def mappingConeZeroSourceShortComplex
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk f (𝟙 G) (by
    rw [Category.comp_id]
    exact hF.eq_of_src _ _)

/-- The canonical zero-source short complex is short exact. -/
theorem mappingConeZeroSourceShortComplex_shortExact
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    (mappingConeZeroSourceShortComplex f hF).ShortExact := by
  let S := mappingConeZeroSourceShortComplex f hF
  have hf : S.f = 0 := hF.eq_of_src _ _
  have hgMono : Mono S.g := by
    change Mono (𝟙 G)
    infer_instance
  have hfMono : Mono S.f := hF.mono _
  have hgEpi : Epi S.g := by
    change Epi (𝟙 G)
    infer_instance
  exact ShortComplex.ShortExact.mk'
    ((S.exact_iff_mono hf).2 hgMono) hfMono hgEpi

/-- A mapping cone with zero source is canonically isomorphic to its target. -/
noncomputable def mappingConeZeroSourceIso
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    mappingCone f ≅ G :=
  HomologicalComplex.homotopyCofiber.zeroSourceIso f hF

/-- The canonical projection from the mapping cone of a map with zero source
to its target. -/
noncomputable def mappingConeZeroSourceDesc
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    mappingCone f ⟶ G :=
  (mappingConeZeroSourceIso f hF).hom

/-- The canonical projection from a zero-source mapping cone is a
quasi-isomorphism. -/
theorem mappingConeZeroSourceDesc_quasiIso
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    QuasiIso (mappingConeZeroSourceDesc f hF) := by
  let _ : IsIso (mappingConeZeroSourceDesc f hF) :=
    (mappingConeZeroSourceIso f hF).isIso_hom
  infer_instance

/-- The cone inclusion followed by the zero-source projection is the
identity. -/
@[reassoc]
theorem mappingCone_inr_comp_zeroSourceDesc
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    mappingCone.inr f ≫ mappingConeZeroSourceDesc f hF = 𝟙 G := by
  exact HomologicalComplex.homotopyCofiber.inr_zeroSourceDesc f hF

/-- The zero-source projection followed by the cone inclusion is the
identity. -/
@[reassoc]
theorem mappingConeZeroSourceDesc_comp_inr
    {F G : CochainComplex C ℤ} (f : F ⟶ G) (hF : IsZero F) :
    mappingConeZeroSourceDesc f hF ≫ mappingCone.inr f =
      𝟙 (mappingCone f) := by
  exact HomologicalComplex.homotopyCofiber.zeroSourceDesc_inr f hF

/-- The mapping cone of a map from a zero source has the homology of its
target. -/
noncomputable def mappingConeZeroSourceHomologyIso
    {F G : CochainComplex C ℤ} (f : F ⟶ G)
    (hF : IsZero F) (k : ℤ) :
    (mappingCone f).homology k ≅ G.homology k :=
  let _ : QuasiIso (mappingConeZeroSourceDesc f hF) :=
    mappingConeZeroSourceDesc_quasiIso f hF
  asIso (HomologicalComplex.homologyMap
    (mappingConeZeroSourceDesc f hF) k)

/-- The mapping-cone inclusion followed by the zero-source homology
coordinate is the identity. -/
@[reassoc]
theorem homologyMap_inr_comp_mappingConeZeroSourceHomologyIso_hom
    {F G : CochainComplex C ℤ} (f : F ⟶ G)
    (hF : IsZero F) (k : ℤ) :
    HomologicalComplex.homologyMap (mappingCone.inr f) k ≫
        (mappingConeZeroSourceHomologyIso f hF k).hom = 𝟙 _ := by
  change HomologicalComplex.homologyMap (mappingCone.inr f) k ≫
      HomologicalComplex.homologyMap
        (mappingConeZeroSourceDesc f hF) k = 𝟙 _
  rw [← HomologicalComplex.homologyMap_comp,
    mappingCone_inr_comp_zeroSourceDesc,
    HomologicalComplex.homologyMap_id]

/-- The zero-source mapping-cone projection is natural in commuting
squares. -/
@[reassoc]
theorem mappingConeZeroSourceDesc_naturality
    {F G F' G' : CochainComplex C ℤ}
    (f : F ⟶ G) (f' : F' ⟶ G')
    (hF : IsZero F) (hF' : IsZero F')
    (a : F ⟶ F') (b : G ⟶ G')
    (comm : f ≫ b = a ≫ f') :
    mappingCone.map f f' a b comm ≫
        mappingConeZeroSourceDesc f' hF' =
      mappingConeZeroSourceDesc f hF ≫ b := by
  rw [← cancel_epi (mappingConeZeroSourceIso f hF).inv]
  change mappingCone.inr f ≫
        (mappingCone.map f f' a b comm ≫
          mappingConeZeroSourceDesc f' hF') =
      mappingCone.inr f ≫ (mappingConeZeroSourceDesc f hF ≫ b)
  calc
    _ = (b ≫ mappingCone.inr f') ≫
        mappingConeZeroSourceDesc f' hF' := by
      rw [← Category.assoc, mappingCone.map, mappingCone.inr_desc]
    _ = b := by
      rw [Category.assoc, mappingCone_inr_comp_zeroSourceDesc,
        Category.comp_id]
    _ = (mappingCone.inr f ≫
        mappingConeZeroSourceDesc f hF) ≫ b := by
      rw [mappingCone_inr_comp_zeroSourceDesc, Category.id_comp]
    _ = _ := Category.assoc _ _ _

/-- Naturality of the zero-source mapping-cone homology comparison. -/
@[reassoc]
theorem mappingConeZeroSourceHomologyIso_hom_naturality
    {F G F' G' : CochainComplex C ℤ}
    (f : F ⟶ G) (f' : F' ⟶ G')
    (hF : IsZero F) (hF' : IsZero F')
    (a : F ⟶ F') (b : G ⟶ G')
    (comm : f ≫ b = a ≫ f') (k : ℤ) :
    HomologicalComplex.homologyMap
        (mappingCone.map f f' a b comm) k ≫
        (mappingConeZeroSourceHomologyIso f' hF' k).hom =
      (mappingConeZeroSourceHomologyIso f hF k).hom ≫
        HomologicalComplex.homologyMap b k := by
  change HomologicalComplex.homologyMap
        (mappingCone.map f f' a b comm) k ≫
        HomologicalComplex.homologyMap
          (mappingConeZeroSourceDesc f' hF') k =
      HomologicalComplex.homologyMap
          (mappingConeZeroSourceDesc f hF) k ≫
        HomologicalComplex.homologyMap b k
  exact HomologicalComplex.homologyMap_square
    (mappingConeZeroSourceDesc_naturality f f' hF hF' a b comm) k

end CochainComplex

end
