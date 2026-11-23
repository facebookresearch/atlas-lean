/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.Coproducts

/-!
# Homology decomposition by connected components

A simplicial set is the coproduct of its connected-component subcomplexes.
Since fixed-coefficient simplicial homology preserves arbitrary coproducts
of simplicial sets, its homology is canonically the coproduct of the
homologies of those components.

The comparison records the formula on each component inclusion.  Conjugating
the standard retraction of a coproduct inclusion through this comparison
makes every component homology inclusion a split monomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w

namespace SSet

/-- Homology of a simplicial set is canonically the coproduct of the
homologies of its connected-component subcomplexes. -/
noncomputable def homologyComponentsIso (X : SSet.{w})
    (R : AddCommGrpCat.{w}) (n : ℕ) :
    X.homology R n ≅
      ∐ fun c : π₀ X => (π₀.component c : SSet.{w}).homology R n :=
  (homologyFunctor R n).mapIso
      ((π₀.isColimitCofan X).coconePointUniqueUpToIso
        (coproductIsCoproduct fun c : π₀ X =>
          (π₀.component c : SSet.{w}))) ≪≫
    homologySigmaIso
      (fun c : π₀ X => (π₀.component c : SSet.{w})) R n

set_option backward.isDefEq.respectTransparency false in
/-- Under the component-homology decomposition, the map induced by a
component inclusion is the corresponding coproduct inclusion. -/
@[reassoc]
theorem homologyMap_component_ι_comp_homologyComponentsIso_hom
    (X : SSet.{w}) (R : AddCommGrpCat.{w}) (n : ℕ) (c : π₀ X) :
    SSet.homologyMap (π₀.component c).ι R n ≫
        (homologyComponentsIso X R n).hom =
      Sigma.ι
        (fun d : π₀ X =>
          (π₀.component d : SSet.{w}).homology R n) c := by
  let e := (π₀.isColimitCofan X).coconePointUniqueUpToIso
    (coproductIsCoproduct fun d : π₀ X =>
      (π₀.component d : SSet.{w}))
  have hleg : (π₀.component c).ι ≫ e.hom =
      Sigma.ι (fun d : π₀ X =>
        (π₀.component d : SSet.{w})) c := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (π₀.isColimitCofan X)
      (coproductIsCoproduct fun d : π₀ X =>
        (π₀.component d : SSet.{w})) ⟨c⟩
  change SSet.homologyMap (π₀.component c).ι R n ≫
      SSet.homologyMap e.hom R n ≫
        (homologySigmaIso
          (fun d : π₀ X => (π₀.component d : SSet.{w})) R n).hom = _
  rw [← Category.assoc, ← SSet.homologyMap_comp, hleg]
  exact homologyMap_ι_comp_homologySigmaIso_hom
    (fun d : π₀ X => (π₀.component d : SSet.{w})) R n c

/-- The canonical splitting of the homology map induced by a simplicial
connected-component inclusion. -/
noncomputable def homologyMapComponentSplitMono
    (X : SSet.{w}) (R : AddCommGrpCat.{w}) (n : ℕ) (c : π₀ X) :
    SplitMono (SSet.homologyMap (π₀.component c).ι R n) where
  retraction :=
    (homologyComponentsIso X R n).hom ≫
      retraction (Sigma.ι (fun d : π₀ X =>
        (π₀.component d : SSet.{w}).homology R n) c)
  id := by
    rw [← Category.assoc,
      homologyMap_component_ι_comp_homologyComponentsIso_hom]
    simp

/-- The homology map induced by the inclusion of any connected-component
subcomplex is a split monomorphism. -/
noncomputable instance homologyMap_component_ι_isSplitMono
    (X : SSet.{w}) (R : AddCommGrpCat.{w}) (n : ℕ) (c : π₀ X) :
    IsSplitMono (SSet.homologyMap (π₀.component c).ι R n) :=
  IsSplitMono.mk' (homologyMapComponentSplitMono X R n c)

end SSet

end
