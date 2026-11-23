/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexColimits
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Simplicial homology preserves coproducts

Fixed-coefficient simplicial homology valued in `AddCommGrpCat` preserves
arbitrary discrete coproducts.  Simplicial chains already preserve all
colimits; AB4 makes discrete colimits of abelian groups exact, so homology
commutes with them.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w

namespace SSet

/-- Discrete colimits of abelian groups preserve homology. -/
noncomputable instance {J : Type w} :
    (colim (J := Discrete J)
      (C := AddCommGrpCat.{w})).PreservesHomology := by
  have : PreservesFiniteLimits
      (colim (J := Discrete J) (C := AddCommGrpCat.{w})) :=
    inferInstance
  have : PreservesFiniteColimits
      (colim (J := Discrete J) (C := AddCommGrpCat.{w})) :=
    inferInstance
  infer_instance

/-- Fixed-coefficient simplicial homology preserves arbitrary discrete
coproducts. -/
instance {J : Type w} (R : AddCommGrpCat.{w}) (n : ℕ) :
    PreservesColimitsOfShape (Discrete J)
      (SSet.homologyFunctor R n) := by
  have h : SSet.homologyFunctor R n =
      (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
          (ComplexShape.down ℕ) n :=
    rfl
  rw [h]
  infer_instance

/-- Homology of a coproduct of simplicial sets is the coproduct of their
homologies. -/
noncomputable def homologySigmaIso {I : Type w}
    (F : I → SSet.{w}) (R : AddCommGrpCat.{w}) (n : ℕ) :
    (∐ F).homology R n ≅ ∐ fun i => (F i).homology R n :=
  preservesColimitIso (SSet.homologyFunctor R n) (Discrete.functor F) ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The homology coproduct comparison sends the map induced by a coproduct
inclusion to the corresponding homology coproduct inclusion. -/
@[reassoc]
theorem homologyMap_ι_comp_homologySigmaIso_hom {I : Type w}
    (F : I → SSet.{w}) (R : AddCommGrpCat.{w}) (n : ℕ) (i : I) :
    SSet.homologyMap (Sigma.ι F i) R n ≫
        (homologySigmaIso F R n).hom =
      Sigma.ι (fun j => (F j).homology R n) i := by
  change (SSet.homologyFunctor R n).map
      (colimit.ι (Discrete.functor F) ⟨i⟩) ≫
        ((preservesColimitIso (SSet.homologyFunctor R n)
          (Discrete.functor F)).hom ≫
          (HasColimit.isoOfNatIso Discrete.natIsoFunctor).hom) =
    colimit.ι (Discrete.functor
      (fun j => (F j).homology R n)) ⟨i⟩
  rw [← Category.assoc, ι_preservesColimitIso_hom]
  change colimit.ι
      (Discrete.functor F ⋙ SSet.homologyFunctor R n) ⟨i⟩ ≫
        (HasColimit.isoOfNatIso Discrete.natIsoFunctor).hom = _
  rw [HasColimit.ι_isoOfNatIso_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse homology coproduct comparison followed by a source inclusion
is the homology map induced by the corresponding simplicial-set coproduct
inclusion. -/
@[reassoc]
theorem homologySigmaIso_inv_comp_homologyMap_ι {I : Type w}
    (F : I → SSet.{w}) (R : AddCommGrpCat.{w}) (n : ℕ) (i : I) :
    Sigma.ι (fun j => (F j).homology R n) i ≫
        (homologySigmaIso F R n).inv =
      SSet.homologyMap (Sigma.ι F i) R n := by
  apply (cancel_mono (homologySigmaIso F R n).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    homologyMap_ι_comp_homologySigmaIso_hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The homology coproduct comparison is natural for a reindexing function
and a family of simplicial maps. -/
theorem homologySigmaIso_naturality
    {I K : Type w} {F : I → SSet.{w}} {G : K → SSet.{w}}
    (e : I → K) (phi : ∀ i, F i ⟶ G (e i))
    (R : AddCommGrpCat.{w}) (n : ℕ) :
    SSet.homologyMap (Sigma.map' e phi) R n ≫
        (homologySigmaIso G R n).hom =
      (homologySigmaIso F R n).hom ≫
        Sigma.map' e (fun i => SSet.homologyMap (phi i) R n) := by
  apply (cancel_epi (homologySigmaIso F R n).inv).1
  apply (coproductIsCoproduct
    (fun i => (F i).homology R n)).hom_ext
  rintro ⟨i⟩
  change Sigma.ι (fun j => (F j).homology R n) i ≫
      (homologySigmaIso F R n).inv ≫
      SSet.homologyMap (Sigma.map' e phi) R n ≫
      (homologySigmaIso G R n).hom =
    Sigma.ι (fun j => (F j).homology R n) i ≫
      (homologySigmaIso F R n).inv ≫
      (homologySigmaIso F R n).hom ≫
      Sigma.map' e (fun i => SSet.homologyMap (phi i) R n)
  simp only [← Category.assoc]
  rw [homologySigmaIso_inv_comp_homologyMap_ι,
    ← SSet.homologyMap_comp,
    Sigma.ι_comp_map',
    SSet.homologyMap_comp,
    Category.assoc,
    homologyMap_ι_comp_homologySigmaIso_hom,
    homologyMap_ι_comp_homologySigmaIso_hom,
    Sigma.ι_comp_map']

end SSet

end
