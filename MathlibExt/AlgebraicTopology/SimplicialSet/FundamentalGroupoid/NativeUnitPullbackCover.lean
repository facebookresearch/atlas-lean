/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeUnitFiberComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseChangeDeck
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
public import MathlibExt.Topology.Homotopy.HSpaceNativeCoverDeck

/-!
# The literal native cover and the pulled unit total

The original native-cover Cartesian map followed by the original
mapping-path section gives a canonical map into the unit total pulled to
the base's native cover. The actual pullback square and right properness
derive that this map is weak; no cover comparison is supplied.

The map retains the original source and base-cover projections and
intertwines the same inverse-precomposition deck actions. The proved
H-space deck homotopies therefore make every actual pulled-unit deck map
act identically on homology, with independent coefficient universes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u uC vC

public section

namespace SSet.KanComplex

/-- The actual unit mapping-path total pulled to the original base native cover. -/
abbrev unitPulledCoverTotal (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  pullback (SSet.mappingPathTarget (nativeCoverUnit X))
    (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
      ((nativeCoverUnit X).app (op ⦋0⦌) x))

/-- The canonical map uses only the original cover map and original mapping-path section. -/
def nativeCoverToUnitPulledTotal (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCover X x ⟶ unitPulledCoverTotal X x :=
  pullback.lift (nativeCoverProjection X x ≫ SSet.mappingPathSection (nativeCoverUnit X))
    (nativeCoverMap (nativeCoverUnit X) x) (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => nativeCoverProjection X x ≫ k)
          (SSet.mappingPathSection_comp_target (nativeCoverUnit X))).trans
          (nativeCoverMap_projection (nativeCoverUnit X) x).symm))

/-- The original mapping-path source coordinate is retained. -/
theorem nativeCoverToUnitPulledTotal_fst (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverToUnitPulledTotal X x ≫
      pullback.fst (SSet.mappingPathTarget (nativeCoverUnit X))
        (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
          ((nativeCoverUnit X).app (op ⦋0⦌) x)) =
      nativeCoverProjection X x ≫ SSet.mappingPathSection (nativeCoverUnit X) :=
  pullback.lift_fst _ _ _

/-- The original induced native map is the complete base-cover coordinate. -/
theorem nativeCoverToUnitPulledTotal_snd (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverToUnitPulledTotal X x ≫
      pullback.snd (SSet.mappingPathTarget (nativeCoverUnit X))
        (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
          ((nativeCoverUnit X).app (op ⦋0⦌) x)) =
      nativeCoverMap (nativeCoverUnit X) x :=
  pullback.lift_snd _ _ _

/-- Returning through the original mapping-path retract gives the literal source projection. -/
theorem nativeCoverToUnitPulledTotal_original (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverToUnitPulledTotal X x ≫
      (pullback.fst (SSet.mappingPathTarget (nativeCoverUnit X))
          (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
            ((nativeCoverUnit X).app (op ⦋0⦌) x)) ≫
        SSet.mappingPathRetract (nativeCoverUnit X)) = nativeCoverProjection X x :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ SSet.mappingPathRetract (nativeCoverUnit X))
      (nativeCoverToUnitPulledTotal_fst X x)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => nativeCoverProjection X x ≫ k)
            (SSet.mappingPathSection_comp_retract (nativeCoverUnit X))).trans
              (Category.comp_id _))))

private def unitSectionPullbackMap (X : SSet.{u}) (x : X _⦋0⦌) :
    pullback (nativeCoverUnit X)
      (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x)) ⟶ unitPulledCoverTotal X x :=
  nativeCoverBaseChangeMap (SSet.mappingPathSection (nativeCoverUnit X))
    (SSet.mappingPathSection_comp_target (nativeCoverUnit X))
    ((nativeCoverUnit X).app (op ⦋0⦌) x)

/-- The actual original cover-to-unit-total map is weak, from its computed pullback square. -/
theorem nativeCoverToUnitPulledTotal_mem_realizationWeakEquivalences
    (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    SSet.realizationWeakEquivalences (nativeCoverToUnitPulledTotal X x) := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let : SSet.KanComplex B := SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid X)
  have hSection : SSet.realizationWeakEquivalences (unitSectionPullbackMap X x) :=
    nativeCoverBaseChangeMap_mem_realizationWeakEquivalences
      (SSet.mappingPathSection (nativeCoverUnit X))
      (SSet.mappingPathSection_comp_target (nativeCoverUnit X))
      ((nativeCoverUnit X).app (op ⦋0⦌) x)
      ((SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
        (SSet.KanComplex.W.of_mappingPathSection (nativeCoverUnit X)))
  let : (SSet.mapFundamentalGroupoid (nativeCoverUnit X)).IsEquivalence :=
    nativeCoverUnit_mapFundamentalGroupoid_isEquivalence X
  let : IsIso (nativeCoverCartesianComparison (nativeCoverUnit X) x) :=
    nativeCoverCartesianComparison_isIso _ _
  have hMap : nativeCoverToUnitPulledTotal X x =
      nativeCoverCartesianComparison (nativeCoverUnit X) x ≫ unitSectionPullbackMap X x := by
    apply pullback.hom_ext
    · rw [nativeCoverToUnitPulledTotal_fst, Category.assoc]
      change _ = nativeCoverCartesianComparison (nativeCoverUnit X) x ≫
        (nativeCoverBaseChangeMap _ _ _ ≫ pullback.fst _ _)
      rw [nativeCoverBaseChangeMap_fst, ← Category.assoc, nativeCoverCartesianComparison_fst]
    · rw [nativeCoverToUnitPulledTotal_snd, Category.assoc]
      change _ = nativeCoverCartesianComparison (nativeCoverUnit X) x ≫
        (nativeCoverBaseChangeMap _ _ _ ≫ pullback.snd _ _)
      rw [nativeCoverBaseChangeMap_snd, nativeCoverCartesianComparison_snd]
  exact hMap.symm ▸ SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso _) hSection

/-- Every original base deck element acts by its SAME inverse-precomposition map. -/
def unitPulledCoverBaseDeckMap {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk
      ((nativeCoverUnit X).app (op ⦋0⦌) x))) :
    unitPulledCoverTotal X x ⟶ unitPulledCoverTotal X x :=
  nativeCoverBaseChangeDeckMap (SSet.mappingPathTarget (nativeCoverUnit X))
    ((nativeCoverUnit X).app (op ⦋0⦌) x) g

/-- The actual original source endomorphism acts through the actual nerve-unit map. -/
def unitPulledCoverDeckMap {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    unitPulledCoverTotal X x ⟶ unitPulledCoverTotal X x :=
  unitPulledCoverBaseDeckMap
    ((SSet.mapFundamentalGroupoid (nativeCoverUnit X)).mapEnd
      (SSet.FundamentalGroupoid.mk x) g)

private theorem unitPulledCoverDeckMap_fst {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    unitPulledCoverDeckMap g ≫ pullback.fst
      (SSet.mappingPathTarget (nativeCoverUnit X))
      (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x)) = pullback.fst _ _ :=
  nativeCoverBaseChangeDeckMap_fst _ _ _

private theorem unitPulledCoverDeckMap_snd {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    unitPulledCoverDeckMap g ≫ pullback.snd
      (SSet.mappingPathTarget (nativeCoverUnit X))
      (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x)) =
    pullback.snd (SSet.mappingPathTarget (nativeCoverUnit X))
        (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
          ((nativeCoverUnit X).app (op ⦋0⦌) x)) ≫
      nativeCoverDeckMap
      (X := CategoryTheory.nerve (SSet.FundamentalGroupoid X))
      (x := (nativeCoverUnit X).app (op ⦋0⦌) x)
      ((SSet.mapFundamentalGroupoid (nativeCoverUnit X)).mapEnd
        (SSet.FundamentalGroupoid.mk x) g) :=
  nativeCoverBaseChangeDeckMap_snd (SSet.mappingPathTarget (nativeCoverUnit X))
    ((nativeCoverUnit X).app (op ⦋0⦌) x)
    ((SSet.mapFundamentalGroupoid (nativeCoverUnit X)).mapEnd
      (SSet.FundamentalGroupoid.mk x) g)

/-- The actual cover comparison intertwines the literal original deck action. -/
theorem nativeCoverToUnitPulledTotal_deck {X : SSet.{u}} [SSet.KanComplex X]
    (x : X _⦋0⦌) (g : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverDeckMap g ≫ nativeCoverToUnitPulledTotal X x =
      nativeCoverToUnitPulledTotal X x ≫ unitPulledCoverDeckMap g := by
  let B : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let eta : X ⟶ B := nativeCoverUnit X
  let b : B _⦋0⦌ := eta.app (op ⦋0⦌) x
  let bg : End (SSet.FundamentalGroupoid.mk b) :=
    (SSet.mapFundamentalGroupoid eta).mapEnd (SSet.FundamentalGroupoid.mk x) g
  let db : nativeCover B b ⟶ nativeCover B b := nativeCoverDeckMap (X := B) (x := b) bg
  let : SSet.KanComplex B :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid X)
  apply pullback.hom_ext
  · have hL := (Category.assoc (nativeCoverDeckMap g) (nativeCoverToUnitPulledTotal X x)
        (pullback.fst _ _)).trans
      ((congrArg (fun k => nativeCoverDeckMap g ≫ k)
        (nativeCoverToUnitPulledTotal_fst X x)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ SSet.mappingPathSection (nativeCoverUnit X))
              (nativeCoverDeckMap_projection g))))
    have hR := (Category.assoc (nativeCoverToUnitPulledTotal X x) (unitPulledCoverDeckMap g)
        (pullback.fst _ _)).trans
      ((congrArg (fun k => nativeCoverToUnitPulledTotal X x ≫ k)
        (unitPulledCoverDeckMap_fst g)).trans (nativeCoverToUnitPulledTotal_fst X x))
    exact hL.trans hR.symm
  · have hL := (Category.assoc (nativeCoverDeckMap g) (nativeCoverToUnitPulledTotal X x)
        (pullback.snd _ _)).trans
      (congrArg (fun k => nativeCoverDeckMap g ≫ k) (nativeCoverToUnitPulledTotal_snd X x))
    have hR := (Category.assoc (nativeCoverToUnitPulledTotal X x) (unitPulledCoverDeckMap g)
        (pullback.snd _ _)).trans
      ((congrArg (fun k => nativeCoverToUnitPulledTotal X x ≫ k)
        (unitPulledCoverDeckMap_snd g)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k : nativeCover X x ⟶ nativeCover B b => k ≫ db)
              (nativeCoverToUnitPulledTotal_snd X x))))
    have hNat : nativeCoverDeckMap g ≫ nativeCoverMap eta x =
        nativeCoverMap eta x ≫ db := nativeCoverMap_deck eta x g
    exact hL.trans (hNat.trans hR.symm)

end SSet.KanComplex

namespace TopCat.HSpaceHomotopyAction

/-- H-space unit traces force triviality of the actual pulled-unit deck homology action,
for every original point and independent coefficient category. -/
theorem unitPulledCoverDeckMap_homologyMap_eq_id
    (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (x : X)
    (g : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap (SSet.KanComplex.unitPulledCoverDeckMap g) R n = 𝟙 _ := by
  let SX := TopCat.toSSet.obj X
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid SX)
  let p := SSet.KanComplex.nativeCoverProjection B
    ((SSet.KanComplex.nativeCoverUnit SX).app (op ⦋0⦌) sx)
  let : SSet.KanComplex SX := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex B := SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid SX)
  let : SSet.KanComplex (SSet.KanComplex.nativeCover SX sx) :=
    SSet.KanComplex.nativeCover_kanComplex _ _
  let : Fibration p := SSet.KanComplex.nativeCoverProjection_fibration _ _
  let a := pullback.fst (SSet.mappingPathTarget (SSet.KanComplex.nativeCoverUnit SX)) p
  let : Fibration a := SSet.fibration_of_isPullback (IsPullback.of_hasPullback _ _)
  let : SSet.KanComplex (SSet.KanComplex.unitPulledCoverTotal SX sx) :=
    HomotopicalAlgebra.isFibrant_of_fibration a
  let c := SSet.KanComplex.nativeCoverToUnitPulledTotal SX sx
  let H := SSet.homologyFunctor R n
  have hc : SSet.KanComplex.W c := (SSet.KanComplex.W_iff_realizationWeakEquivalence c).mpr
    (SSet.KanComplex.nativeCoverToUnitPulledTotal_mem_realizationWeakEquivalences SX sx)
  let : QuasiIso (SSet.chainComplexMap c R) := hc.quasiIso_chainComplexMap R
  let : IsIso (H.map c) := (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap c R) n)
  have hSquare : H.map (SSet.KanComplex.nativeCoverDeckMap g) ≫ H.map c =
      H.map c ≫ H.map (SSet.KanComplex.unitPulledCoverDeckMap g) :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (SSet.KanComplex.nativeCoverToUnitPulledTotal_deck sx g)).trans
        (H.map_comp _ _))
  apply (cancel_epi (H.map c)).mp
  exact hSquare.symm.trans
    ((congrArg (fun k => k ≫ H.map c) (nativeCoverDeckMap_homologyMap_eq_id X x g R n)).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- Every base endomorphism is reached by the computed unit endomorphism map,
so the same homology identity covers ALL base deck labels. -/
theorem unitPulledCoverBaseDeckMap_homologyMap_eq_id
    (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (x : X)
    (g : End (SSet.FundamentalGroupoid.mk
      ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x))))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap (SSet.KanComplex.unitPulledCoverBaseDeckMap g) R n = 𝟙 _ := by
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let F := SSet.mapFundamentalGroupoid
    (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X))
  let : F.IsEquivalence := SSet.KanComplex.nativeCoverUnit_mapFundamentalGroupoid_isEquivalence _
  let a : End (SSet.FundamentalGroupoid.mk sx) := End.of (F.preimage g.asHom)
  have ha : F.mapEnd (SSet.FundamentalGroupoid.mk sx) a = g :=
    End.ext (F.map_preimage g.asHom)
  have hMap : SSet.KanComplex.unitPulledCoverDeckMap a =
      SSet.KanComplex.unitPulledCoverBaseDeckMap g :=
    congrArg (SSet.KanComplex.unitPulledCoverBaseDeckMap
      (X := TopCat.toSSet.obj X) (x := sx)) ha
  exact (congrArg (fun f => SSet.homologyMap f R n) hMap).symm.trans
    (unitPulledCoverDeckMap_homologyMap_eq_id X x a R n)

end TopCat.HSpaceHomotopyAction

namespace SSet.KanComplex

private theorem unitPulledCoverBaseDeckMap_eq_computation {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk ((nativeCoverUnit X).app (op ⦋0⦌) x))) :
    unitPulledCoverBaseDeckMap g = nativeCoverBaseChangeDeckMap
      (SSet.mappingPathTarget (nativeCoverUnit X)) ((nativeCoverUnit X).app (op ⦋0⦌) x) g := by
  unfold unitPulledCoverBaseDeckMap; rfl

/-- The existing unit-total action is the original pulled native-cover deck action. -/
theorem unitPulledCoverBaseDeckMap_eq {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk ((nativeCoverUnit X).app (op ⦋0⦌) x))) :
    unitPulledCoverBaseDeckMap g = nativeCoverBaseChangeDeckMap
      (SSet.mappingPathTarget (nativeCoverUnit X)) ((nativeCoverUnit X).app (op ⦋0⦌) x) g :=
  unitPulledCoverBaseDeckMap_eq_computation g

end SSet.KanComplex
