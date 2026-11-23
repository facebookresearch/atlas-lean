/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellNativeRelativeBasis
import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyRelativeHomology
import MathlibExt.AlgebraicTopology.PlusConstruction.CellFundamentalGroupQuotient
import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
import Mathlib.CategoryTheory.Functor.FullyFaithful
public import MathlibExt.Topology.CWComplex.UnbasedWhitehead
public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Ring.Defs
public import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff

/-!
# Independent classical plus constructions

For a connected Hausdorff classical CW source and a perfect normal subgroup
of its actual fundamental group, the original two/three-cell construction
has the prescribed kernel, canonical acyclic fibers at every target point,
and homology isomorphisms with every integral target local system.

The full output retains the entire relative cover quotient and the same
regular-cover projection. Its CW realization model, literal forward
comparison, continuous inverse and both ordinary inverse homotopies are
constructed from the actual attachments. The construction is independent
of Quillen's Q construction. This is the classical construction requested
in Weibel, The K-book, IV.1.4; no mapping universality is asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory
open scoped Simplicial

universe u uC vC

-- The actual stock colimit choices are lexical and private. These avoid
-- repeated forall-index synthesis without exporting colliding instances.
private local instance rawAddCommGrpColimits (I : Type u) :
    HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance rawAddCommGrpCoproducts : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance rawIntegerModuleColimits (I : Type u) :
    HasColimitsOfShape (Discrete I) (ModuleCat.{u} ℤ) :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

private local instance rawIntegerModuleCoproducts : HasCoproducts.{u} (ModuleCat.{u} ℤ) :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

namespace OriginalRegularPlusSourceComparison

section Categorical

variable {C : Type uC} [Category.{vC} C] [HasPullbacks C]
variable {A B Z E D : C} (f : A ⟶ B) (g : B ⟶ Z) (pY : E ⟶ B) (pZ : D ⟶ Z)
variable (e : E ≅ pullback g pZ) (he : e.hom ≫ pullback.fst g pZ = pY)

/-- The existing comparison is pulled back by the existing stock map. -/
private def pulledComparison : pullback f pY ⟶ pullback f (pullback.fst g pZ) :=
  pullback.map f pY f (pullback.fst g pZ) (𝟙 A) e.hom (𝟙 B)
    (by simp) ((Category.comp_id pY).trans he.symm)

private theorem pulledComparison_isIso : IsIso (pulledComparison f g pY pZ e he) := by
  change IsIso (pullback.map f pY f (pullback.fst g pZ) (𝟙 A) e.hom (𝟙 B)
    (by simp) ((Category.comp_id pY).trans he.symm))
  infer_instance

/-- The stock pulled Iso and stock pasting Iso give the actual source Iso. -/
private def sourceIso : pullback f pY ≅ pullback (f ≫ g) pZ := by
  have hi : IsIso (pulledComparison f g pY pZ e he) := pulledComparison_isIso f g pY pZ e he
  exact @asIso C _ _ _ (pulledComparison f g pY pZ e he) hi ≪≫
    pullbackRightPullbackFstIso g pZ f

/-- Its original X projection is unchanged. -/
private theorem sourceIso_fst :
    (sourceIso f g pY pZ e he).hom ≫ pullback.fst (f ≫ g) pZ = pullback.fst f pY := by
  change (pulledComparison f g pY pZ e he ≫ (pullbackRightPullbackFstIso g pZ f).hom) ≫
    pullback.fst (f ≫ g) pZ = pullback.fst f pY
  rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst]
  simp only [pulledComparison, pullback.map, pullback.lift_fst, Category.comp_id]

/-- Its whole cover projection is the SAME original two map, Cartesian comparison and third projection. -/
private theorem sourceIso_snd :
    (sourceIso f g pY pZ e he).hom ≫ pullback.snd (f ≫ g) pZ =
      pullback.snd f pY ≫ e.hom ≫ pullback.snd g pZ := by
  change (pulledComparison f g pY pZ e he ≫ (pullbackRightPullbackFstIso g pZ f).hom) ≫
    pullback.snd (f ≫ g) pZ = pullback.snd f pY ≫ e.hom ≫ pullback.snd g pZ
  rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc]
  simp only [pulledComparison, pullback.map, pullback.lift_snd, Category.assoc]

end Categorical

section Original

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
  [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
  [P.Normal] [Group.IsPerfect P]

private abbrev twoInclusion := TopCat.toSSet.map (LoopCellAttachment.inclusion X x P)
private abbrev threeInclusion := TopCat.toSSet.map
  (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P)
private abbrev oldProjection := SSet.KanComplex.nativeCoverProjection
  (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
  (LoopCellSphericalGenerators.nativeTargetPoint X x P)
private abbrev newProjection := AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeProjection X x P
private abbrev oldCoverIso := AlgebraicTopology.LoopCellRegularThreeComparison.nativeTwoToThreePullbackIso X x P

/-- This property comes from the actual native Cartesian comparison's first projection. -/
private theorem oldCoverIso_projection :
    (oldCoverIso X x P).hom ≫ pullback.fst (threeInclusion X x P) (newProjection X x P) =
      oldProjection X x P := by
  rw [AlgebraicTopology.LoopCellRegularThreeComparison.nativeTwoToThreePullbackIso_hom]
  exact AlgebraicTopology.LoopCellRegularThreeComparison.nativeTwoToThreePullback_fst X x P

/-- The same original map X→Z, before the singular functor's composition equality. -/
private def originalSourceIso :
    pullback (twoInclusion X x P) (oldProjection X x P) ≅
      pullback (twoInclusion X x P ≫ threeInclusion X x P) (newProjection X x P) :=
  sourceIso (twoInclusion X x P) (threeInclusion X x P)
    (oldProjection X x P) (newProjection X x P) (oldCoverIso X x P)
    (oldCoverIso_projection X x P)

private theorem originalSourceIso_fst :
    (originalSourceIso X x P).hom ≫
      pullback.fst (twoInclusion X x P ≫ threeInclusion X x P) (newProjection X x P) =
        pullback.fst (twoInclusion X x P) (oldProjection X x P) :=
  sourceIso_fst (twoInclusion X x P) (threeInclusion X x P)
    (oldProjection X x P) (newProjection X x P) (oldCoverIso X x P)
    (oldCoverIso_projection X x P)

private theorem originalSourceIso_snd :
    (originalSourceIso X x P).hom ≫
      pullback.snd (twoInclusion X x P ≫ threeInclusion X x P) (newProjection X x P) =
        pullback.snd (twoInclusion X x P) (oldProjection X x P) ≫
          (oldCoverIso X x P).hom ≫ pullback.snd (threeInclusion X x P) (newProjection X x P) :=
  sourceIso_snd (twoInclusion X x P) (threeInclusion X x P)
    (oldProjection X x P) (newProjection X x P) (oldCoverIso X x P)
    (oldCoverIso_projection X x P)

private abbrev originalInclusion : X ⟶ AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P :=
  LoopCellAttachment.inclusion X x P ≫
    AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The actual singular composition equality names the unchanged
source comparison, with its explicit map-first orientation. -/
private theorem originalInclusion_singular_comp :
    twoInclusion X x P ≫ threeInclusion X x P =
      TopCat.toSSet.map (originalInclusion X x P) :=
  (TopCat.toSSet.map_comp (LoopCellAttachment.inclusion X x P)
    (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P)).symm

/-- The singular composition equality only transports the source object;
no original map or cover coordinate is replaced. -/
private def originalCompositeSourceIso :
    pullback (twoInclusion X x P) (oldProjection X x P) ≅
      pullback (TopCat.toSSet.map (originalInclusion X x P)) (newProjection X x P) :=
  originalSourceIso X x P ≪≫
    eqToIso (congrArg (fun k : TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj
        (AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P) => pullback k (newProjection X x P))
      (originalInclusion_singular_comp X x P))

/-- The source transport retains the original second projection. -/
private theorem pullback_eqToIso_snd {A B Z : SSet.{u}} {f g : A ⟶ Z}
    (p : B ⟶ Z) (h : f = g) :
    (eqToIso (congrArg (fun k => pullback k p) h)).hom ≫ pullback.snd g p = pullback.snd f p := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- The complete original X→Z regular-cover source square is calibrated
by the typed singular composition equality and original pullback law. -/
private theorem originalCompositeSourceIso_projection :
    (originalCompositeSourceIso X x P).hom ≫
      pullback.snd (TopCat.toSSet.map (originalInclusion X x P)) (newProjection X x P) =
        pullback.snd (twoInclusion X x P) (oldProjection X x P) ≫
          (oldCoverIso X x P).hom ≫ pullback.snd (threeInclusion X x P) (newProjection X x P) := by
  let hComp : twoInclusion X x P ≫ threeInclusion X x P =
      TopCat.toSSet.map (originalInclusion X x P) := originalInclusion_singular_comp X x P
  let e : pullback (twoInclusion X x P ≫ threeInclusion X x P) (newProjection X x P) ≅
      pullback (TopCat.toSSet.map (originalInclusion X x P)) (newProjection X x P) :=
    eqToIso (congrArg (fun k => pullback k (newProjection X x P)) hComp)
  have he : e.hom ≫
      pullback.snd (TopCat.toSSet.map (originalInclusion X x P)) (newProjection X x P) =
    pullback.snd (twoInclusion X x P ≫ threeInclusion X x P) (newProjection X x P) :=
    pullback_eqToIso_snd (newProjection X x P) hComp
  change ((originalSourceIso X x P).hom ≫ e.hom) ≫ _ = _
  rw [Category.assoc, he]
  exact originalSourceIso_snd X x P

end Original

end OriginalRegularPlusSourceComparison


namespace OriginalRegularPlusTriple

open OriginalRegularPlusSourceComparison

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
  [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
  [P.Normal] [Group.IsPerfect P]

/-- The actual boundary, on EVERY full original coefficient vector. -/
private theorem boundary_basis_value (v : P →₀ MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)) :
    AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoBoundary X x P
      (AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeLambdaBasisIso X x P v) =
        AlgebraicTopology.LoopCellNativeRelativeBasis.originalRegularLambdaBasisIso X x P v := by
  let := AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeDeckModule X x P
  let := AlgebraicTopology.LoopCellNativeRelativeBasis.originalRegularDeckModule X x P
  let e2 := AlgebraicTopology.LoopCellNativeRelativeBasis.originalRegularLambdaBasisIso X x P
  let e3 := AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeLambdaBasisIso X x P
  have h : e2.symm (AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoLinearMap X x P (e3 v)) = v :=
    (AlgebraicTopology.LoopCellRegularThreeComparison.originalRR3ToRR2Matrix_apply X x P v).symm.trans
      (LinearMap.congr_fun
        (AlgebraicTopology.LoopCellRegularThreeComparison.originalRR3ToRR2Matrix_eq_id X x P) v)
  have hValue : AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoLinearMap X x P (e3 v) = e2 v :=
    (e2.apply_symm_apply _).symm.trans (congrArg e2 h)
  exact (AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoLinearMap_apply X x P _).symm.trans hValue

/-- The full matrix proves bijectivity of the SAME underlying module morphism. -/
private theorem original_boundary_isIso :
    IsIso (AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoBoundary X x P) := by
  let := AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeDeckModule X x P
  let := AlgebraicTopology.LoopCellNativeRelativeBasis.originalRegularDeckModule X x P
  let e2 := AlgebraicTopology.LoopCellNativeRelativeBasis.originalRegularLambdaBasisIso X x P
  let e3 := AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeLambdaBasisIso X x P
  let d := AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoBoundary X x P
  have hValue (a : AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeHomology X x P 3) :
      d a = e2 (e3.symm a) :=
    (congrArg d (e3.apply_symm_apply a)).symm.trans
      (boundary_basis_value X x P (e3.symm a))
  apply (ConcreteCategory.isIso_iff_bijective d).mpr
  change Function.Bijective (fun a : AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeHomology X x P 3 => d a)
  rw [show (fun a : AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeHomology X x P 3 => d a) =
      (fun a => e2 (e3.symm a)) from funext hValue]
  exact e2.bijective.comp e3.symm.bijective


private abbrev coeff : AddCommGrpCat.{u} := singularIntegralCoefficients.{u}
private abbrev chain : SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj coeff
private abbrev pair2 := LoopCellPulledSimplicialModel.nativePair X x P
private abbrev pair3 := AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreePair X x P
private abbrev cartIso := AlgebraicTopology.LoopCellRegularThreeComparison.nativeTwoToThreePullbackIso X x P

/-- The mapped ACTUAL Cartesian Iso is typed on the original pair
carriers. No opaque cover-object identification is needed in subsequent
cancellation, quotient or monicity arguments. -/
private def mappedCartesianChainIso :
    (pair2 X x P).right.chainComplex coeff ≅ (pair3 X x P).left.chainComplex coeff :=
  chain.mapIso (cartIso X x P)

/-- The whole original coefficient/connecting square, not an augmentation, transports δ invertibility. -/
private theorem native_boundary_isIso :
    IsIso (AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary X x P) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let d := AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoBoundary X x P
  let e2 := (AlgebraicTopology.LoopCellNativeRelativeBasis.originalRegularNativeHomologyIso X x P).hom
  let e3 := (AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeNativeHomologyIso X x P 3).hom
  let b := AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary X x P
  let : IsIso d := original_boundary_isIso X x P
  have h : IsIso (e3 ≫ b) := by
    rw [← AlgebraicTopology.LoopCellRegularThreeComparison.originalRegularThreeToTwoBoundary_native]
    infer_instance
  exact (isIso_comp_left_iff e3 b).mp h

/-- The actual old cover inclusion is reindexed by the actual Cartesian Iso. -/
private def fRaw : (pair2 X x P).left.chainComplex coeff ⟶
    (pair3 X x P).left.chainComplex coeff :=
  SSet.chainComplexMap (pair2 X x P).hom coeff ≫ (chain.map (cartIso X x P).hom)

private abbrev gRaw := SSet.chainComplexMap (pair3 X x P).hom coeff

private abbrev rawTriple : ShortComplex (ChainComplex AddCommGrpCat.{u} ℕ) where
  X₁ := cokernel (fRaw X x P)
  X₂ := cokernel (fRaw X x P ≫ gRaw X x P)
  X₃ := cokernel (gRaw X x P)
  f := cokernel.map (fRaw X x P) (fRaw X x P ≫ gRaw X x P)
    (𝟙 _) (gRaw X x P) (by simp)
  g := cokernel.map (fRaw X x P ≫ gRaw X x P) (gRaw X x P)
    (fRaw X x P) (𝟙 _) (by simp)
  zero := ((kernelCokernelCompSequence_exact (fRaw X x P) (gRaw X x P)).sc' 3 4 5).zero

private theorem rawTriple_shortExact : (rawTriple X x P).ShortExact := by
  let f := fRaw X x P
  let g := gRaw X x P
  let h := kernelCokernelCompSequence_exact f g
  let : Mono g := ((pair3 X x P).shortExact_chainComplexShortComplex coeff).mono_f
  have hK : IsZero (kernel g) := (CategoryTheory.Preadditive.mono_iff_isZero_kernel g).mp inferInstance
  have hMono : Mono (h.sc' 3 4 5).f := (h.exact' 2 3 4).mono_g (hK.eq_zero_of_src _)
  have hEpi : Epi (h.sc' 3 4 5).g := by
    change Epi ((kernelCokernelCompSequence f g).map' 4 5)
    infer_instance
  exact ShortComplex.ShortExact.mk' (h.exact' 3 4 5) hMono hEpi

/-- The actual cokernel UP identifies the first term with the SAME original native RR2 pair. -/
private def rawTwoIso : (rawTriple X x P).X₁ ≅ (pair2 X x P).chainComplex coeff := by
  let f := fRaw X x P
  let m : (pair2 X x P).left.chainComplex coeff ⟶
      (pair2 X x P).right.chainComplex coeff :=
    SSet.chainComplexMap (pair2 X x P).hom coeff
  let c : (pair2 X x P).right.chainComplex coeff ≅
      (pair3 X x P).left.chainComplex coeff := mappedCartesianChainIso X x P
  let w := c.symm
  have hf : f = m ≫ c.hom := by rfl
  have ha : (𝟙 _) ≫ m = f ≫ w.hom := by
    rw [Category.id_comp, hf]
    change m = (m ≫ c.hom) ≫ c.inv
    rw [Category.assoc, c.hom_inv_id, Category.comp_id]
  let a : Arrow.mk f ≅ Arrow.mk m := Arrow.isoMk' f m (Iso.refl _) w ha
  exact CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel f)
    ((pair2 X x P).isColimitCokernelCoforkChainComplex coeff) a

private theorem rawTwoIso_projection :
    cokernel.π (fRaw X x P) ≫ (rawTwoIso X x P).hom =
      chain.map (cartIso X x P).inv ≫ (pair2 X x P).chainComplexπ coeff := by
  let f := fRaw X x P
  let m : (pair2 X x P).left.chainComplex coeff ⟶
      (pair2 X x P).right.chainComplex coeff :=
    SSet.chainComplexMap (pair2 X x P).hom coeff
  let c : (pair2 X x P).right.chainComplex coeff ≅
      (pair3 X x P).left.chainComplex coeff := mappedCartesianChainIso X x P
  let w := c.symm
  have hf : f = m ≫ c.hom := by rfl
  have ha : (𝟙 _) ≫ m = f ≫ w.hom := by
    rw [Category.id_comp, hf]
    change m = (m ≫ c.hom) ≫ c.inv
    rw [Category.assoc, c.hom_inv_id, Category.comp_id]
  let a : Arrow.mk f ≅ Arrow.mk m := Arrow.isoMk' f m (Iso.refl _) w ha
  exact CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel f)
    ((pair2 X x P).cokernelCoforkChainComplex coeff) a.hom

/-- The THIRD relative term uses the explicit actual pair cofork and its
existing universal property; the raw third carrier is the literal cokernel. -/
private def rawThreeCofork : CokernelCofork (gRaw X x P) :=
  CokernelCofork.ofπ ((pair3 X x P).chainComplexπ coeff)
    ((pair3 X x P).chainComplex_condition coeff)

private def rawThreeCoforkIsColimit : IsColimit (rawThreeCofork X x P) := by
  exact (pair3 X x P).isColimitCokernelCoforkChainComplex coeff

private def rawThreeIso : (rawTriple X x P).X₃ ≅ (pair3 X x P).chainComplex coeff :=
  (cokernelIsCokernel (gRaw X x P)).coconePointUniqueUpToIso (rawThreeCoforkIsColimit X x P)

private theorem rawThreeIso_projection :
    cokernel.π (gRaw X x P) ≫ (rawThreeIso X x P).hom =
      (pair3 X x P).chainComplexπ coeff := by
  have h := (cokernelIsCokernel (gRaw X x P)).comp_coconePointUniqueUpToIso_hom
    (rawThreeCoforkIsColimit X x P) WalkingParallelPair.one
  exact h

private theorem rawThreeIso_inverse_projection :
    (pair3 X x P).chainComplexπ coeff ≫ (rawThreeIso X x P).inv = cokernel.π (gRaw X x P) := by
  have h := rawThreeIso_projection X x P
  apply (cancel_mono (rawThreeIso X x P).hom).mp
  calc
    ((pair3 X x P).chainComplexπ coeff ≫ (rawThreeIso X x P).inv) ≫
        (rawThreeIso X x P).hom = (pair3 X x P).chainComplexπ coeff := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = cokernel.π (gRaw X x P) ≫ (rawThreeIso X x P).hom := h.symm

private def thirdPairToRawTriple : (pair3 X x P).chainComplexShortComplex coeff ⟶ rawTriple X x P where
  τ₁ := cokernel.π (fRaw X x P)
  τ₂ := cokernel.π (fRaw X x P ≫ gRaw X x P)
  τ₃ := (rawThreeIso X x P).inv
  comm₁₂ := by
    change cokernel.π (fRaw X x P) ≫
        cokernel.map (fRaw X x P) (fRaw X x P ≫ gRaw X x P) (𝟙 _) (gRaw X x P) (by simp) =
      gRaw X x P ≫ cokernel.π (fRaw X x P ≫ gRaw X x P)
    exact cokernel.π_desc _ _ _
  comm₂₃ := by
    change cokernel.π (fRaw X x P ≫ gRaw X x P) ≫
        cokernel.map (fRaw X x P ≫ gRaw X x P) (gRaw X x P) (fRaw X x P) (𝟙 _) (by simp) =
      (pair3 X x P).chainComplexπ coeff ≫ (rawThreeIso X x P).inv
    rw [rawThreeIso_inverse_projection]
    let f := fRaw X x P ≫ gRaw X x P
    let g := gRaw X x P
    have he : cokernel.map f g (fRaw X x P) (𝟙 _) (by simp [f, g]) =
        cokernel.desc f (cokernel.π g) (by
          simp only [f, g, Category.assoc, cokernel.condition, comp_zero]) := by
      unfold cokernel.map
      simp only [Category.id_comp]
    rw [he]
    exact cokernel.π_desc f (cokernel.π g) _

private theorem rawTriple_boundary_recipe :
    HomologicalComplex.homologyMap (rawThreeIso X x P).inv 3 ≫
        (rawTriple_shortExact X x P).δ 3 2 (by simp) =
      ((pair3 X x P).shortExact_chainComplexShortComplex coeff).δ 3 2 (by simp) ≫
        HomologicalComplex.homologyMap (cokernel.π (fRaw X x P)) 2 :=
  (HomologicalComplex.HomologySequence.δ_naturality (thirdPairToRawTriple X x P)
    ((pair3 X x P).shortExact_chainComplexShortComplex coeff)
    (rawTriple_shortExact X x P) 3 2 (by simp)).symm

/-- The original RR2 unit homology Iso is typed in the SAME actual
relative chain-complex homology, so its object is never silently changed. -/
private def rawNativeUnitHomologyIso :
    ((pair2 X x P).chainComplex coeff).homology 2 ≅
      AlgebraicTopology.LoopCellNativeRelativeBasis.nativeHomologyTwo X x P coeff :=
  AlgebraicTopology.LoopCellNativeRelativeBasis.nativeRelativeUnitHomologyIso X x P coeff 2

/-- The native RR2 pair comparison retains the original actual realization unit. -/
private def rawTwoReturnIso : (rawTriple X x P).X₁.homology 2 ≅
    AlgebraicTopology.LoopCellNativeRelativeBasis.nativeHomologyTwo X x P coeff :=
  HomologicalComplex.homologyMapIso (rawTwoIso X x P) 2 ≪≫ rawNativeUnitHomologyIso X x P

/-- The original pair δ, exact quotient square and public native boundary
recipe identify the SAME full map. All objects are explicitly typed in the
actual chain-complex homology category, without foreign functor aliases. -/
private theorem rawTriple_boundary_native :
    HomologicalComplex.homologyMap (rawThreeIso X x P).inv 3 ≫
        (rawTriple_shortExact X x P).δ 3 2 (by simp) ≫ (rawTwoReturnIso X x P).hom =
      AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary X x P := by
  let a : ((pair3 X x P).chainComplex coeff).homology 3 ⟶
      (rawTriple X x P).X₃.homology 3 :=
    HomologicalComplex.homologyMap (rawThreeIso X x P).inv 3
  let δ : (rawTriple X x P).X₃.homology 3 ⟶ (rawTriple X x P).X₁.homology 2 :=
    (rawTriple_shortExact X x P).δ 3 2 (by simp)
  let d : ((pair3 X x P).chainComplex coeff).homology 3 ⟶
      ((pair3 X x P).left.chainComplex coeff).homology 2 :=
    ((pair3 X x P).shortExact_chainComplexShortComplex coeff).δ 3 2 (by simp)
  let q : ((pair3 X x P).left.chainComplex coeff).homology 2 ⟶
      (rawTriple X x P).X₁.homology 2 :=
    HomologicalComplex.homologyMap (cokernel.π (fRaw X x P)) 2
  let e : (rawTriple X x P).X₁.homology 2 ⟶
      ((pair2 X x P).chainComplex coeff).homology 2 :=
    HomologicalComplex.homologyMap (rawTwoIso X x P).hom 2
  let b : ((pair3 X x P).left.chainComplex coeff).homology 2 ⟶
      ((pair2 X x P).right.chainComplex coeff).homology 2 :=
    HomologicalComplex.homologyMap (mappedCartesianChainIso X x P).inv 2
  let p : ((pair2 X x P).right.chainComplex coeff).homology 2 ⟶
      ((pair2 X x P).chainComplex coeff).homology 2 :=
    HomologicalComplex.homologyMap ((pair2 X x P).chainComplexπ coeff) 2
  let u : ((pair2 X x P).chainComplex coeff).homology 2 ⟶
      AlgebraicTopology.LoopCellNativeRelativeBasis.nativeHomologyTwo X x P coeff :=
    (rawNativeUnitHomologyIso X x P).hom
  let r : (rawTriple X x P).X₁.homology 2 ⟶
      AlgebraicTopology.LoopCellNativeRelativeBasis.nativeHomologyTwo X x P coeff :=
    (rawTwoReturnIso X x P).hom
  have hδ : a ≫ δ = d ≫ q := rawTriple_boundary_recipe X x P
  have hr : r = e ≫ u := by rfl
  have hQ : q ≫ e = b ≫ p :=
    (HomologicalComplex.homologyMap_comp _ _ 2).symm.trans
      ((congrArg (fun k => HomologicalComplex.homologyMap k 2)
        (rawTwoIso_projection X x P)).trans
          (HomologicalComplex.homologyMap_comp _ _ 2))
  have hRecipe : AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary X x P =
      d ≫ b ≫ p ≫ u :=
    AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary_recipe X x P
  calc
    _ = a ≫ δ ≫ r := by rfl
    _ = (a ≫ δ) ≫ r := (Category.assoc a δ r).symm
    _ = (d ≫ q) ≫ r := congrArg (fun k => k ≫ r) hδ
    _ = (d ≫ q) ≫ (e ≫ u) := congrArg (fun k => (d ≫ q) ≫ k) hr
    _ = d ≫ ((q ≫ e) ≫ u) :=
      (Category.assoc d q (e ≫ u)).trans
        (congrArg (fun k => d ≫ k) (Category.assoc q e u).symm)
    _ = d ≫ ((b ≫ p) ≫ u) := congrArg (fun k => d ≫ (k ≫ u)) hQ
    _ = d ≫ b ≫ p ≫ u := by simp only [Category.assoc]
    _ = _ := hRecipe.symm

private theorem rawTriple_boundary_isIso : IsIso ((rawTriple_shortExact X x P).δ 3 2 (by simp)) := by
  let a := HomologicalComplex.homologyMap (rawThreeIso X x P).inv 3
  let d := (rawTriple_shortExact X x P).δ 3 2 (by simp)
  let b := (rawTwoReturnIso X x P).hom
  let : IsIso a := inferInstance
  let : IsIso (AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary X x P) :=
    native_boundary_isIso X x P
  have h : IsIso ((a ≫ d) ≫ b) := by
    rw [show (a ≫ d) ≫ b = AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary X x P from
      (Category.assoc a d b).trans (rawTriple_boundary_native X x P)]
    infer_instance
  have h' : IsIso (a ≫ d) := (isIso_comp_right_iff (a ≫ d) b).mp h
  exact (isIso_comp_left_iff a d).mp h'

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] [Group.IsPerfect P] in
/-- The exact classical pair comparison gives vanishing away from degree two. -/
private theorem realized_two_off_diagonal (n : ℕ) (hn : n ≠ 2) :
    IsZero ((relativeSingularHomologyFunctor AddCommGrpCat.{u}
      coeff n).obj
        (LoopCellQuotientCellPresentation.realizedPair X x P)) := by
  let E := SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)
  let a := LoopCellQuotientCellPresentation.attachingCell X x P
  have hz := CellFamilyAttachment.isZero_attachmentRelativeHomology_of_ne
    E 1 a coeff n hn
  let H := relativeSingularHomologyFunctor AddCommGrpCat.{u} coeff n
  exact hz.of_iso (H.mapIso (LoopCellQuotientCellPresentation.classicalPairIso X x P)).symm

omit [Group.IsPerfect P] in
/-- The genuine whole old-space comparison transports every relative degree. -/
private theorem lifted_two_off_diagonal (n : ℕ) (hn : n ≠ 2) :
    IsZero ((relativeSingularHomologyFunctor AddCommGrpCat.{u}
      coeff n).obj (LoopCellSphericalGenerators.liftedPair X x P)) := by
  let c := AlgebraicTopology.LoopCellNativeRelativeBasis.nativeComparisonChainMap X x P
    coeff
  let : QuasiIso c := AlgebraicTopology.LoopCellNativeRelativeBasis.nativeComparisonChainMap_quasiIso
    X x P coeff
  have hc : IsIso (HomologicalComplex.homologyMap c n) :=
    (quasiIsoAt_iff_isIso_homologyMap c n).mp inferInstance
  let e : (relativeSingularHomologyFunctor AddCommGrpCat.{u} coeff n).obj
        (LoopCellQuotientCellPresentation.realizedPair X x P) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} coeff n).obj
        (LoopCellSphericalGenerators.liftedPair X x P) :=
    @asIso _ _ _ _ (HomologicalComplex.homologyMap c n) hc
  exact (realized_two_off_diagonal X x P n hn).of_iso e.symm

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The SAME upstairs three-cell family vanishes outside degree three. -/
private theorem upstairs_three_off_diagonal (n : ℕ) (hn : n ≠ 3) :
    IsZero ((relativeSingularHomologyFunctor AddCommGrpCat.{u} coeff n).obj
      (AlgebraicTopology.LoopCellNativeRelativeBasis.upstairsThreePair X x P)) := by
  exact CellFamilyAttachment.isZero_attachmentRelativeHomology_of_ne
    (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (AlgebraicTopology.LoopCellNativeRelativeBasis.chosenSphericalCopy X x P)
    coeff n hn


omit [Group.IsPerfect P] in
private theorem pair2_off_diagonal (n : ℕ) (hn : n ≠ 2) : IsZero ((pair2 X x P).homology coeff n) :=
  (lifted_two_off_diagonal X x P n hn).of_iso
    (AlgebraicTopology.LoopCellNativeRelativeBasis.nativeRelativeUnitHomologyIso X x P coeff n)

private theorem pair3_off_diagonal (n : ℕ) (hn : n ≠ 3) : IsZero ((pair3 X x P).homology coeff n) :=
  (upstairs_three_off_diagonal X x P n hn).of_iso
    (AlgebraicTopology.LoopCellRegularThreeComparison.relativeThreeHomologyIso X x P coeff n).symm

/-- Every degree of the actual raw middle relative complex vanishes. The
special degrees use the SAME calibrated full original boundary. -/
private theorem raw_middle_relative_isZero (n : ℕ) : IsZero ((rawTriple X x P).X₂.homology n) := by
  let T := rawTriple X x P
  let hT := rawTriple_shortExact X x P
  let d := hT.δ 3 2 (by simp)
  let : IsIso d := rawTriple_boundary_isIso X x P
  have hLeft (k : ℕ) (hk : k ≠ 2) : IsZero (T.X₁.homology k) :=
    (pair2_off_diagonal X x P k hk).of_iso (HomologicalComplex.homologyMapIso (rawTwoIso X x P) k)
  have hRight (k : ℕ) (hk : k ≠ 3) : IsZero (T.X₃.homology k) :=
    (pair3_off_diagonal X x P k hk).of_iso (HomologicalComplex.homologyMapIso (rawThreeIso X x P) k)
  by_cases h2 : n = 2
  · subst n
    have hf : HomologicalComplex.homologyMap T.f 2 = 0 := by
      apply (cancel_epi d).mp
      exact (hT.δ_comp 3 2 (by simp)).trans (comp_zero).symm
    exact (hT.homology_exact₂ 2).isZero_X₂ hf ((hRight 2 (by omega)).eq_zero_of_tgt _)
  · by_cases h3 : n = 3
    · subst n
      have hg : HomologicalComplex.homologyMap T.g 3 = 0 := by
        apply (cancel_mono d).mp
        exact (hT.comp_δ 3 2 (by simp)).trans (zero_comp).symm
      exact (hT.homology_exact₂ 3).isZero_X₂ ((hLeft 3 (by omega)).eq_zero_of_src _) hg
    · exact (hT.homology_exact₂ n).isZero_X₂
        ((hLeft n h2).eq_zero_of_src _) ((hRight n h3).eq_zero_of_tgt _)

private theorem raw_composite_mono : Mono (fRaw X x P ≫ gRaw X x P) := by
  let : Mono (SSet.chainComplexMap (pair2 X x P).hom coeff) :=
    ((pair2 X x P).shortExact_chainComplexShortComplex coeff).mono_f
  let c : (pair2 X x P).right.chainComplex coeff ≅
      (pair3 X x P).left.chainComplex coeff := mappedCartesianChainIso X x P
  let m : (pair2 X x P).left.chainComplex coeff ⟶
      (pair2 X x P).right.chainComplex coeff :=
    SSet.chainComplexMap (pair2 X x P).hom coeff
  have hMap : fRaw X x P = m ≫ c.hom := by rfl
  let : Mono m := ((pair2 X x P).shortExact_chainComplexShortComplex coeff).mono_f
  let : Mono (fRaw X x P) := by
    rw [hMap]
    infer_instance
  let : Mono (gRaw X x P) := ((pair3 X x P).shortExact_chainComplexShortComplex coeff).mono_f
  infer_instance

/-- The actual raw composite cover map has every integral homology map invertible. -/
private theorem raw_composite_homology_isIso (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (fRaw X x P ≫ gRaw X x P) n) := by
  let f := fRaw X x P ≫ gRaw X x P
  let : Mono f := raw_composite_mono X x P
  let : Mono (Arrow.mk f).hom := by change Mono f; infer_instance
  let S := ShortComplex.cokernelSequence f
  let hS : S.ShortExact := ShortComplex.cokernelSequence_shortExact (Arrow.mk f)
  have hz (k : ℕ) : IsZero (S.X₃.homology k) := raw_middle_relative_isZero X x P k
  let : Mono (HomologicalComplex.homologyMap f n) :=
    (hS.homology_exact₁ (n + 1) n (by simp)).mono_g ((hz (n + 1)).eq_zero_of_src _)
  let : Epi (HomologicalComplex.homologyMap f n) :=
    (hS.homology_exact₂ n).epi_f ((hz n).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap f n)

private abbrev qComposite : (pair2 X x P).left ⟶ (pair3 X x P).right :=
  (pair2 X x P).hom ≫ (cartIso X x P).hom ≫ (pair3 X x P).hom

/-- The chain functor applies to the SAME whole cover-map composition. -/
private theorem qComposite_homology_isIso (n : ℕ) : IsIso (SSet.homologyMap (qComposite X x P) coeff n) := by
  let C := chain
  have hMap : C.map (qComposite X x P) = fRaw X x P ≫ gRaw X x P := by
    calc
      C.map (qComposite X x P) = C.map (pair2 X x P).hom ≫
          C.map ((cartIso X x P).hom ≫ (pair3 X x P).hom) :=
        C.map_comp (pair2 X x P).hom ((cartIso X x P).hom ≫ (pair3 X x P).hom)
      _ = C.map (pair2 X x P).hom ≫
          (C.map (cartIso X x P).hom ≫ C.map (pair3 X x P).hom) :=
        congrArg (fun k => C.map (pair2 X x P).hom ≫ k)
          (C.map_comp (cartIso X x P).hom (pair3 X x P).hom)
      _ = fRaw X x P ≫ gRaw X x P := by
        rw [← Category.assoc]
        rfl
  let : IsIso (HomologicalComplex.homologyMap (fRaw X x P ≫ gRaw X x P) n) := raw_composite_homology_isIso X x P n
  change IsIso (HomologicalComplex.homologyMap (C.map (qComposite X x P)) n)
  rw [hMap]
  infer_instance

/-- The actual source Iso and its WHOLE projection square identify the
composite homology map with the literal original X→Z regular projection. -/
private theorem original_raw_regular_projection_homology_isIso (n : ℕ) :
    IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map (originalInclusion X x P)) (newProjection X x P)) coeff n) := by
  let k := originalCompositeSourceIso X x P
  let q := pullback.snd (TopCat.toSSet.map (originalInclusion X x P)) (newProjection X x P)
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} := SSet.homologyFunctor coeff n
  have hq : k.hom ≫ q = qComposite X x P := originalCompositeSourceIso_projection X x P
  let : IsIso (H.map k.hom) := inferInstance
  have hQC : IsIso (H.map (qComposite X x P)) := by
    change IsIso (SSet.homologyMap (qComposite X x P) coeff n)
    exact qComposite_homology_isIso X x P n
  have hMap : H.map k.hom ≫ H.map q = H.map (qComposite X x P) :=
    (H.map_comp k.hom q).symm.trans (congrArg H.map hq)
  have h : IsIso (H.map k.hom ≫ H.map q) := by
    rw [hMap]
    exact hQC
  exact (isIso_comp_left_iff (H.map k.hom) (H.map q)).mp h

/-- The exact original point equation transports the predicate on the SAME
projection, without resetting any native path or cover choice. -/
private theorem original_regular_projection_homology_isIso (n : ℕ) :
    IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map (originalInclusion X x P))
        (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P))
          (TopCat.toSSetObj₀Equiv.symm
            (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P)))) coeff n) := by
  let F : (TopCat.toSSet.obj (AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P)) _⦋0⦌ → Prop :=
    fun z => IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map (originalInclusion X x P))
        (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P)) z)) coeff n)
  have hRaw : F (AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreePoint X x P) :=
    original_raw_regular_projection_homology_isIso X x P n
  exact Eq.mp (congrArg F (AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreePoint_eq_original X x P)) hRaw

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- Path connectedness belongs to the computed cell spaces. -/
private theorem original_three_pathConnected : PathConnectedSpace
    (AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P) := by
  let : PathConnectedSpace (LoopCellAttachment.space X x P) :=
    CellFamilyAttachment.pathConnectedSpace X 1 (LoopCellAttachment.attachingMap X x P)
  exact CellFamilyAttachment.pathConnectedSpace (LoopCellAttachment.space X x P) 2
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- All target local systems now follow from the ACTUAL original regular
projection maps, using the accepted same-map ending-fiber/stalk theorem. -/
private theorem original_plus_localCoefficientHomologyEquivalence :
    TopCat.IsLocalCoefficientHomologyEquivalence (originalInclusion X x P) := by
  let := original_three_pathConnected X x P
  exact TopCat.localCoefficientHomologyEquivalence_of_regularCoverHomology
    (originalInclusion X x P)
    (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P)
    (original_regular_projection_homology_isIso X x P)

/-- Canonical reduced acyclicity holds for EVERY point of the SAME original
three-cell space. No acyclicity, local-system equivalence or fiber model was input. -/
private theorem original_plus_isAcyclicMapAt_all :
    ∀ z : AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P,
      TopCat.IsAcyclicMapAt (originalInclusion X x P) z := by
  intro z
  exact TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence (originalInclusion X x P)
    (original_plus_localCoefficientHomologyEquivalence X x P) z


/-- The actual higher-cell groupoid equivalence yields bijectivity of the
ACTUAL ordinary fundamental-group map, through its existing singular square. -/
private theorem original_three_pi1Map_bijective :
    Function.Bijective (FundamentalGroup.mapOfEq
      (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P).hom rfl
      (x := LoopCellAttachment.inclusion X x P x)) := by
  let Y := LoopCellAttachment.space X x P
  let Z := AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P
  let f := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let y := LoopCellAttachment.inclusion X x P x
  let q := TopCat.toSSet.map f
  let F := SSet.mapFundamentalGroupoid q
  let : F.IsEquivalence := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusionFundamentalGroupoid_isEquivalence X x P
  let a := SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y)
  let c := TopCat.singularMappedVertexIso f y
  let eF : End a ≃ End (F.obj a) :=
    End.homEquiv.trans
      (((Functor.FullyFaithful.ofFullyFaithful F).homEquiv (X := a) (Y := a)).trans
        End.homEquiv.symm)
  let ec : End (F.obj a) ≃ End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f y))) :=
    End.homEquiv.trans ((Iso.homCongr c c).trans End.homEquiv.symm)
  let eY := TopCat.singularFundamentalGroupoidEndMulEquiv Y y
  let eZ := TopCat.singularFundamentalGroupoidEndMulEquiv Z (f y)
  let e := eY.symm.toEquiv.trans ((eF.trans ec).trans eZ.toEquiv)
  have hNative (z : End a) :
      SSet.basedFundamentalGroupHom q (TopCat.toSSetObj₀Equiv.symm y)
        (TopCat.toSSetObj₀Equiv.symm (f y)) c z = ec (eF z) := by
    rw [SSet.basedFundamentalGroupHom_apply]
    rfl
  have hValue (z : FundamentalGroup Y y) :
      FundamentalGroup.mapOfEq f.hom rfl z = e z := by
    apply eZ.symm.injective
    rw [show e z = eZ (ec (eF (eY.symm z))) from rfl, eZ.symm_apply_apply]
    have h := TopCat.singularEnd_inverse_naturality f y z
    change eZ.symm (FundamentalGroup.mapOfEq f.hom rfl z) = ec (eF (eY.symm z))
    exact h.trans (hNative (eY.symm z))
  change Function.Bijective (fun z : FundamentalGroup Y y => FundamentalGroup.mapOfEq f.hom rfl z)
  rw [show (fun z : FundamentalGroup Y y => FundamentalGroup.mapOfEq f.hom rfl z) = e from funext hValue]
  exact e.bijective

/-- The zero point equality does not replace the actual induced map. -/
private theorem pi1Map_comp {A B D : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ D) (a : A) :
    FundamentalGroup.mapOfEq (f ≫ g).hom (rfl : (f ≫ g).hom a = (f ≫ g) a) =
      (FundamentalGroup.mapOfEq g.hom (rfl : g.hom (f a) = g (f a))).comp
        (FundamentalGroup.mapOfEq f.hom (rfl : f.hom a = f a)) := by
  apply MonoidHom.ext
  intro z
  simp only [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, TopCat.hom_comp]
  exact congrArg End.of (Path.Homotopic.Quotient.map_comp (p := z.asHom) (f := f.hom) (g := g.hom))

/-- The literal original two/three-cell composite is surjective on
its actual ordinary fundamental group: the first inclusion is surjective
and the same second inclusion is bijective. -/
private theorem original_plus_pi1Map_surjective :
    Function.Surjective (FundamentalGroup.mapOfEq (originalInclusion X x P).hom
      (rfl : (originalInclusion X x P).hom x =
        AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P)) := by
  let i₂ := LoopCellAttachment.inclusion X x P
  let i₃ := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let m₂ := FundamentalGroup.mapOfEq i₂.hom (rfl : i₂.hom x = i₂ x)
  let m₃ := FundamentalGroup.mapOfEq i₃.hom
    (rfl : i₃.hom (i₂ x) = i₃ (i₂ x))
  have h₂ : Function.Surjective m₂ := LoopCellAttachment.pi1Map_surjective X x P
  have h₃ : Function.Surjective m₃ := (original_three_pi1Map_bijective X x P).2
  have hcomp : FundamentalGroup.mapOfEq (originalInclusion X x P).hom rfl =
      m₃.comp m₂ := pi1Map_comp i₂ i₃ x
  rw [hcomp]
  exact h₃.comp h₂

/-- The SAME full original composite has kernel exactly the prescribed normal subgroup. -/
private theorem original_plus_kernel_eq :
    MonoidHom.ker (FundamentalGroup.mapOfEq (originalInclusion X x P).hom
      (rfl : (originalInclusion X x P).hom x =
        AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P)) = P := by
  let i2 := LoopCellAttachment.inclusion X x P
  let i3 := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let m2 := FundamentalGroup.mapOfEq i2.hom (rfl : i2.hom x = i2 x)
  let m3 := FundamentalGroup.mapOfEq i3.hom (rfl : i3.hom (i2 x) = i3 (i2 x))
  have h3 : Function.Injective m3 := (original_three_pi1Map_bijective X x P).1
  have h2 : MonoidHom.ker m2 = P := by
    change MonoidHom.ker (LoopCellAttachment.pi1Map X x P) = P
    exact CellQuotientVanKampen.ker_pi1Map X x P
  rw [show FundamentalGroup.mapOfEq (originalInclusion X x P).hom rfl = m3.comp m2 from
    pi1Map_comp i2 i3 x]
  ext z
  change m3 (m2 z) = 1 ↔ z ∈ P
  have hEq : m3 (m2 z) = 1 ↔ m2 z = 1 :=
    ⟨fun h => h3 (h.trans m3.map_one.symm), fun h => h ▸ m3.map_one⟩
  rw [hEq]
  change z ∈ MonoidHom.ker m2 ↔ z ∈ P
  rw [h2]

/-- This is the constructed actual two/three-cell plus map, with no plus,
acyclicity, kernel, matrix or coherent cover witness supplied by the caller. -/
private theorem original_cell_plusConstructionAt :
    TopCat.IsPlusConstructionAt (originalInclusion X x P) x
      (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P) rfl P where
  acyclic := original_plus_isAcyclicMapAt_all X x P _
  kernel_eq := original_plus_kernel_eq X x P


private abbrev finalModel := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeModel X x P

private abbrev finalModelComparison : SSet.toTop.obj (finalModel X x P) ⟶
    AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P :=
  CellFamilySimplicialModel.realizationMap (LoopCellAttachment.space X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- Cofibrancy of the ACTUAL two/three-cell space and its actual CW realization
model is derived, so the genuine target CW type is not a caller-supplied witness. -/
private def finalModelHomotopyEquiv : SSet.toTop.obj (finalModel X x P) ≃ₕ
    AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P := by
  let Y := LoopCellAttachment.space X x P
  let Z := AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P
  let K := finalModel X x P
  let m := finalModelComparison X x P
  letI : IsCofibrant Y := AlgebraicTopology.LoopCellRegularThreeComparison.originalTwo_isCofibrant X x P
  letI : IsCofibrant Z := CellFamilySimplicialModel.isCofibrant_attachment Y 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)
  letI : IsCofibrant (SSet.toTop.obj K) := SSet.RealizationCWUpgrade.realization_isCofibrant K
  have hm : TopCat.weakHomotopyEquivalences m :=
    CellFamilySimplicialModel.realizationMap_weak Y 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)
  exact (TopCat.cofibrantWeakHomotopyEquiv (SSet.toTop.obj K) Z m hm).val

private theorem finalModelHomotopyEquiv_toFun :
    (finalModelHomotopyEquiv X x P).toFun = (finalModelComparison X x P).hom := by
  let Y := LoopCellAttachment.space X x P
  let Z := AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P
  let K := finalModel X x P
  let m := finalModelComparison X x P
  let : IsCofibrant Y := AlgebraicTopology.LoopCellRegularThreeComparison.originalTwo_isCofibrant X x P
  let : IsCofibrant Z := CellFamilySimplicialModel.isCofibrant_attachment Y 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)
  let : IsCofibrant (SSet.toTop.obj K) := SSet.RealizationCWUpgrade.realization_isCofibrant K
  have hm : TopCat.weakHomotopyEquivalences m :=
    CellFamilySimplicialModel.realizationMap_weak Y 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)
  exact TopCat.cofibrantWeakHomotopyEquiv_toFun (SSet.toTop.obj K) Z m hm

/-- The returned original plus target has a constructed genuine unbased CW model. -/
private theorem original_three_genuine_CWType :
    ∃ C : TopCat.{u}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (C ≃ₕ AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P) := by
  let K := finalModel X x P
  let C := SSet.toTop.obj K
  let : T2Space C := SSet.realization_t2Space K
  let : Topology.CWComplex (Set.univ : Set C) := inferInstance
  exact ⟨C, inferInstance, inferInstance, ⟨finalModelHomotopyEquiv X x P⟩⟩

/-- Both actual inverse homotopies belong to the returned model equivalence;
the forward comparison is the original map, not merely homotopic to it. -/
private theorem finalModel_actual_inverse :
    ∃ g : AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P ⟶
        SSet.toTop.obj (finalModel X x P),
      Nonempty (TopCat.Homotopy (finalModelComparison X x P ≫ g) (𝟙 _)) ∧
      Nonempty (TopCat.Homotopy (g ≫ finalModelComparison X x P) (𝟙 _)) := by
  let e := finalModelHomotopyEquiv X x P
  let f := finalModelComparison X x P
  let g := TopCat.ofHom e.invFun
  have hf : e.toFun = f.hom := finalModelHomotopyEquiv_toFun X x P
  have hL : e.invFun.comp e.toFun = (f ≫ g).hom := by
    rw [TopCat.hom_comp, TopCat.hom_ofHom, ← hf]
  have hR : e.toFun.comp e.invFun = (g ≫ f).hom := by
    rw [TopCat.hom_comp, TopCat.hom_ofHom, ← hf]
  exact ⟨g, ⟨e.left_inv.some.cast hL (TopCat.hom_id (X := SSet.toTop.obj (finalModel X x P))).symm⟩,
    ⟨e.right_inv.some.cast hR (TopCat.hom_id (X := AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P)).symm⟩⟩

/-- Complete actual cell-construction output, including genuine target CW type. -/
private theorem original_cell_plus_construction :
    TopCat.IsPlusConstructionAt (originalInclusion X x P) x
        (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P) rfl P ∧
      (∀ z : AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P,
        TopCat.IsAcyclicMapAt (originalInclusion X x P) z) ∧
      (∃ C : TopCat.{u}, ∃ _ : T2Space C,
        ∃ _ : Topology.CWComplex (Set.univ : Set C),
          Nonempty (C ≃ₕ AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P)) :=
  ⟨original_cell_plusConstructionAt X x P, original_plus_isAcyclicMapAt_all X x P,
    original_three_genuine_CWType X x P⟩


end OriginalRegularPlusTriple

namespace AlgebraicTopology.LoopCellIndependentPlus

/-- The actual original two/three-cell plus construction requires only
connectedness of the given Hausdorff classical CW source. Path connectedness
is derived by the canonical CW-type theorem, and the actual map, point,
every fiber, exact kernel and genuine target CW model are retained. -/
public theorem original_connected_CW_plus_construction
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    TopCat.IsPlusConstructionAt i x
        (LoopCellRegularThreeComparison.originalThreeBasePoint X x P) rfl P ∧
      (∀ z : LoopCellRegularThreeComparison.originalThree X x P,
        TopCat.IsAcyclicMapAt i z) ∧
      (∃ C : TopCat.{u}, ∃ _ : T2Space C,
        ∃ _ : Topology.CWComplex (Set.univ : Set C),
          Nonempty (C ≃ₕ LoopCellRegularThreeComparison.originalThree X x P)) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  exact OriginalRegularPlusTriple.original_cell_plus_construction X x P


/-- Complete output of the SAME independently constructed cell map.
All target local systems, every ending fiber, the exact kernel, surjective
fundamental-group map, connected target, whole relative/regular cover homology, and the actual CW-model
forward map with BOTH ordinary inverse families are retained. No plus,
acyclicity, homology, kernel, model or inverse witness is supplied. -/
public theorem original_connected_CW_plus_construction_full
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let Z := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let y := LoopCellRegularThreeComparison.originalThreeBasePoint X x P
    let R : AddCommGrpCat.{u} := singularIntegralCoefficients.{u}
    let F := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
    let A := LoopCellPulledSimplicialModel.nativePair X x P
    let B := LoopCellRegularThreeComparison.nativeThreePair X x P
    let f := SSet.chainComplexMap A.hom R ≫
      F.map (LoopCellRegularThreeComparison.nativeTwoToThreePullbackIso X x P).hom
    let g := SSet.chainComplexMap B.hom R
    let K := LoopCellRegularThreeComparison.originalThreeModel X x P
    let c := CellFamilySimplicialModel.realizationMap (LoopCellAttachment.space X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)
    TopCat.IsPlusConstructionAt i x y rfl P ∧
      TopCat.IsLocalCoefficientHomologyEquivalence i ∧
      (∀ z : Z, TopCat.IsAcyclicMapAt i z) ∧
      MonoidHom.ker (FundamentalGroup.mapOfEq i.hom (rfl : i.hom x = y)) = P ∧
      Function.Surjective (FundamentalGroup.mapOfEq i.hom (rfl : i.hom x = y)) ∧
      PathConnectedSpace Z ∧
      (∀ n : ℕ, IsZero ((cokernel (f ≫ g)).homology n)) ∧
      (∀ n : ℕ, IsIso (SSet.homologyMap
        (pullback.snd (TopCat.toSSet.map i)
          (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Z)
            (TopCat.toSSetObj₀Equiv.symm y))) R n)) ∧
      (∃ _ : T2Space (SSet.toTop.obj K),
        ∃ _ : Topology.CWComplex (Set.univ : Set (SSet.toTop.obj K)),
          ∃ e : SSet.toTop.obj K ≃ₕ Z, e.toFun = c.hom ∧
            ∃ r : Z ⟶ SSet.toTop.obj K,
              Nonempty (TopCat.Homotopy (c ≫ r) (𝟙 _)) ∧
                Nonempty (TopCat.Homotopy (r ≫ c) (𝟙 _))) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  refine ⟨OriginalRegularPlusTriple.original_cell_plusConstructionAt X x P,
    OriginalRegularPlusTriple.original_plus_localCoefficientHomologyEquivalence X x P,
    OriginalRegularPlusTriple.original_plus_isAcyclicMapAt_all X x P,
    OriginalRegularPlusTriple.original_plus_kernel_eq X x P,
    OriginalRegularPlusTriple.original_plus_pi1Map_surjective X x P,
    OriginalRegularPlusTriple.original_three_pathConnected X x P, ?_, ?_, ?_⟩
  · intro n
    exact OriginalRegularPlusTriple.raw_middle_relative_isZero X x P n
  · intro n
    exact OriginalRegularPlusTriple.original_regular_projection_homology_isIso X x P n
  · let K := LoopCellRegularThreeComparison.originalThreeModel X x P
    let : T2Space (SSet.toTop.obj K) := SSet.realization_t2Space K
    let : Topology.CWComplex (Set.univ : Set (SSet.toTop.obj K)) := inferInstance
    exact ⟨inferInstance, inferInstance,
      OriginalRegularPlusTriple.finalModelHomotopyEquiv X x P,
      OriginalRegularPlusTriple.finalModelHomotopyEquiv_toFun X x P,
      OriginalRegularPlusTriple.finalModel_actual_inverse X x P⟩

end AlgebraicTopology.LoopCellIndependentPlus


end
