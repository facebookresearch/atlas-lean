/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingOperatorEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.TriangleShearFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.TriangleTargetShearFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.TriangleTargetReedyFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ScalarFibreWeakDetection

/-!
# Both original decorated outer two-horn restrictions

The selected adjacent edge is an intrinsic equivalence. Both global horn
restrictions use the original full mapping end and actual native pullbacks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.DecoratedOuterTwoHorn
open SegalHomotopy

/-- The original edge01 in the source outer horn. -/
def firstEdge : (Δ[1] : SSet.{u}) ⟶ (Λ[2, 0] : SSet.{u}) :=
  SSet.Rezk.outerHornRightIso.hom ≫ SSet.Rezk.outerHornRight

/-- The original edge12 in the target outer horn. -/
def lastEdge : (Δ[1] : SSet.{u}) ⟶ (Λ[2, 2] : SSet.{u}) :=
  SSet.Rezk.outerHornTargetRightIso.hom ≫ SSet.Rezk.outerHornTargetRight

/-- The source horn retains its literal first01 edge. -/
@[reassoc (attr := simp)]
theorem firstEdge_ι : firstEdge.{u} ≫ (SSet.horn 2 0).ι = SSet.stdSimplex.δ (2 : Fin 3) := by
  simp only [firstEdge, Category.assoc, SSet.Rezk.outerHornRight_ι,
    SSet.Rezk.outerHornRightIso_ι]

/-- The target horn retains its literal last12 edge. -/
@[reassoc (attr := simp)]
theorem lastEdge_ι : lastEdge.{u} ≫ (SSet.horn 2 2).ι = SSet.stdSimplex.δ (0 : Fin 3) := by
  exact SSet.Rezk.outerHornTargetRightIso_inclusion

/-- The actual source-horn mapping subcomplex selected by its first edge. -/
def firstTarget (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    ((discreteSourceMapping W).obj (op (Λ[2, 0] : SSet.{u}))).Subcomplex :=
  (EquivalenceMapping.subcomplex W hW Δ[1]).preimage
    ((discreteSourceMapping W).map firstEdge.op)

/-- The literal selected first-edge source of the actual restriction. -/
def firstSource (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    ((discreteSourceMapping W).obj (op (Δ[2] : SSet.{u}))).Subcomplex :=
  (firstTarget W hW).preimage ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op)

/-- The actual target-horn mapping subcomplex selected by its last edge. -/
def lastTarget (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    ((discreteSourceMapping W).obj (op (Λ[2, 2] : SSet.{u}))).Subcomplex :=
  (EquivalenceMapping.subcomplex W hW Δ[1]).preimage
    ((discreteSourceMapping W).map lastEdge.op)

/-- The literal selected last-edge source of the actual restriction. -/
def lastSource (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    ((discreteSourceMapping W).obj (op (Δ[2] : SSet.{u}))).Subcomplex :=
  (lastTarget W hW).preimage ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op)

/-- The canonical original selected first-edge restriction. -/
def firstRestriction (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (firstSource W hW : SSet.{u}) ⟶ (firstTarget W hW : SSet.{u}) :=
  (firstTarget W hW).fromPreimage ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op)

/-- The canonical original selected last-edge restriction. -/
def lastRestriction (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (lastSource W hW : SSet.{u}) ⟶ (lastTarget W hW : SSet.{u}) :=
  (lastTarget W hW).fromPreimage ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op)

/-- The first selected restriction keeps both original inclusion legs. -/
@[reassoc (attr := simp)]
theorem firstRestriction_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    firstRestriction W hW ≫ (firstTarget W hW).ι =
      (firstSource W hW).ι ≫ (discreteSourceMapping W).map (SSet.horn 2 0).ι.op :=
  SSet.Subcomplex.fromPreimage_ι _ _

/-- The last selected restriction keeps both original inclusion legs. -/
@[reassoc (attr := simp)]
theorem lastRestriction_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    lastRestriction W hW ≫ (lastTarget W hW).ι =
      (lastSource W hW).ι ≫ (discreteSourceMapping W).map (SSet.horn 2 2).ι.op :=
  SSet.Subcomplex.fromPreimage_ι _ _

private def firstPair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    mappingFibre W y z ⟶ mappingFibre W x y ⨯ mappingFibre W y z :=
  prod.lift (mappingFibre.snd W y z ≫ SSet.yonedaEquiv.symm a) (𝟙 _)

private abbrev firstFixed (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) : SSet.{u} :=
  pullback (triangleComparison W x y z) (firstPair W x y z a)

private abbrev firstP (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstFixed W x y z a ⟶ triangleSpace W x y z := pullback.fst _ _

private abbrev firstQ (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstFixed W x y z a ⟶ mappingFibre W y z := pullback.snd _ _

private def firstM (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstFixed W x y z a ⟶ mappingFibre W x z :=
  firstP W x y z a ≫ triangleMiddle W x y z

private theorem firstQ_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    trivialFibrations SSet.{u} (firstQ W x y z a) :=
  (trivialFibrations SSet.{u}).of_isPullback
    (IsPullback.of_hasPullback (triangleComparison W x y z) (firstPair W x y z a))
    (triangleComparison_trivialFibration W hW x y z)

private def firstSection (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    mappingFibre W y z ⟶ firstFixed W x y z a :=
  pullback.lift (firstPair W x y z a ≫ mappingCompositionSection W hW x y z) (𝟙 _)
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id,
        Category.id_comp])

private theorem firstSection_Q (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstSection W hW x y z a ≫ firstQ W x y z a = 𝟙 _ := pullback.lift_snd _ _ _

private theorem firstSection_M (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstSection W hW x y z a ≫ firstM W x y z a = mappingPrecomposition W hW x y z a := by
  dsimp only [firstSection, firstM]
  rw [← Category.assoc, pullback.lift_fst]
  rfl

private theorem firstM_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a)) :
    SSet.realizationWeakEquivalences (firstM W x y z a) := by
  have hq : SSet.realizationWeakEquivalences (firstQ W x y z a) :=
    (firstQ_trivialFibration W hW x y z a).2
  have hs : SSet.realizationWeakEquivalences (firstSection W hW x y z a) := by
    apply SSet.realizationWeakEquivalences.of_postcomp (firstSection W hW x y z a)
      (firstQ W x y z a) hq
    rw [firstSection_Q]
    exact SSet.realizationWeakEquivalences.id_mem _
  apply SSet.realizationWeakEquivalences.of_precomp (firstSection W hW x y z a)
    (firstM W x y z a) hs
  rw [firstSection_M]
  exact mappingPrecomposition_realizationWeakEquivalence W hW x y a ha z

private def firstBase (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    mappingFibre W x z ⟶ mappingFibre W x z ⨯ mappingFibre W x y :=
  prod.lift (𝟙 _) (mappingFibre.snd W x z ≫ SSet.yonedaEquiv.symm a)

private theorem firstQ_eq (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstQ W x y z a = firstP W x y z a ≫ triangleComparison W x y z ≫ prod.snd := by
  dsimp only [firstQ, firstP, firstFixed, firstPair]
  have h := congrArg (fun f => f ≫ prod.snd)
    (pullback.condition (f := triangleComparison W x y z) (g := firstPair W x y z a))
  simpa only [Category.assoc, firstPair, prod.lift_snd, Category.comp_id] using h.symm

private theorem firstM_square (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    firstP W x y z a ≫ triangleShear W x y z = firstM W x y z a ≫ firstBase W x y z a := by
  apply prod.hom_ext
  · simp only [Category.assoc, triangleShear_middle, firstBase, prod.lift_fst,
      Category.comp_id, firstM]
  · have h := congrArg (fun f => f ≫ prod.fst)
      (pullback.condition (f := triangleComparison W x y z) (g := firstPair W x y z a))
    have hp : firstQ W x y z a ≫ mappingFibre.snd W y z =
        firstM W x y z a ≫ mappingFibre.snd W x z := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have h₁ : firstP W x y z a ≫ triangleComparison W x y z ≫ prod.fst =
        firstQ W x y z a ≫ mappingFibre.snd W y z ≫ SSet.yonedaEquiv.symm a := by
      dsimp only [firstFixed, firstP, firstQ, firstPair]
      simpa only [Category.assoc, firstPair, prod.lift_fst] using h
    calc
      _ = firstP W x y z a ≫ triangleComparison W x y z ≫ prod.fst := by
        rw [Category.assoc, triangleShear_first]
      _ = _ := h₁
      _ = firstM W x y z a ≫ mappingFibre.snd W x z ≫ SSet.yonedaEquiv.symm a := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ SSet.yonedaEquiv.symm a) hp
      _ = _ := by simp only [Category.assoc, firstBase, prod.lift_snd]

private theorem firstM_isPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    IsPullback (firstP W x y z a) (firstM W x y z a)
      (triangleShear W x y z) (firstBase W x y z a) := by
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux'
    (PullbackCone.mk _ _ (firstM_square W x y z a)) (fun s => ?_))
  have he : s.fst ≫ triangleComparison W x y z =
      (s.fst ≫ triangleComparison W x y z ≫ prod.snd) ≫ firstPair W x y z a := by
    apply prod.hom_ext
    · have h := congrArg (fun f => f ≫ prod.snd) s.condition
      have hp : s.snd ≫ mappingFibre.snd W x z =
          s.fst ≫ triangleComparison W x y z ≫ prod.snd ≫ mappingFibre.snd W y z :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      have h₁ : s.fst ≫ triangleComparison W x y z ≫ prod.fst =
          s.snd ≫ mappingFibre.snd W x z ≫ SSet.yonedaEquiv.symm a := by
        simpa only [Category.assoc, triangleShear_first, firstBase, prod.lift_snd] using h
      calc
        _ = _ := h₁
        _ = s.fst ≫ triangleComparison W x y z ≫ prod.snd ≫
            mappingFibre.snd W y z ≫ SSet.yonedaEquiv.symm a := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ SSet.yonedaEquiv.symm a) hp
        _ = _ := by simp only [Category.assoc, firstPair, prod.lift_fst]
    · simp only [Category.assoc, firstPair, prod.lift_snd, Category.comp_id]
  let l := pullback.lift s.fst (s.fst ≫ triangleComparison W x y z ≫ prod.snd) he
  refine ⟨l, pullback.lift_fst _ _ _, ?_, ?_⟩
  · change l ≫ firstM W x y z a = s.snd
    have hl : l ≫ firstP W x y z a = s.fst := pullback.lift_fst _ _ _
    have h := congrArg (fun f => f ≫ prod.fst) s.condition
    have hm : s.fst ≫ triangleMiddle W x y z = s.snd := by
      simpa only [Category.assoc, triangleShear_middle, firstBase, prod.lift_fst,
        Category.comp_id] using h
    change (l ≫ firstP W x y z a) ≫ triangleMiddle W x y z = s.snd
    rw [hl]
    exact hm
  · intro m hm _
    change m ≫ firstP W x y z a = s.fst at hm
    apply pullback.hom_ext (f := triangleComparison W x y z) (g := firstPair W x y z a)
    · exact hm.trans (pullback.lift_fst _ _ _).symm
    · change m ≫ firstQ W x y z a = l ≫ firstQ W x y z a
      calc
        _ = m ≫ firstP W x y z a ≫ triangleComparison W x y z ≫ prod.snd := by rw [firstQ_eq]
        _ = s.fst ≫ triangleComparison W x y z ≫ prod.snd := by rw [← Category.assoc, hm]
        _ = _ := (pullback.lift_snd _ _ _).symm

private theorem firstM_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    Fibration (firstM W x y z a) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hf := ReedyModel.triangleShear_fibration W x y z hW.1
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    ((fibrations SSet.{u}).of_isPullback (firstM_isPullback W x y z a)
      ((HomotopicalAlgebra.fibration_iff _).mp hf))

private theorem firstM_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a)) :
    trivialFibrations SSet.{u} (firstM W x y z a) :=
  ⟨(HomotopicalAlgebra.fibration_iff _).mp (firstM_fibration W hW x y z a),
    firstM_weak W hW x y z a ha⟩

private def lastPair (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    mappingFibre W x y ⟶ mappingFibre W x y ⨯ mappingFibre W y z :=
  prod.lift (𝟙 _) (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm a)

private abbrev lastFixed (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) : SSet.{u} :=
  pullback (triangleComparison W x y z) (lastPair W x y z a)

private abbrev lastP (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastFixed W x y z a ⟶ triangleSpace W x y z := pullback.fst _ _

private abbrev lastQ (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastFixed W x y z a ⟶ mappingFibre W x y := pullback.snd _ _

private def lastM (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastFixed W x y z a ⟶ mappingFibre W x z := lastP W x y z a ≫ triangleMiddle W x y z

private theorem lastQ_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    trivialFibrations SSet.{u} (lastQ W x y z a) :=
  (trivialFibrations SSet.{u}).of_isPullback
    (IsPullback.of_hasPullback (triangleComparison W x y z) (lastPair W x y z a))
    (triangleComparison_trivialFibration W hW x y z)

private def lastSection (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    mappingFibre W x y ⟶ lastFixed W x y z a :=
  pullback.lift (lastPair W x y z a ≫ mappingCompositionSection W hW x y z) (𝟙 _)
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id,
        Category.id_comp])

private theorem lastSection_Q (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastSection W hW x y z a ≫ lastQ W x y z a = 𝟙 _ := pullback.lift_snd _ _ _

private theorem lastSection_M (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastSection W hW x y z a ≫ lastM W x y z a = mappingPostcomposition W hW x y z a := by
  dsimp only [lastSection, lastM]
  rw [← Category.assoc, pullback.lift_fst]
  rfl

private theorem lastM_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W y z).app (op ⦋0⦌) a)) :
    SSet.realizationWeakEquivalences (lastM W x y z a) := by
  have hq : SSet.realizationWeakEquivalences (lastQ W x y z a) :=
    (lastQ_trivialFibration W hW x y z a).2
  have hs : SSet.realizationWeakEquivalences (lastSection W hW x y z a) := by
    apply SSet.realizationWeakEquivalences.of_postcomp (lastSection W hW x y z a)
      (lastQ W x y z a) hq
    rw [lastSection_Q]
    exact SSet.realizationWeakEquivalences.id_mem _
  apply SSet.realizationWeakEquivalences.of_precomp (lastSection W hW x y z a)
    (lastM W x y z a) hs
  rw [lastSection_M]
  exact mappingPostcomposition_realizationWeakEquivalence W hW y z a ha x

private def lastBase (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    mappingFibre W x z ⟶ mappingFibre W x z ⨯ mappingFibre W y z :=
  prod.lift (𝟙 _) (mappingFibre.snd W x z ≫ SSet.yonedaEquiv.symm a)

private theorem lastQ_eq (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastQ W x y z a = lastP W x y z a ≫ triangleComparison W x y z ≫ prod.fst := by
  dsimp only [lastQ, lastP, lastFixed, lastPair]
  have h := congrArg (fun f => f ≫ prod.fst)
    (pullback.condition (f := triangleComparison W x y z) (g := lastPair W x y z a))
  simpa only [Category.assoc, lastPair, prod.lift_fst, Category.comp_id] using h.symm

private theorem lastM_square (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    lastP W x y z a ≫ triangleTargetShear W x y z =
      lastM W x y z a ≫ lastBase W x y z a := by
  apply prod.hom_ext
  · simp only [Category.assoc, triangleTargetShear_fst, lastBase, prod.lift_fst,
      Category.comp_id, lastM]
  · have h := congrArg (fun f => f ≫ prod.snd)
      (pullback.condition (f := triangleComparison W x y z) (g := lastPair W x y z a))
    have hp : lastQ W x y z a ≫ mappingFibre.snd W x y =
        lastM W x y z a ≫ mappingFibre.snd W x z := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have h₁ : lastP W x y z a ≫ triangleComparison W x y z ≫ prod.snd =
        lastQ W x y z a ≫ mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm a := by
      dsimp only [lastFixed, lastP, lastQ, lastPair]
      simpa only [Category.assoc, lastPair, prod.lift_snd] using h
    calc
      _ = lastP W x y z a ≫ triangleComparison W x y z ≫ prod.snd := by
        rw [Category.assoc, triangleTargetShear_snd]
      _ = _ := h₁
      _ = lastM W x y z a ≫ mappingFibre.snd W x z ≫ SSet.yonedaEquiv.symm a := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ SSet.yonedaEquiv.symm a) hp
      _ = _ := by simp only [Category.assoc, lastBase, prod.lift_snd]

private theorem lastM_isPullback (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    IsPullback (lastP W x y z a) (lastM W x y z a)
      (triangleTargetShear W x y z) (lastBase W x y z a) := by
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux'
    (PullbackCone.mk _ _ (lastM_square W x y z a)) (fun s => ?_))
  have he : s.fst ≫ triangleComparison W x y z =
      (s.fst ≫ triangleComparison W x y z ≫ prod.fst) ≫ lastPair W x y z a := by
    apply prod.hom_ext
    · simp only [Category.assoc, lastPair, prod.lift_fst, Category.comp_id]
    · have h := congrArg (fun f => f ≫ prod.snd) s.condition
      have hp : s.snd ≫ mappingFibre.snd W x z =
          s.fst ≫ triangleComparison W x y z ≫ prod.fst ≫ mappingFibre.snd W x y :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      have h₁ : s.fst ≫ triangleComparison W x y z ≫ prod.snd =
          s.snd ≫ mappingFibre.snd W x z ≫ SSet.yonedaEquiv.symm a := by
        simpa only [Category.assoc, triangleTargetShear_snd, lastBase, prod.lift_snd] using h
      calc
        _ = _ := h₁
        _ = s.fst ≫ triangleComparison W x y z ≫ prod.fst ≫
            mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm a := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ SSet.yonedaEquiv.symm a) hp
        _ = _ := by simp only [Category.assoc, lastPair, prod.lift_snd]
  let l := pullback.lift s.fst (s.fst ≫ triangleComparison W x y z ≫ prod.fst) he
  refine ⟨l, pullback.lift_fst _ _ _, ?_, ?_⟩
  · change l ≫ lastM W x y z a = s.snd
    have hl : l ≫ lastP W x y z a = s.fst := pullback.lift_fst _ _ _
    have h := congrArg (fun f => f ≫ prod.fst) s.condition
    have hm : s.fst ≫ triangleMiddle W x y z = s.snd := by
      simpa only [Category.assoc, triangleTargetShear_fst, lastBase, prod.lift_fst,
        Category.comp_id] using h
    change (l ≫ lastP W x y z a) ≫ triangleMiddle W x y z = s.snd
    rw [hl]
    exact hm
  · intro m hm _
    change m ≫ lastP W x y z a = s.fst at hm
    apply pullback.hom_ext (f := triangleComparison W x y z) (g := lastPair W x y z a)
    · exact hm.trans (pullback.lift_fst _ _ _).symm
    · change m ≫ lastQ W x y z a = l ≫ lastQ W x y z a
      calc
        _ = m ≫ lastP W x y z a ≫ triangleComparison W x y z ≫ prod.fst := by rw [lastQ_eq]
        _ = s.fst ≫ triangleComparison W x y z ≫ prod.fst := by rw [← Category.assoc, hm]
        _ = _ := (pullback.lift_snd _ _ _).symm

private theorem lastM_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    Fibration (lastM W x y z a) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hf := ReedyModel.triangleTargetShear_fibration W x y z hW.1
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    ((fibrations SSet.{u}).of_isPullback (lastM_isPullback W x y z a)
      ((HomotopicalAlgebra.fibration_iff _).mp hf))

private theorem lastM_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W y z).app (op ⦋0⦌) a)) :
    trivialFibrations SSet.{u} (lastM W x y z a) :=
  ⟨(HomotopicalAlgebra.fibration_iff _).mp (lastM_fibration W hW x y z a),
    lastM_weak W hW x y z a ha⟩

private theorem sourceTriangleSquare (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    IsPullback (triangleProjection W x y z) (triangleShear W x y z)
      (outerHornComparison W) (triangleShearPair W x y z) := by
  apply IsPullback.of_iso_pullback
    (⟨by
      rw [← triangleShearIso_hom_projection W x y z,
        ← triangleShearIso_hom_pair W x y z]
      simp only [Category.assoc, pullback.condition]⟩)
    (triangleShearIso W x y z)
  · exact triangleShearIso_hom_projection W x y z
  · exact triangleShearIso_hom_pair W x y z

private theorem targetTriangleSquare (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    IsPullback (triangleProjection W x y z) (triangleTargetShear W x y z)
      (outerHornTargetComparison W) (triangleTargetShearPair W x y z) := by
  apply IsPullback.of_iso_pullback
    (⟨by
      rw [← triangleTargetShearIso_hom_projection W x y z,
        ← triangleTargetShearIso_hom_pair W x y z]
      simp only [Category.assoc, pullback.condition]⟩)
    (triangleTargetShearIso W x y z)
  · exact triangleTargetShearIso_hom_projection W x y z
  · exact triangleTargetShearIso_hom_pair W x y z

private theorem firstOuterSquare (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    IsPullback (firstP W x y z a ≫ triangleProjection W x y z) (firstM W x y z a)
      (outerHornComparison W) (firstBase W x y z a ≫ triangleShearPair W x y z) :=
  (firstM_isPullback W x y z a).paste_horiz (sourceTriangleSquare W x y z)

private theorem lastOuterSquare (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y z) _⦋0⦌) :
    IsPullback (lastP W x y z a ≫ triangleProjection W x y z) (lastM W x y z a)
      (outerHornTargetComparison W) (lastBase W x y z a ≫ triangleTargetShearPair W x y z) :=
  (lastM_isPullback W x y z a).paste_horiz (targetTriangleSquare W x y z)

private def pointArrow (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y :=
  pullback.lift (SSet.yonedaEquiv.symm g) (𝟙 _) (by
    apply prod.hom_ext
    · rw [Category.assoc, mappingEndpoint_fst, Category.id_comp,
        mappingPointPair_fst, SSet.yonedaEquiv_symm_comp, hs]
    · rw [Category.assoc, mappingEndpoint_snd, Category.id_comp,
        mappingPointPair_snd, SSet.yonedaEquiv_symm_comp, ht])

private theorem pointArrow_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    pointArrow W x y g hs ht ≫ mappingFibre.fst W x y = SSet.yonedaEquiv.symm g :=
  pullback.lift_fst _ _ _

private theorem pointArrow_snd (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    pointArrow W x y g hs ht ≫ mappingFibre.snd W x y = 𝟙 _ :=
  pullback.lift_snd _ _ _

private def point (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (mappingFibre W x y) _⦋0⦌ := SSet.yonedaEquiv (pointArrow W x y g hs ht)

private theorem point_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (mappingFibre.fst W x y).app (op ⦋0⦌) (point W x y g hs ht) = g := by
  change SSet.yonedaEquiv (pointArrow W x y g hs ht ≫ mappingFibre.fst W x y) = g
  rw [pointArrow_fst, Equiv.apply_symm_apply]

private theorem point_symm (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    SSet.yonedaEquiv.symm (point W x y g hs ht) = pointArrow W x y g hs ht :=
  Equiv.symm_apply_apply _ _

private theorem firstOuterPoint_TF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (b : (outerHornFork W) _⦋0⦌)
    (hb : IsEquivalenceEdge W hW
      ((pullback.snd (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app (op ⦋0⦌) b)) :
    trivialFibrations SSet.{u}
      (pullback.snd (outerHornComparison W) (SSet.yonedaEquiv.symm b)) := by
  let l := (pullback.fst (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app
    (op ⦋0⦌) b
  let r := (pullback.snd (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app
    (op ⦋0⦌) b
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) l
  let y := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) r
  let z := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) l
  have hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) r = x :=
    (congrArg (fun f => f.app (op ⦋0⦌) b)
      (pullback.condition (f := W.diagram.δ (1 : Fin 2))
        (g := W.diagram.δ (1 : Fin 2)))).symm
  let a := point W x y r hs rfl
  let h := point W x z l rfl rfl
  have ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a) := by
    dsimp only [a]
    rw [point_fst]
    exact hb
  have he : SSet.yonedaEquiv.symm h ≫ firstBase W x y z a ≫ triangleShearPair W x y z =
      SSet.yonedaEquiv.symm b := by
    apply pullback.hom_ext
    · simp only [Category.assoc, triangleShearPair_fst, firstBase, prod.lift_fst_assoc,
        Category.id_comp]
      change SSet.yonedaEquiv.symm h ≫ mappingFibre.fst W x z = _
      rw [show SSet.yonedaEquiv.symm h = pointArrow W x z l rfl rfl from point_symm ..,
        pointArrow_fst, SSet.yonedaEquiv_symm_comp]
    · simp only [Category.assoc, triangleShearPair_snd, firstBase, prod.lift_snd_assoc]
      rw [show SSet.yonedaEquiv.symm h = pointArrow W x z l rfl rfl from point_symm ..,
        ← Category.assoc _ (mappingFibre.snd W x z) _, pointArrow_snd, Category.id_comp]
      rw [show SSet.yonedaEquiv.symm a = pointArrow W x y r hs rfl from point_symm ..,
        pointArrow_fst, SSet.yonedaEquiv_symm_comp]
  have hp := (IsPullback.of_hasPullback (firstM W x y z a) (SSet.yonedaEquiv.symm h)).paste_horiz
    (firstOuterSquare W x y z a)
  rw [he] at hp
  have ht : trivialFibrations SSet.{u}
      (pullback.snd (firstM W x y z a) (SSet.yonedaEquiv.symm h)) :=
    (trivialFibrations SSet.{u}).of_isPullback
      (IsPullback.of_hasPullback (firstM W x y z a) (SSet.yonedaEquiv.symm h))
      (firstM_trivialFibration W hW x y z a ha)
  apply ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso hp.isoPullback.hom _).mp
  rw [hp.isoPullback_hom_snd]
  exact ht

private theorem lastOuterPoint_TF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (b : (outerHornTargetFork W) _⦋0⦌)
    (hb : IsEquivalenceEdge W hW
      ((pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))).app (op ⦋0⦌) b)) :
    trivialFibrations SSet.{u}
      (pullback.snd (outerHornTargetComparison W) (SSet.yonedaEquiv.symm b)) := by
  let l := (pullback.fst (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))).app
    (op ⦋0⦌) b
  let r := (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))).app
    (op ⦋0⦌) b
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) l
  let y := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) r
  let z := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) l
  have ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) r = z :=
    (congrArg (fun f => f.app (op ⦋0⦌) b)
      (pullback.condition (f := W.diagram.δ (0 : Fin 2))
        (g := W.diagram.δ (0 : Fin 2)))).symm
  let a := point W y z r rfl ht
  let h := point W x z l rfl rfl
  have ha : IsEquivalenceEdge W hW ((mappingFibre.fst W y z).app (op ⦋0⦌) a) := by
    dsimp only [a]
    rw [point_fst]
    exact hb
  have he : SSet.yonedaEquiv.symm h ≫ lastBase W x y z a ≫ triangleTargetShearPair W x y z =
      SSet.yonedaEquiv.symm b := by
    apply pullback.hom_ext
    · simp only [Category.assoc, triangleTargetShearPair_fst, lastBase, prod.lift_fst_assoc,
        Category.id_comp]
      change SSet.yonedaEquiv.symm h ≫ mappingFibre.fst W x z = _
      rw [show SSet.yonedaEquiv.symm h = pointArrow W x z l rfl rfl from point_symm ..,
        pointArrow_fst, SSet.yonedaEquiv_symm_comp]
    · simp only [Category.assoc, triangleTargetShearPair_snd, lastBase, prod.lift_snd_assoc]
      rw [show SSet.yonedaEquiv.symm h = pointArrow W x z l rfl rfl from point_symm ..,
        ← Category.assoc _ (mappingFibre.snd W x z) _, pointArrow_snd, Category.id_comp]
      rw [show SSet.yonedaEquiv.symm a = pointArrow W y z r rfl ht from point_symm ..,
        pointArrow_fst, SSet.yonedaEquiv_symm_comp]
  have hp := (IsPullback.of_hasPullback (lastM W x y z a) (SSet.yonedaEquiv.symm h)).paste_horiz
    (lastOuterSquare W x y z a)
  rw [he] at hp
  have hf : trivialFibrations SSet.{u}
      (pullback.snd (lastM W x y z a) (SSet.yonedaEquiv.symm h)) :=
    (trivialFibrations SSet.{u}).of_isPullback
      (IsPullback.of_hasPullback (lastM W x y z a) (SSet.yonedaEquiv.symm h))
      (lastM_trivialFibration W hW x y z a ha)
  apply ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso hp.isoPullback.hom _).mp
  rw [hp.isoPullback_hom_snd]
  exact hf

private theorem firstEdgeNormalization (W : SimplicialSpace.{u}) :
    (outerHornMappingIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map firstEdge.op ≫ (discreteYonedaIso W 1).hom := by
  rw [outerHornMappingIso_snd]
  change (discreteSourceMapping W).map SSet.Rezk.outerHornRight.op ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornRightIso.hom.op ≫ _ = _
  simp only [firstEdge, op_comp, CategoryTheory.Functor.map_comp, Category.assoc]

private theorem lastEdgeNormalization (W : SimplicialSpace.{u}) :
    (outerHornTargetMappingIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map lastEdge.op ≫ (discreteYonedaIso W 1).hom := by
  rw [outerHornTargetMappingIso_hom_snd]
  change (discreteSourceMapping W).map SSet.Rezk.outerHornTargetRight.op ≫
      (discreteSourceMapping W).map SSet.Rezk.outerHornTargetRightIso.hom.op ≫ _ = _
  simp only [lastEdge, op_comp, CategoryTheory.Functor.map_comp, Category.assoc]

private theorem firstRawPoint_TF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (b : ((discreteSourceMapping W).obj (op (Λ[2, 0] : SSet.{u}))) _⦋0⦌)
    (hb : IsEquivalenceEdge W hW
      (((discreteSourceMapping W).map firstEdge.op ≫ (discreteYonedaIso W 1).hom).app
        (op ⦋0⦌) b)) :
    trivialFibrations SSet.{u}
      (pullback.snd ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op)
        (SSet.yonedaEquiv.symm b)) := by
  let r := (discreteSourceMapping W).map (SSet.horn 2 0).ι.op
  let b' := (outerHornMappingIso W).hom.app (op ⦋0⦌) b
  have hb' : IsEquivalenceEdge W hW
      ((pullback.snd (W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app
        (op ⦋0⦌) b') := by
    change IsEquivalenceEdge W hW
      (((outerHornMappingIso W).hom ≫ pullback.snd _ _).app (op ⦋0⦌) b)
    rw [firstEdgeNormalization]
    exact hb
  have hr : r ≫ (outerHornMappingIso W).hom =
      (discreteYonedaIso W 2).hom ≫ outerHornComparison W := by
    rw [← outerHornMappingIso_normalization W]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, r]
  have hs := (IsPullback.of_hasPullback r (SSet.yonedaEquiv.symm b)).of_iso
    (fst' := pullback.fst r (SSet.yonedaEquiv.symm b) ≫ (discreteYonedaIso W 2).hom)
    (snd' := pullback.snd r (SSet.yonedaEquiv.symm b))
    (f' := outerHornComparison W) (g' := SSet.yonedaEquiv.symm b')
    (Iso.refl _) (discreteYonedaIso W 2) (Iso.refl _) (outerHornMappingIso W)
    (by simp) (by simp) hr (by simp only [Iso.refl_hom, Category.id_comp,
      SSet.yonedaEquiv_symm_comp, b'])
  have ht := firstOuterPoint_TF W hW b' hb'
  have hh := ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso
    hs.isoPullback.hom (pullback.snd (outerHornComparison W) (SSet.yonedaEquiv.symm b'))).mpr ht
  rw [hs.isoPullback_hom_snd] at hh
  exact hh

private theorem lastRawPoint_TF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (b : ((discreteSourceMapping W).obj (op (Λ[2, 2] : SSet.{u}))) _⦋0⦌)
    (hb : IsEquivalenceEdge W hW
      (((discreteSourceMapping W).map lastEdge.op ≫ (discreteYonedaIso W 1).hom).app
        (op ⦋0⦌) b)) :
    trivialFibrations SSet.{u}
      (pullback.snd ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op)
        (SSet.yonedaEquiv.symm b)) := by
  let r := (discreteSourceMapping W).map (SSet.horn 2 2).ι.op
  let b' := (outerHornTargetMappingIso W).hom.app (op ⦋0⦌) b
  have hb' : IsEquivalenceEdge W hW
      ((pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))).app
        (op ⦋0⦌) b') := by
    change IsEquivalenceEdge W hW
      (((outerHornTargetMappingIso W).hom ≫ pullback.snd _ _).app (op ⦋0⦌) b)
    rw [lastEdgeNormalization]
    exact hb
  have hr : r ≫ (outerHornTargetMappingIso W).hom =
      (discreteYonedaIso W 2).hom ≫ outerHornTargetComparison W := by
    rw [← outerHornTargetMappingIso_restriction W]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, r]
  have hs := (IsPullback.of_hasPullback r (SSet.yonedaEquiv.symm b)).of_iso
    (fst' := pullback.fst r (SSet.yonedaEquiv.symm b) ≫ (discreteYonedaIso W 2).hom)
    (snd' := pullback.snd r (SSet.yonedaEquiv.symm b))
    (f' := outerHornTargetComparison W) (g' := SSet.yonedaEquiv.symm b')
    (Iso.refl _) (discreteYonedaIso W 2) (Iso.refl _) (outerHornTargetMappingIso W)
    (by simp) (by simp) hr (by simp only [Iso.refl_hom, Category.id_comp,
      SSet.yonedaEquiv_symm_comp, b'])
  have ht := lastOuterPoint_TF W hW b' hb'
  have hh := ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso
    hs.isoPullback.hom (pullback.snd (outerHornTargetComparison W)
        (SSet.yonedaEquiv.symm b'))).mpr ht
  rw [hs.isoPullback_hom_snd] at hh
  exact hh

private theorem TF_of_point_TF {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (h : ∀ b : Y _⦋0⦌, trivialFibrations SSet.{u} (pullback.snd p (SSet.yonedaEquiv.symm b))) :
    trivialFibrations SSet.{u} p := by
  refine ⟨Fibration.mem, ?_⟩
  apply (SSet.realizationWeakEquivalence_iff_fibrewise_of_fibrations
    p p (𝟙 Y) (Category.comp_id p)).mpr
  intro b
  let η := SSet.Subcomplex.mapFiber (f := p) (f' := 𝟙 Y) p (𝟙 Y)
    ((Category.comp_id p).trans (Category.comp_id p).symm) (y := b) (y' := b) rfl
  let a := SSet.stdSimplex.isTerminalObj₀.from (SSet.Subcomplex.fiber p b : SSet.{u})
  let c := SSet.stdSimplex.isTerminalObj₀.from (SSet.Subcomplex.fiber (𝟙 Y) b : SSet.{u})
  have hs : IsPullback (SSet.Subcomplex.fiber p b).ι a p (SSet.yonedaEquiv.symm b) := by
    simpa only [SSet.yonedaEquiv_symm_zero] using SSet.Subcomplex.fiber_isPullback p b
  have ha : trivialFibrations SSet.{u} a := by
    have hh := ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso hs.isoPullback.hom
      (pullback.snd p (SSet.yonedaEquiv.symm b))).mpr (h b)
    rw [hs.isoPullback_hom_snd] at hh
    exact hh
  have ht : IsTerminal (SSet.Subcomplex.fiber (𝟙 Y) b : SSet.{u}) := by
    change IsTerminal ((SSet.Subcomplex.ofSimplex b).preimage (𝟙 Y) : SSet.{u})
    rw [SSet.Subcomplex.preimage_id]
    exact SSet.Subcomplex.isTerminalOfSimplex b
  let _ : IsIso c := isIso_of_isTerminal ht SSet.stdSimplex.isTerminalObj₀ c
  have hc : η ≫ c = a := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  apply (SSet.realizationWeakEquivalences.cancel_right_of_respectsIso η c).mp
  rw [hc]
  exact ha.2

private theorem rawHorn_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) (j : Fin 3) :
    Fibration ((discreteSourceMapping W).map (SSet.horn 2 j).ι.op) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let i := (SSet.horn 2 j : (Δ[2] : SSet.{u}).Subcomplex).ι
  let _ : Mono i := by dsimp [i]; infer_instance
  let _ : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [NatTrans.mono_iff_mono_app]
    intro n
    change Mono (i.app m)
    infer_instance
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  have hf : cofibrations SimplicialSpace.{u} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp
      ((ReedyModel.cofibration_iff f).mpr inferInstance)
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (ReedyModel.inner_precomp_fibration f W hf hW.1)

/-- The original first-edge selected square is its actual preimage pullback. -/
theorem firstRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsPullback (firstSource W hW).ι (firstRestriction W hW)
      ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op) (firstTarget W hW).ι :=
  SSet.Subcomplex.preimage_isPullback _ _

/-- The original last-edge selected square is its actual preimage pullback. -/
theorem lastRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsPullback (lastSource W hW).ι (lastRestriction W hW)
      ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op) (lastTarget W hW).ι :=
  SSet.Subcomplex.preimage_isPullback _ _

/-- Reedy fibrancy makes the original selected first-edge restriction a Kan fibration. -/
theorem firstRestriction_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (firstRestriction W hW) := by
  let _ : Fibration ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op) := rawHorn_fibration W hW 0
  exact ⟨(fibrations SSet.{u}).of_isPullback (firstRestriction_isPullback W hW) Fibration.mem⟩

/-- Reedy fibrancy makes the original selected last-edge restriction a Kan fibration. -/
theorem lastRestriction_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (lastRestriction W hW) := by
  let _ : Fibration ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op) := rawHorn_fibration W hW 2
  exact ⟨(fibrations SSet.{u}).of_isPullback (lastRestriction_isPullback W hW) Fibration.mem⟩

/-- The first-edge selected target is Kan, with its fibrancy derived internally. -/
theorem firstTarget_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (firstTarget W hW : SSet.{u}) := by
  let _ : SSet.KanComplex ((discreteSourceMapping W).obj (op (Λ[2, 0] : SSet.{u}))) :=
    EquivalenceMapping.rawMapping_kan W hW _
  let _ : Fibration (firstTarget W hW).ι :=
    ⟨(fibrations SSet.{u}).of_isPullback
      (SSet.Subcomplex.preimage_isPullback (EquivalenceMapping.subcomplex W hW Δ[1])
        ((discreteSourceMapping W).map firstEdge.op)).flip
      (EquivalenceMapping.inclusion_fibration W hW Δ[1]).mem⟩
  exact isFibrant_of_fibration (firstTarget W hW).ι

/-- The last-edge selected target is Kan, with its fibrancy derived internally. -/
theorem lastTarget_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (lastTarget W hW : SSet.{u}) := by
  let _ : SSet.KanComplex ((discreteSourceMapping W).obj (op (Λ[2, 2] : SSet.{u}))) :=
    EquivalenceMapping.rawMapping_kan W hW _
  let _ : Fibration (lastTarget W hW).ι :=
    ⟨(fibrations SSet.{u}).of_isPullback
      (SSet.Subcomplex.preimage_isPullback (EquivalenceMapping.subcomplex W hW Δ[1])
        ((discreteSourceMapping W).map lastEdge.op)).flip
      (EquivalenceMapping.inclusion_fibration W hW Δ[1]).mem⟩
  exact isFibrant_of_fibration (lastTarget W hW).ι

/-- The original selected first-edge source is Kan through its same restriction. -/
theorem firstSource_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (firstSource W hW : SSet.{u}) := by
  let _ : SSet.KanComplex (firstTarget W hW : SSet.{u}) := firstTarget_kan W hW
  let _ : Fibration (firstRestriction W hW) := firstRestriction_fibration W hW
  exact isFibrant_of_fibration (firstRestriction W hW)

/-- The original selected last-edge source is Kan through its same restriction. -/
theorem lastSource_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (lastSource W hW : SSet.{u}) := by
  let _ : SSet.KanComplex (lastTarget W hW : SSet.{u}) := lastTarget_kan W hW
  let _ : Fibration (lastRestriction W hW) := lastRestriction_fibration W hW
  exact isFibrant_of_fibration (lastRestriction W hW)

/-- The global original source-horn restriction is trivial over every selected first edge. -/
theorem firstRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (firstRestriction W hW) := by
  let _ : Fibration (firstRestriction W hW) := firstRestriction_fibration W hW
  apply TF_of_point_TF (firstRestriction W hW)
  intro b
  have he : ((discreteSourceMapping W).map firstEdge.op).app (op ⦋0⦌) b.val ∈
      (EquivalenceMapping.subcomplex W hW Δ[1]).obj (op ⦋0⦌) := b.property
  have hb : IsEquivalenceEdge W hW
      (((discreteSourceMapping W).map firstEdge.op ≫ (discreteYonedaIso W 1).hom).app
        (op ⦋0⦌) b.val) :=
    (mem_equivalenceSubcomplex_zero W hW _).mp
      ((EquivalenceMapping.mem_subcomplex_one W hW _ _).mp he)
  have ht := firstRawPoint_TF W hW b.val hb
  have hs :=
      (IsPullback.of_hasPullback (firstRestriction W hW) (SSet.yonedaEquiv.symm b)).paste_horiz
    (firstRestriction_isPullback W hW)
  rw [SSet.yonedaEquiv_symm_comp] at hs
  change IsPullback
    (pullback.fst (firstRestriction W hW) (SSet.yonedaEquiv.symm b) ≫ (firstSource W hW).ι)
    (pullback.snd (firstRestriction W hW) (SSet.yonedaEquiv.symm b))
    ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op) (SSet.yonedaEquiv.symm b.val) at hs
  have hh := ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso hs.isoPullback.hom
    (pullback.snd ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op)
      (SSet.yonedaEquiv.symm b.val))).mpr ht
  rw [hs.isoPullback_hom_snd] at hh
  exact hh

/-- The global original target-horn restriction is trivial over every selected last edge. -/
theorem lastRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (lastRestriction W hW) := by
  let _ : Fibration (lastRestriction W hW) := lastRestriction_fibration W hW
  apply TF_of_point_TF (lastRestriction W hW)
  intro b
  have he : ((discreteSourceMapping W).map lastEdge.op).app (op ⦋0⦌) b.val ∈
      (EquivalenceMapping.subcomplex W hW Δ[1]).obj (op ⦋0⦌) := b.property
  have hb : IsEquivalenceEdge W hW
      (((discreteSourceMapping W).map lastEdge.op ≫ (discreteYonedaIso W 1).hom).app
        (op ⦋0⦌) b.val) :=
    (mem_equivalenceSubcomplex_zero W hW _).mp
      ((EquivalenceMapping.mem_subcomplex_one W hW _ _).mp he)
  have ht := lastRawPoint_TF W hW b.val hb
  have hs :=
      (IsPullback.of_hasPullback (lastRestriction W hW) (SSet.yonedaEquiv.symm b)).paste_horiz
    (lastRestriction_isPullback W hW)
  rw [SSet.yonedaEquiv_symm_comp] at hs
  change IsPullback
    (pullback.fst (lastRestriction W hW) (SSet.yonedaEquiv.symm b) ≫ (lastSource W hW).ι)
    (pullback.snd (lastRestriction W hW) (SSet.yonedaEquiv.symm b))
    ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op) (SSet.yonedaEquiv.symm b.val) at hs
  have hh := ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso hs.isoPullback.hom
    (pullback.snd ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op)
      (SSet.yonedaEquiv.symm b.val))).mpr ht
  rw [hs.isoPullback_hom_snd] at hh
  exact hh

private theorem triangleIsoCancellation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (t : (W.diagram _⦋2⦌) _⦋0⦌) :
    (IsEquivalenceEdge W hW ((W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t) →
      IsEquivalenceEdge W hW ((W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t) →
      IsEquivalenceEdge W hW ((W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t)) ∧
    (IsEquivalenceEdge W hW ((W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) →
      IsEquivalenceEdge W hW ((W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t) →
      IsEquivalenceEdge W hW ((W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)) := by
  let a₀ := (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t
  let b₀ := (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t
  let c₀ := (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) a₀
  let y := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) a₀
  let z := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) b₀
  have hb : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) b₀ = y := by
    exact congrArg (fun f => f.app (op ⦋0⦌) t)
      (W.diagram.δ_comp_δ (i := (0 : Fin 2)) (j := 1) (by decide)).symm
  have hc₀ : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) c₀ = x := by
    exact congrArg (fun f => f.app (op ⦋0⦌) t)
      (W.diagram.δ_comp_δ_self (i := (1 : Fin 2)))
  have hc₁ : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) c₀ = z := by
    exact congrArg (fun f => f.app (op ⦋0⦌) t)
      (W.diagram.δ_comp_δ_self (i := (0 : Fin 2))).symm
  let a := point W x y a₀ rfl rfl
  let b := point W y z b₀ hb rfl
  let c := point W x z c₀ hc₀ hc₁
  have ha' : (mappingFibre.fst W x y).app (op ⦋0⦌) a = a₀ := point_fst ..
  have hb' : (mappingFibre.fst W y z).app (op ⦋0⦌) b = b₀ := point_fst ..
  have hc' : (mappingFibre.fst W x z).app (op ⦋0⦌) c = c₀ := point_fst ..
  have hcomp : compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b) = SSet.π₀.mk c :=
    compose_of_original_triangle W hW t a b c ha' hb' hc'
  constructor
  · intro ha hc
    let _ : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) :=
      (isEquivalenceEdge_iff_of_fibre W hW a₀ a ha').mp ha
    let _ : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨z⟩) (SSet.π₀.mk c) :=
      (isEquivalenceEdge_iff_of_fibre W hW c₀ c hc').mp hc
    have _ : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨z⟩)
        (compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b)) := hcomp.symm ▸ inferInstance
    exact (isEquivalenceEdge_iff_of_fibre W hW b₀ b hb').mpr
      (IsIso.of_isIso_comp_left (C := Object W hW)
        (X := ⟨x⟩) (Y := ⟨y⟩) (Z := ⟨z⟩) (SSet.π₀.mk a) (SSet.π₀.mk b))
  · intro hb hc
    let _ : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨z⟩) (SSet.π₀.mk b) :=
      (isEquivalenceEdge_iff_of_fibre W hW b₀ b hb').mp hb
    let _ : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨z⟩) (SSet.π₀.mk c) :=
      (isEquivalenceEdge_iff_of_fibre W hW c₀ c hc').mp hc
    have _ : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨z⟩)
        (compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b)) := hcomp.symm ▸ inferInstance
    exact (isEquivalenceEdge_iff_of_fibre W hW a₀ a ha').mpr
      (IsIso.of_isIso_comp_right (C := Object W hW)
        (X := ⟨z⟩) (Y := ⟨y⟩) (Z := ⟨x⟩) (SSet.π₀.mk a) (SSet.π₀.mk b))

private theorem oneToTwoCases (θ : ⦋1⦌ ⟶ ⦋2⦌) :
    θ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 0 ∨ θ = SimplexCategory.δ (2 : Fin 3) ∨
    θ = SimplexCategory.δ (1 : Fin 3) ∨ θ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 1 ∨
    θ = SimplexCategory.δ (0 : Fin 3) ∨ θ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 2 := by
  have hm := θ.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
  generalize h₀ : θ.toOrderHom 0 = i at hm
  generalize h₁ : θ.toOrderHom 1 = j at hm
  fin_cases i <;> fin_cases j
  · exact Or.inl (SimplexCategory.Hom.ext_one_left _ _ h₀ h₁)
  · exact Or.inr (Or.inl (SimplexCategory.Hom.ext_one_left _ _ h₀ h₁))
  · exact Or.inr (Or.inr (Or.inl (SimplexCategory.Hom.ext_one_left _ _ h₀ h₁)))
  · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ 0)) hm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (SimplexCategory.Hom.ext_one_left _ _ h₀ h₁))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (SimplexCategory.Hom.ext_one_left _ _ h₀ h₁)))))
  · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ 0)) hm)
  · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ 1)) hm)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (SimplexCategory.Hom.ext_one_left _ _ h₀ h₁)))))

private theorem constantTriangleEdge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (t : (W.diagram _⦋2⦌) _⦋0⦌) (i : Fin 3) :
    IsEquivalenceEdge W hW ((W.diagram.map (SimplexCategory.const ⦋1⦌ ⦋2⦌ i).op).app
      (op ⦋0⦌) t) := by
  have hc : SimplexCategory.const ⦋1⦌ ⦋2⦌ i =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋2⦌ i :=
    SimplexCategory.Hom.ext_one_left _ _ rfl rfl
  rw [hc, op_comp, W.diagram.map_comp]
  exact identity_isEquivalenceEdge W hW _

private theorem allEvaluationsOfFaces (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (q : ((discreteSourceMapping W).obj (op (Δ[2] : SSet.{u}))) _⦋0⦌)
    (h : ∀ i : Fin 3, IsEquivalenceEdge W hW
      ((W.diagram.δ i).app (op ⦋0⦌) ((discreteYonedaIso W 2).hom.app (op ⦋0⦌) q))) :
    ∀ γ : (Δ[1] : SSet.{u}) ⟶ Δ[2], IsEquivalenceEdge W hW
      ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) := by
  intro γ
  obtain ⟨θ, rfl⟩ := SSet.stdSimplex.map_surjective γ
  change IsEquivalenceEdge W hW
    (((discreteSourceMapping W).map (SSet.stdSimplex.map θ).op ≫
      (discreteYonedaIso W 1).hom).app (op ⦋0⦌) q)
  rw [discreteYonedaIso_naturality_index]
  rcases oneToTwoCases θ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact constantTriangleEdge W hW _ 0
  · exact h 2
  · exact h 1
  · exact constantTriangleEdge W hW _ 1
  · exact h 0
  · exact constantTriangleEdge W hW _ 2

private theorem equivalenceFaceOfHorn {A : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (i : A ⟶ (Δ[2] : SSet.{u}))
    (q : ((discreteSourceMapping W).obj (op (Δ[2] : SSet.{u}))) _⦋0⦌)
    (hq : ((discreteSourceMapping W).map i.op).app (op ⦋0⦌) q ∈
      (EquivalenceMapping.subcomplex W hW A).obj (op ⦋0⦌))
    (j : Fin 3) (γ : (Δ[1] : SSet.{u}) ⟶ A) (hγ : γ ≫ i = SSet.stdSimplex.δ j) :
    IsEquivalenceEdge W hW ((W.diagram.δ j).app (op ⦋0⦌)
      ((discreteYonedaIso W 2).hom.app (op ⦋0⦌) q)) := by
  have h := (mem_equivalenceSubcomplex_zero W hW _).mp
    (((EquivalenceMapping.mem_subcomplex W hW A _ _).mp hq) γ)
  change IsEquivalenceEdge W hW
    (((discreteSourceMapping W).map i.op ≫ EquivalenceMapping.edgeEvaluation W γ).app
      (op ⦋0⦌) q) at h
  rw [EquivalenceMapping.edgeEvaluation_source, hγ] at h
  change IsEquivalenceEdge W hW
    (((discreteSourceMapping W).map (SSet.stdSimplex.map (SimplexCategory.δ j)).op ≫
      (discreteYonedaIso W 1).hom).app (op ⦋0⦌) q) at h
  rw [discreteYonedaIso_naturality_index] at h
  exact h

/-- All-edge selection over the source horn is the literal semantic preimage, including its missing
edge12. -/
theorem firstAll_preimage (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW Δ[2] =
      (EquivalenceMapping.subcomplex W hW (Λ[2, 0] : SSet.{u})).preimage
        ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op) := by
  ext n q
  constructor
  · intro hq
    exact ((EquivalenceMapping.restriction W hW (SSet.horn 2 0).ι).app n ⟨q, hq⟩).property
  · intro hq
    let α := SimplexCategory.const ⦋0⦌ n.unop 0
    let q₀ := ((discreteSourceMapping W).obj (op (Δ[2] : SSet.{u}))).map α.op q
    have hq₀ : ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op).app (op ⦋0⦌) q₀ ∈
        (EquivalenceMapping.subcomplex W hW (Λ[2, 0] : SSet.{u})).obj (op ⦋0⦌) := by
      have h := (EquivalenceMapping.mem_subcomplex_operator W hW _ α.op _).mp hq
      rw [← ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op).naturality_apply] at h
      exact h
    have ha := equivalenceFaceOfHorn W hW (SSet.horn 2 0).ι q₀ hq₀ 2 firstEdge firstEdge_ι
    have hc := equivalenceFaceOfHorn W hW (SSet.horn 2 0).ι q₀ hq₀ 1
      (SSet.Rezk.outerHornLeftIso.hom ≫ SSet.Rezk.outerHornLeft)
      (by rw [Category.assoc, SSet.Rezk.outerHornLeft_ι, SSet.Rezk.outerHornLeftIso_ι])
    have hb := (triangleIsoCancellation W hW _).1 ha hc
    apply (EquivalenceMapping.mem_subcomplex_vertex W hW Δ[2] n q α).mpr
    apply allEvaluationsOfFaces W hW q₀
    intro j
    fin_cases j
    · exact hb
    · exact hc
    · exact ha

/-- All-edge selection over the target horn is the literal semantic preimage, including its missing
edge01. -/
theorem lastAll_preimage (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW Δ[2] =
      (EquivalenceMapping.subcomplex W hW (Λ[2, 2] : SSet.{u})).preimage
        ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op) := by
  ext n q
  constructor
  · intro hq
    exact ((EquivalenceMapping.restriction W hW (SSet.horn 2 2).ι).app n ⟨q, hq⟩).property
  · intro hq
    let α := SimplexCategory.const ⦋0⦌ n.unop 0
    let q₀ := ((discreteSourceMapping W).obj (op (Δ[2] : SSet.{u}))).map α.op q
    have hq₀ : ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op).app (op ⦋0⦌) q₀ ∈
        (EquivalenceMapping.subcomplex W hW (Λ[2, 2] : SSet.{u})).obj (op ⦋0⦌) := by
      have h := (EquivalenceMapping.mem_subcomplex_operator W hW _ α.op _).mp hq
      rw [← ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op).naturality_apply] at h
      exact h
    have hb := equivalenceFaceOfHorn W hW (SSet.horn 2 2).ι q₀ hq₀ 0 lastEdge lastEdge_ι
    have hc := equivalenceFaceOfHorn W hW (SSet.horn 2 2).ι q₀ hq₀ 1
      (SSet.Rezk.outerHornTargetLeftIso.hom ≫ SSet.Rezk.outerHornTargetLeft)
      SSet.Rezk.outerHornTargetLeftIso_inclusion
    have ha := (triangleIsoCancellation W hW _).2 hb hc
    apply (EquivalenceMapping.mem_subcomplex_vertex W hW Δ[2] n q α).mpr
    apply allEvaluationsOfFaces W hW q₀
    intro j
    fin_cases j
    · exact hb
    · exact hc
    · exact ha

private theorem allFirstTarget_le (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW (Λ[2, 0] : SSet.{u}) ≤ firstTarget W hW := by
  intro n q hq
  apply (EquivalenceMapping.mem_subcomplex_one W hW n _).mpr
  exact ((EquivalenceMapping.mem_subcomplex W hW _ n q).mp hq) firstEdge

private theorem allLastTarget_le (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW (Λ[2, 2] : SSet.{u}) ≤ lastTarget W hW := by
  intro n q hq
  apply (EquivalenceMapping.mem_subcomplex_one W hW n _).mpr
  exact ((EquivalenceMapping.mem_subcomplex W hW _ n q).mp hq) lastEdge

private theorem allFirstSource_le (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW Δ[2] ≤ firstSource W hW :=
  (firstAll_preimage W hW).le.trans
    (SSet.Subcomplex.preimage_monotone _ (allFirstTarget_le W hW))

private theorem allLastSource_le (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW Δ[2] ≤ lastSource W hW :=
  (lastAll_preimage W hW).le.trans
    (SSet.Subcomplex.preimage_monotone _ (allLastTarget_le W hW))

/-- The actual all-edge source horn includes into its same first-edge selected target. -/
def firstAllTargetInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (EquivalenceMapping.subcomplex W hW (Λ[2, 0] : SSet.{u}) : SSet.{u}) ⟶ firstTarget W hW :=
  SSet.Subcomplex.homOfLE (allFirstTarget_le W hW)

/-- The actual all-edge target horn includes into its same last-edge selected target. -/
def lastAllTargetInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (EquivalenceMapping.subcomplex W hW (Λ[2, 2] : SSet.{u}) : SSet.{u}) ⟶ lastTarget W hW :=
  SSet.Subcomplex.homOfLE (allLastTarget_le W hW)

/-- The actual all-edge triangle includes into its first-edge selected source. -/
def firstAllSourceInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (EquivalenceMapping.subcomplex W hW Δ[2] : SSet.{u}) ⟶ firstSource W hW :=
  SSet.Subcomplex.homOfLE (allFirstSource_le W hW)

/-- The actual all-edge triangle includes into its last-edge selected source. -/
def lastAllSourceInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (EquivalenceMapping.subcomplex W hW Δ[2] : SSet.{u}) ⟶ lastSource W hW :=
  SSet.Subcomplex.homOfLE (allLastSource_le W hW)

/-- The first all-edge target inclusion retains the original ambient horn. -/
@[reassoc (attr := simp)]
theorem firstAllTargetInclusion_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    firstAllTargetInclusion W hW ≫ (firstTarget W hW).ι =
      (EquivalenceMapping.subcomplex W hW (Λ[2, 0] : SSet.{u})).ι :=
  SSet.Subcomplex.homOfLE_ι (allFirstTarget_le W hW)

/-- The last all-edge target inclusion retains the original ambient horn. -/
@[reassoc (attr := simp)]
theorem lastAllTargetInclusion_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    lastAllTargetInclusion W hW ≫ (lastTarget W hW).ι =
      (EquivalenceMapping.subcomplex W hW (Λ[2, 2] : SSet.{u})).ι :=
  SSet.Subcomplex.homOfLE_ι (allLastTarget_le W hW)

/-- The first all-edge source inclusion retains the original ambient triangle. -/
@[reassoc (attr := simp)]
theorem firstAllSourceInclusion_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    firstAllSourceInclusion W hW ≫ (firstSource W hW).ι =
      (EquivalenceMapping.subcomplex W hW Δ[2]).ι :=
  SSet.Subcomplex.homOfLE_ι (allFirstSource_le W hW)

/-- The last all-edge source inclusion retains the original ambient triangle. -/
@[reassoc (attr := simp)]
theorem lastAllSourceInclusion_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    lastAllSourceInclusion W hW ≫ (lastSource W hW).ι =
      (EquivalenceMapping.subcomplex W hW Δ[2]).ι :=
  SSet.Subcomplex.homOfLE_ι (allLastSource_le W hW)

private theorem allRestrictionRawPullback {A : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (i : A ⟶ (Δ[2] : SSet.{u}))
    (h : EquivalenceMapping.subcomplex W hW Δ[2] =
      (EquivalenceMapping.subcomplex W hW A).preimage ((discreteSourceMapping W).map i.op)) :
    IsPullback (EquivalenceMapping.subcomplex W hW Δ[2]).ι
      (EquivalenceMapping.restriction W hW i) ((discreteSourceMapping W).map i.op)
      (EquivalenceMapping.subcomplex W hW A).ι := by
  let e := SSet.Subcomplex.eqToIso h
  refine (SSet.Subcomplex.preimage_isPullback (EquivalenceMapping.subcomplex W hW A)
    ((discreteSourceMapping W).map i.op)).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · exact SSet.Subcomplex.homOfLE_ι h.le
  · apply (cancel_mono (EquivalenceMapping.subcomplex W hW A).ι).mp
    simp only [Category.assoc, SSet.Subcomplex.fromPreimage_ι,
      EquivalenceMapping.restriction_ι, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc]
    exact congrArg (fun f => f ≫ (discreteSourceMapping W).map i.op)
      (SSet.Subcomplex.homOfLE_ι h.le)

/-- The source-horn all-edge restriction is the actual base change of the selected global map. -/
theorem firstAllRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsPullback (firstAllSourceInclusion W hW)
      (EquivalenceMapping.restriction W hW (SSet.horn 2 0).ι)
      (firstRestriction W hW) (firstAllTargetInclusion W hW) := by
  have hw : firstAllSourceInclusion W hW ≫ firstRestriction W hW =
      EquivalenceMapping.restriction W hW (SSet.horn 2 0).ι ≫ firstAllTargetInclusion W hW := by
    apply (cancel_mono (firstTarget W hW).ι).mp
    simp only [Category.assoc, firstRestriction_ι, firstAllSourceInclusion_ι_assoc,
      firstAllTargetInclusion_ι, EquivalenceMapping.restriction_ι]
  have ho : IsPullback (firstAllSourceInclusion W hW ≫ (firstSource W hW).ι)
      (EquivalenceMapping.restriction W hW (SSet.horn 2 0).ι)
      ((discreteSourceMapping W).map (SSet.horn 2 0).ι.op)
      (firstAllTargetInclusion W hW ≫ (firstTarget W hW).ι) := by
    simpa only [firstAllSourceInclusion_ι, firstAllTargetInclusion_ι] using
      allRestrictionRawPullback W hW (SSet.horn 2 0).ι (firstAll_preimage W hW)
  exact ho.of_right hw (firstRestriction_isPullback W hW)

/-- The target-horn all-edge restriction is the actual base change of the selected global map. -/
theorem lastAllRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsPullback (lastAllSourceInclusion W hW)
      (EquivalenceMapping.restriction W hW (SSet.horn 2 2).ι)
      (lastRestriction W hW) (lastAllTargetInclusion W hW) := by
  have hw : lastAllSourceInclusion W hW ≫ lastRestriction W hW =
      EquivalenceMapping.restriction W hW (SSet.horn 2 2).ι ≫ lastAllTargetInclusion W hW := by
    apply (cancel_mono (lastTarget W hW).ι).mp
    simp only [Category.assoc, lastRestriction_ι, lastAllSourceInclusion_ι_assoc,
      lastAllTargetInclusion_ι, EquivalenceMapping.restriction_ι]
  have ho : IsPullback (lastAllSourceInclusion W hW ≫ (lastSource W hW).ι)
      (EquivalenceMapping.restriction W hW (SSet.horn 2 2).ι)
      ((discreteSourceMapping W).map (SSet.horn 2 2).ι.op)
      (lastAllTargetInclusion W hW ≫ (lastTarget W hW).ι) := by
    simpa only [lastAllSourceInclusion_ι, lastAllTargetInclusion_ι] using
      allRestrictionRawPullback W hW (SSet.horn 2 2).ι (lastAll_preimage W hW)
  exact ho.of_right hw (lastRestriction_isPullback W hW)

/-- The literal original all-edge source-horn restriction is a Kan-Quillen trivial fibration. -/
theorem firstAllRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (EquivalenceMapping.restriction W hW (SSet.horn 2 0).ι) :=
  (trivialFibrations SSet.{u}).of_isPullback (firstAllRestriction_isPullback W hW)
    (firstRestriction_trivialFibration W hW)

/-- The literal original all-edge target-horn restriction is a Kan-Quillen trivial fibration. -/
theorem lastAllRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (EquivalenceMapping.restriction W hW (SSet.horn 2 2).ι) :=
  (trivialFibrations SSet.{u}).of_isPullback (lastAllRestriction_isPullback W hW)
    (lastRestriction_trivialFibration W hW)

private def selectedMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) (A : SSet.{u}) (γ : (Δ[1] : SSet.{u}) ⟶ A) :
    ((EquivalenceMapping.subcomplex W hW Δ[1]).preimage
        ((discreteSourceMapping W).map γ.op) : SSet.{u}) ⟶
      (EquivalenceMapping.subcomplex V hV Δ[1]).preimage ((discreteSourceMapping V).map γ.op) :=
  SSet.Subcomplex.lift
    (((EquivalenceMapping.subcomplex W hW Δ[1]).preimage ((discreteSourceMapping W).map γ.op)).ι ≫
      (discreteSourceMappingMap q).app (op A)) (by
    intro n a ha
    obtain ⟨b, rfl⟩ := ha
    let e : (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}).obj n :=
      ⟨((discreteSourceMapping W).map γ.op).app n b.val, b.property⟩
    have h := ((EquivalenceMapping.targetMap q hW hV Δ[1]).app n e).property
    have hn := congrArg (fun f => f.app n b.val)
      ((discreteSourceMappingMap q).naturality γ.op)
    change ((discreteSourceMappingMap q).app (op (Δ[1] : SSet.{u}))).app n
        (((discreteSourceMapping W).map γ.op).app n b.val) =
      ((discreteSourceMapping V).map γ.op).app n
        (((discreteSourceMappingMap q).app (op A)).app n b.val) at hn
    change ((discreteSourceMapping V).map γ.op).app n
      (((discreteSourceMappingMap q).app (op A)).app n b.val) ∈
        (EquivalenceMapping.subcomplex V hV Δ[1]).obj n
    rw [← hn]
    exact h)

/-- Every original target map carries the selected first-edge horn to its same counterpart. -/
def firstTargetMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    (firstTarget W hW : SSet.{u}) ⟶ firstTarget V hV := selectedMap q hW hV _ firstEdge

/-- Every original target map carries the selected last-edge horn to its same counterpart. -/
def lastTargetMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    (lastTarget W hW : SSet.{u}) ⟶ lastTarget V hV := selectedMap q hW hV _ lastEdge

/-- The selected first-edge target map retains the original raw end map and inclusion. -/
@[reassoc (attr := simp)]
theorem firstTargetMap_ι {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    firstTargetMap q hW hV ≫ (firstTarget V hV).ι =
      (firstTarget W hW).ι ≫ (discreteSourceMappingMap q).app (op (Λ[2, 0] : SSet.{u})) := by
  unfold firstTargetMap selectedMap
  exact SSet.Subcomplex.lift_ι _ _

/-- The selected last-edge target map retains the original raw end map and inclusion. -/
@[reassoc (attr := simp)]
theorem lastTargetMap_ι {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    lastTargetMap q hW hV ≫ (lastTarget V hV).ι =
      (lastTarget W hW).ι ≫ (discreteSourceMappingMap q).app (op (Λ[2, 2] : SSet.{u})) := by
  unfold lastTargetMap selectedMap
  exact SSet.Subcomplex.lift_ι _ _

/-- Every original target map carries the first-edge selected triangle to its actual counterpart. -/
def firstSourceMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    (firstSource W hW : SSet.{u}) ⟶ firstSource V hV :=
  SSet.Subcomplex.lift ((firstSource W hW).ι ≫
    (discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u}))) (by
    intro n a ha
    obtain ⟨b, rfl⟩ := ha
    let e : (firstTarget W hW : SSet.{u}).obj n :=
      ⟨((discreteSourceMapping W).map (SSet.horn 2 0).ι.op).app n b.val, b.property⟩
    have h := ((firstTargetMap q hW hV).app n e).property
    have hi := congrArg (fun f => f.app n e) (firstTargetMap_ι q hW hV)
    change ((firstTargetMap q hW hV).app n e).val =
      ((discreteSourceMappingMap q).app (op (Λ[2, 0] : SSet.{u}))).app n e.val at hi
    rw [hi] at h
    have hn := congrArg (fun f => f.app n b.val)
      ((discreteSourceMappingMap q).naturality (SSet.horn 2 0).ι.op)
    change ((discreteSourceMappingMap q).app (op (Λ[2, 0] : SSet.{u}))).app n
        (((discreteSourceMapping W).map (SSet.horn 2 0).ι.op).app n b.val) =
      ((discreteSourceMapping V).map (SSet.horn 2 0).ι.op).app n
        (((discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u}))).app n b.val) at hn
    change ((discreteSourceMapping V).map (SSet.horn 2 0).ι.op).app n
      (((discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u}))).app n b.val) ∈
        (firstTarget V hV).obj n
    rw [← hn]
    exact h)

/-- Every original target map carries the last-edge selected triangle to its actual counterpart. -/
def lastSourceMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    (lastSource W hW : SSet.{u}) ⟶ lastSource V hV :=
  SSet.Subcomplex.lift ((lastSource W hW).ι ≫
    (discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u}))) (by
    intro n a ha
    obtain ⟨b, rfl⟩ := ha
    let e : (lastTarget W hW : SSet.{u}).obj n :=
      ⟨((discreteSourceMapping W).map (SSet.horn 2 2).ι.op).app n b.val, b.property⟩
    have h := ((lastTargetMap q hW hV).app n e).property
    have hi := congrArg (fun f => f.app n e) (lastTargetMap_ι q hW hV)
    change ((lastTargetMap q hW hV).app n e).val =
      ((discreteSourceMappingMap q).app (op (Λ[2, 2] : SSet.{u}))).app n e.val at hi
    rw [hi] at h
    have hn := congrArg (fun f => f.app n b.val)
      ((discreteSourceMappingMap q).naturality (SSet.horn 2 2).ι.op)
    change ((discreteSourceMappingMap q).app (op (Λ[2, 2] : SSet.{u}))).app n
        (((discreteSourceMapping W).map (SSet.horn 2 2).ι.op).app n b.val) =
      ((discreteSourceMapping V).map (SSet.horn 2 2).ι.op).app n
        (((discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u}))).app n b.val) at hn
    change ((discreteSourceMapping V).map (SSet.horn 2 2).ι.op).app n
      (((discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u}))).app n b.val) ∈
        (lastTarget V hV).obj n
    rw [← hn]
    exact h)

/-- The first selected source map retains its exact original triangle-end inclusion. -/
@[reassoc (attr := simp)]
theorem firstSourceMap_ι {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    firstSourceMap q hW hV ≫ (firstSource V hV).ι =
      (firstSource W hW).ι ≫ (discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u})) := by
  unfold firstSourceMap
  exact SSet.Subcomplex.lift_ι _ _

/-- The last selected source map retains its exact original triangle-end inclusion. -/
@[reassoc (attr := simp)]
theorem lastSourceMap_ι {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    lastSourceMap q hW hV ≫ (lastSource V hV).ι =
      (lastSource W hW).ι ≫ (discreteSourceMappingMap q).app (op (Δ[2] : SSet.{u})) := by
  unfold lastSourceMap
  exact SSet.Subcomplex.lift_ι _ _

/-- The whole first-edge selected restriction is natural in every original target map. -/
theorem firstRestriction_target_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    firstSourceMap q hW hV ≫ firstRestriction V hV =
      firstRestriction W hW ≫ firstTargetMap q hW hV := by
  apply (cancel_mono (firstTarget V hV).ι).mp
  simp only [Category.assoc, firstRestriction_ι, firstRestriction_ι_assoc,
    firstSourceMap_ι_assoc, firstTargetMap_ι]
  simpa only [Category.assoc] using congrArg (fun f => (firstSource W hW).ι ≫ f)
    ((discreteSourceMappingMap q).naturality (SSet.horn 2 0).ι.op).symm

/-- The whole last-edge selected restriction is natural in every original target map. -/
theorem lastRestriction_target_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    lastSourceMap q hW hV ≫ lastRestriction V hV =
      lastRestriction W hW ≫ lastTargetMap q hW hV := by
  apply (cancel_mono (lastTarget V hV).ι).mp
  simp only [Category.assoc, lastRestriction_ι, lastRestriction_ι_assoc,
    lastSourceMap_ι_assoc, lastTargetMap_ι]
  simpa only [Category.assoc] using congrArg (fun f => (lastSource W hW).ι ≫ f)
    ((discreteSourceMappingMap q).naturality (SSet.horn 2 2).ι.op).symm

/-- The first selected restriction retains every original inner simplicial operator. -/
theorem firstRestriction_operator (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (a : (firstSource W hW : SSet.{u}).obj n) :
    (firstRestriction W hW).app m ((firstSource W hW : SSet.{u}).map θ a) =
      (firstTarget W hW : SSet.{u}).map θ ((firstRestriction W hW).app n a) :=
  (firstRestriction W hW).naturality_apply θ a

/-- The last selected restriction retains every original inner simplicial operator. -/
theorem lastRestriction_operator (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (a : (lastSource W hW : SSet.{u}).obj n) :
    (lastRestriction W hW).app m ((lastSource W hW : SSet.{u}).map θ a) =
      (lastTarget W hW : SSet.{u}).map θ ((lastRestriction W hW).app n a) :=
  (lastRestriction W hW).naturality_apply θ a

/-- The first all-edge target inclusion keeps the same whole target-map square. -/
theorem firstAllTargetInclusion_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    EquivalenceMapping.targetMap q hW hV (Λ[2, 0] : SSet.{u}) ≫ firstAllTargetInclusion V hV =
      firstAllTargetInclusion W hW ≫ firstTargetMap q hW hV := by
  apply (cancel_mono (firstTarget V hV).ι).mp
  simp only [Category.assoc, firstAllTargetInclusion_ι, firstTargetMap_ι,
    firstAllTargetInclusion_ι_assoc, EquivalenceMapping.targetMap_ι]

/-- The last all-edge target inclusion keeps the same whole target-map square. -/
theorem lastAllTargetInclusion_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    EquivalenceMapping.targetMap q hW hV (Λ[2, 2] : SSet.{u}) ≫ lastAllTargetInclusion V hV =
      lastAllTargetInclusion W hW ≫ lastTargetMap q hW hV := by
  apply (cancel_mono (lastTarget V hV).ι).mp
  simp only [Category.assoc, lastAllTargetInclusion_ι, lastTargetMap_ι,
    lastAllTargetInclusion_ι_assoc, EquivalenceMapping.targetMap_ι]

/-- The first all-edge source inclusion keeps the same whole target-map square. -/
theorem firstAllSourceInclusion_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    EquivalenceMapping.targetMap q hW hV Δ[2] ≫ firstAllSourceInclusion V hV =
      firstAllSourceInclusion W hW ≫ firstSourceMap q hW hV := by
  apply (cancel_mono (firstSource V hV).ι).mp
  simp only [Category.assoc, firstAllSourceInclusion_ι, firstSourceMap_ι,
    firstAllSourceInclusion_ι_assoc, EquivalenceMapping.targetMap_ι]

/-- The last all-edge source inclusion keeps the same whole target-map square. -/
theorem lastAllSourceInclusion_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    EquivalenceMapping.targetMap q hW hV Δ[2] ≫ lastAllSourceInclusion V hV =
      lastAllSourceInclusion W hW ≫ lastSourceMap q hW hV := by
  apply (cancel_mono (lastSource V hV).ι).mp
  simp only [Category.assoc, lastAllSourceInclusion_ι, lastSourceMap_ι,
    lastAllSourceInclusion_ι_assoc, EquivalenceMapping.targetMap_ι]

end SimplicialSpace.DecoratedOuterTwoHorn
