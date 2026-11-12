/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Code.FrontierD.FKRectBlackOrbitRibbonPrimitive
import Code.FrontierD.FKRectZeroTurnDevelopedAnchor



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section

def fkRectBoundaryMergeOldWinding0
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))

def fkRectBoundaryMergeOldWinding1
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))

def fkRectBoundaryMergeNewWinding
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R (insert e F)))
    (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))

def fkRectBoundarySplitNewWinding1
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R (insert e F)))
    (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))




theorem fkRectBoundaryMerge_sameSign_dependent_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hmerge : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (hnonzero0 : fkRectBoundaryMergeOldWinding0 R F e ≠ 0)
    (hnonzero1 : fkRectBoundaryMergeOldWinding1 R F e ≠ 0)
    (hdependent : ¬ FKRectWindingIndependent
      (fkRectBoundaryMergeOldWinding0 R F e)
      (fkRectBoundaryMergeOldWinding1 R F e))
    (hsign :
      0 < (fkRectBoundaryMergeOldWinding0 R F e).1 *
          (fkRectBoundaryMergeOldWinding1 R F e).1 ∨
      0 < (fkRectBoundaryMergeOldWinding0 R F e).2 *
          (fkRectBoundaryMergeOldWinding1 R F e).2) :
    False := by
  let u := fkRectBoundaryMergeOldWinding0 R F e
  let v := fkRectBoundaryMergeOldWinding1 R F e
  have hu : FKRectPrimitiveWinding u := by
    unfold u fkRectBoundaryMergeOldWinding0
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact hnonzero0
  have hv : FKRectPrimitiveWinding v := by
    unfold v fkRectBoundaryMergeOldWinding1
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact hnonzero1
  have hnotPrimitive : ¬ FKRectPrimitiveWinding (u + v) :=
    not_primitiveWinding_add_of_primitive_dependent_sameSign
      hu hv (by exact hdependent) (by exact hsign)
  have hsumNonzero : u + v ≠ 0 := by
    intro hzero
    have hfst := congrArg Prod.fst hzero
    have hsnd := congrArg Prod.snd hzero
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero,
      Prod.snd_zero] at hfst hsnd
    rcases hsign with hsign | hsign
    · change 0 < u.1 * v.1 at hsign
      have hvfst : v.1 = -u.1 := by omega
      rw [hvfst] at hsign
      nlinarith [sq_nonneg u.1]
    · change 0 < u.2 * v.2 at hsign
      have hvsnd : v.2 = -u.2 := by omega
      rw [hvsnd] at hsign
      nlinarith [sq_nonneg u.2]
  have hmerged : fkRectBoundaryMergeNewWinding R F e = u + v := by
    exact fkRectBlackBoundaryCycleClassWinding_insert_of_not_reachable
      R F e heF hmerge
  have hnewNonzero : fkRectBoundaryMergeNewWinding R F e ≠ 0 := by
    rw [hmerged]
    exact hsumNonzero
  have hnewPrimitive : FKRectPrimitiveWinding
      (fkRectBoundaryMergeNewWinding R F e) := by
    unfold fkRectBoundaryMergeNewWinding
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact hnewNonzero
  apply hnotPrimitive
  rw [← hmerged]
  exact hnewPrimitive



theorem fkRectBoundarySplit_sameSign_dependent_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsplit : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (hnonzero0 : fkRectBoundaryMergeNewWinding R F e ≠ 0)
    (hnonzero1 : fkRectBoundarySplitNewWinding1 R F e ≠ 0)
    (hdependent : ¬ FKRectWindingIndependent
      (fkRectBoundaryMergeNewWinding R F e)
      (fkRectBoundarySplitNewWinding1 R F e))
    (hsign :
      0 < (fkRectBoundaryMergeNewWinding R F e).1 *
          (fkRectBoundarySplitNewWinding1 R F e).1 ∨
      0 < (fkRectBoundaryMergeNewWinding R F e).2 *
          (fkRectBoundarySplitNewWinding1 R F e).2) :
    False := by
  let u := fkRectBoundaryMergeNewWinding R F e
  let v := fkRectBoundarySplitNewWinding1 R F e
  have hu : FKRectPrimitiveWinding u := by
    unfold u fkRectBoundaryMergeNewWinding
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact hnonzero0
  have hv : FKRectPrimitiveWinding v := by
    unfold v fkRectBoundarySplitNewWinding1
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact hnonzero1
  have hnotPrimitive : ¬ FKRectPrimitiveWinding (u + v) :=
    not_primitiveWinding_add_of_primitive_dependent_sameSign
      hu hv (by exact hdependent) (by exact hsign)
  have hsumNonzero : u + v ≠ 0 := by
    intro hzero
    have hfst := congrArg Prod.fst hzero
    have hsnd := congrArg Prod.snd hzero
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero,
      Prod.snd_zero] at hfst hsnd
    rcases hsign with hsign | hsign
    · change 0 < u.1 * v.1 at hsign
      have hvfst : v.1 = -u.1 := by omega
      rw [hvfst] at hsign
      nlinarith [sq_nonneg u.1]
    · change 0 < u.2 * v.2 at hsign
      have hvsnd : v.2 = -u.2 := by omega
      rw [hvsnd] at hsign
      nlinarith [sq_nonneg u.2]
  have hwinding : fkRectBoundaryMergeOldWinding0 R F e = u + v := by
    exact fkRectBlackBoundaryCycleClassWinding_split_of_reachable
      R F e heF hsplit
  have holdNonzero : fkRectBoundaryMergeOldWinding0 R F e ≠ 0 := by
    rw [hwinding]
    exact hsumNonzero
  have holdPrimitive : FKRectPrimitiveWinding
      (fkRectBoundaryMergeOldWinding0 R F e) := by
    unfold fkRectBoundaryMergeOldWinding0
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact holdNonzero
  apply hnotPrimitive
  rw [← hwinding]
  exact holdPrimitive



theorem fkRectBoundarySplit_nonzero_winding_persists_exactly_one
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsplit : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (holdNonzero : fkRectBoundaryMergeOldWinding0 R F e ≠ 0)
    (hdependent : ¬ FKRectWindingIndependent
      (fkRectBoundaryMergeNewWinding R F e)
      (fkRectBoundarySplitNewWinding1 R F e)) :
    (fkRectBoundaryMergeNewWinding R F e = 0 ∧
        fkRectBoundarySplitNewWinding1 R F e =
          fkRectBoundaryMergeOldWinding0 R F e) ∨
      (fkRectBoundaryMergeNewWinding R F e =
          fkRectBoundaryMergeOldWinding0 R F e ∧
        fkRectBoundarySplitNewWinding1 R F e = 0) := by
  let u := fkRectBoundaryMergeOldWinding0 R F e
  let v := fkRectBoundaryMergeNewWinding R F e
  let w := fkRectBoundarySplitNewWinding1 R F e
  have hu : FKRectPrimitiveWinding u := by
    unfold u fkRectBoundaryMergeOldWinding0
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact holdNonzero
  have hv : v = 0 ∨ FKRectPrimitiveWinding v := by
    by_cases hzero : v = 0
    · exact Or.inl hzero
    · right
      unfold v fkRectBoundaryMergeNewWinding
      rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      apply fkRectBlackBoundaryPrimalCycleWinding_primitive
      rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      exact hzero
  have hw : w = 0 ∨ FKRectPrimitiveWinding w := by
    by_cases hzero : w = 0
    · exact Or.inl hzero
    · right
      unfold w fkRectBoundarySplitNewWinding1
      rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      apply fkRectBlackBoundaryPrimalCycleWinding_primitive
      rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      exact hzero
  have hsum : u = v + w := by
    exact fkRectBlackBoundaryCycleClassWinding_split_of_reachable
      R F e heF hsplit
  have hvw : v.1 * w.2 - v.2 * w.1 = 0 := by
    unfold FKRectWindingIndependent at hdependent
    push Not at hdependent
    exact hdependent
  have hdepv : ¬ FKRectWindingIndependent u v := by
    unfold FKRectWindingIndependent
    push Not
    have hfst := congrArg Prod.fst hsum
    have hsnd := congrArg Prod.snd hsum
    simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
    rw [hfst, hsnd]
    linear_combination -hvw
  have hdepw : ¬ FKRectWindingIndependent u w := by
    unfold FKRectWindingIndependent
    push Not
    have hfst := congrArg Prod.fst hsum
    have hsnd := congrArg Prod.snd hsum
    simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
    rw [hfst, hsnd]
    linear_combination hvw
  exact primitiveWinding_split_eq_zero_or_eq hu hsum hv hw hdepv hdepw



theorem fkRectBoundaryMerge_nonzero_winding_from_exactly_one
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hmerge : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (hnewNonzero : fkRectBoundaryMergeNewWinding R F e ≠ 0)
    (hdependent : ¬ FKRectWindingIndependent
      (fkRectBoundaryMergeOldWinding0 R F e)
      (fkRectBoundaryMergeOldWinding1 R F e)) :
    (fkRectBoundaryMergeOldWinding0 R F e = 0 ∧
        fkRectBoundaryMergeOldWinding1 R F e =
          fkRectBoundaryMergeNewWinding R F e) ∨
      (fkRectBoundaryMergeOldWinding0 R F e =
          fkRectBoundaryMergeNewWinding R F e ∧
        fkRectBoundaryMergeOldWinding1 R F e = 0) := by
  let u := fkRectBoundaryMergeNewWinding R F e
  let v := fkRectBoundaryMergeOldWinding0 R F e
  let w := fkRectBoundaryMergeOldWinding1 R F e
  have hu : FKRectPrimitiveWinding u := by
    unfold u fkRectBoundaryMergeNewWinding
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    apply fkRectBlackBoundaryPrimalCycleWinding_primitive
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact hnewNonzero
  have hv : v = 0 ∨ FKRectPrimitiveWinding v := by
    by_cases hzero : v = 0
    · exact Or.inl hzero
    · right
      unfold v fkRectBoundaryMergeOldWinding0
      rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      apply fkRectBlackBoundaryPrimalCycleWinding_primitive
      rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      exact hzero
  have hw : w = 0 ∨ FKRectPrimitiveWinding w := by
    by_cases hzero : w = 0
    · exact Or.inl hzero
    · right
      unfold w fkRectBoundaryMergeOldWinding1
      rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      apply fkRectBlackBoundaryPrimalCycleWinding_primitive
      rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
      exact hzero
  have hsum : u = v + w := by
    exact fkRectBlackBoundaryCycleClassWinding_insert_of_not_reachable
      R F e heF hmerge
  have hvw : v.1 * w.2 - v.2 * w.1 = 0 := by
    unfold FKRectWindingIndependent at hdependent
    push Not at hdependent
    exact hdependent
  have hdepv : ¬ FKRectWindingIndependent u v := by
    unfold FKRectWindingIndependent
    push Not
    have hfst := congrArg Prod.fst hsum
    have hsnd := congrArg Prod.snd hsum
    simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
    rw [hfst, hsnd]
    linear_combination -hvw
  have hdepw : ¬ FKRectWindingIndependent u w := by
    unfold FKRectWindingIndependent
    push Not
    have hfst := congrArg Prod.fst hsum
    have hsnd := congrArg Prod.snd hsum
    simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
    rw [hfst, hsnd]
    linear_combination hvw
  exact primitiveWinding_split_eq_zero_or_eq hu hsum hv hw hdepv hdepw

end

end StatMech.FrontierD
