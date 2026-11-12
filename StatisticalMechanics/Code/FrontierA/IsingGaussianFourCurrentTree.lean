/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianFiniteCurrentUrsell
import Code.FrontierA.GrahamWeightedAuxiliaryAlgebra











open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def finiteTreeMixedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = grahamPairSupport k l
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i k
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = ∅
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0))



noncomputable def finiteTreeSeparatedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0) *
      (if CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
        then 1 else 0))



theorem finiteTreeMixedFourMass_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    finiteTreeMixedFourMass G beta J i j k l =
      gatedSourcePairSum G beta J (grahamPairSupport i j)
          (grahamPairSupport k l)
          (fun n => CurrentConnected G n i k) *
        currentSum G beta J ∅ ^ 2 := by
  let P : Current V -> Prop := fun n => CurrentConnected G n i k
  have hpairs := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport i j) (grahamPairSupport k l) P
  have hvac := summable_gatedSourcePairSummand G beta J ∅ ∅ (fun _ => True)
  have hprod := summable_mul_of_summable_norm hpairs.norm hvac.norm
  rw [pow_two, ← sourcePairSum_eq_mul, ← gatedSourcePairSum_true]
  unfold finiteTreeMixedFourMass gatedSourcePairSum
  rw [Summable.tsum_mul_tsum hpairs hvac hprod]
  apply tsum_congr
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [P, if_true, mul_one]



theorem finiteTreeMixedFourMass_eq_allThree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l =
      gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun n => grahamAllThreeConnected G n i j k l) *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTreeMixedFourMass_eq]
  have hij' : grahamPairSupport i j = {i, j} := by
    ext x
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm]
  have hkl' : grahamPairSupport k l = {k, l} := by
    ext x
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    by_cases hxk : x = k <;> by_cases hxl : x = l <;> simp_all [eq_comm]
  rw [hij', hkl', ← gc37_sourcePairConnSum_eq_gated]
  rw [← grahamAllThreeMass_eq_pairConnectionMass G beta J
    hij hik hil hjk hjl hkl]



theorem finiteTreeSeparatedFourMass_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) :
    finiteTreeSeparatedFourMass G beta J i j k l y =
      gatedSourcePairSum G beta J (grahamPairSupport i j) ∅
          (fun n => CurrentConnected G n i y) *
        gatedSourcePairSum G beta J (grahamPairSupport k l) ∅
          (fun n => CurrentConnected G n k y) := by
  let P : Current V -> Prop := fun n => CurrentConnected G n i y
  let Q : Current V -> Prop := fun n => CurrentConnected G n k y
  have hleft := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport i j) ∅ P
  have hright := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport k l) ∅ Q
  have hprod := summable_mul_of_summable_norm hleft.norm hright.norm
  unfold finiteTreeSeparatedFourMass gatedSourcePairSum
  rw [Summable.tsum_mul_tsum hleft hright hprod]



theorem finiteTreeSeparatedFourMass_eq_twoPointMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) :
    finiteTreeSeparatedFourMass G beta J i j k l y =
      currentSum G beta J (grahamPairSupport i y) *
        currentSum G beta J (grahamPairSupport j y) *
        currentSum G beta J (grahamPairSupport k y) *
        currentSum G beta J (grahamPairSupport l y) := by
  rw [finiteTreeSeparatedFourMass_eq,
    gatedPairConnection_eq_twoPointMass,
    gatedPairConnection_eq_twoPointMass]
  have hjy : grahamPairSupport y j = grahamPairSupport j y := by
    unfold grahamPairSupport
    rw [symmDiff_comm]
  have hly : grahamPairSupport y l = grahamPairSupport l y := by
    unfold grahamPairSupport
    rw [symmDiff_comm]
  rw [hjy, hly]
  ring



theorem sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y =
      finiteCurrentTreeDiagramMass G beta J i j k l := by
  unfold finiteCurrentTreeDiagramMass
  apply Finset.sum_congr rfl
  intro y _
  exact finiteTreeSeparatedFourMass_eq_twoPointMass G beta J i j k l y

end StatMech.FrontierA
