/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.KacWardPortChainEvenPolynomial
import Code.FrontierA.SurfaceKacWardTwist









open scoped BigOperators

namespace StatMech.FrontierA

open Finset SimpleGraph

noncomputable section


def kwOrderedSplitEdgeClass
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology 1) :
    Sym2 (KWDartPort G) → SurfaceHomology 1 :=
  fun edge => edgeClass (kwOrderedSplitEdgeProjection edge)

private theorem fin2_complexSign_injective :
    Function.Injective (fun z : Fin 2 => (surfaceParitySign z : Complex)) := by
  intro x y h
  have hx : x = 0 ∨ x = 1 := by omega
  have hy : y = 0 ∨ y = 1 := by omega
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · rfl
    · norm_num [surfaceParitySign] at h
  · rcases hy with rfl | rfl
    · norm_num [surfaceParitySign] at h
    · rfl

private theorem surfaceHomology_one_ext_character
    {h k : SurfaceHomology 1}
    (hchar : ∀ lambda : SurfaceSpinStructure 1,
      surfaceHomologyCharacter lambda h =
        surfaceHomologyCharacter lambda k) : h = k := by
  apply Prod.ext
  · funext i
    fin_cases i
    apply fin2_complexSign_injective
    simpa [surfaceHomologyCharacter, surfaceSpinLinearParity,
      Fin.sum_univ_one] using
      hchar ((fun _ => 1), (fun _ => 0))
  · funext i
    fin_cases i
    apply fin2_complexSign_injective
    simpa [surfaceHomologyCharacter, surfaceSpinLinearParity,
      Fin.sum_univ_one] using
      hchar ((fun _ => 0), (fun _ => 1))

private theorem kwOrderedSplitWeight_character
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (edgeClass : Sym2 V → SurfaceHomology 1)
    (hdiag : ∀ v, edgeClass s(v, v) = 0)
    (lambda : SurfaceSpinStructure 1)
    {edge : Sym2 (KWDartPort G)}
    (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset) :
    kwOrderedSplitWeight G
        (fun e => surfaceHomologyCharacter lambda (edgeClass e)) edge =
      surfaceHomologyCharacter lambda (kwOrderedSplitEdgeClass edgeClass edge) := by
  by_cases hd : (kwOrderedSplitEdgeProjection edge).IsDiag
  · induction edge using Sym2.inductionOn with
    | _ p q =>
      rw [kwOrderedSplitEdgeProjection_mk, Sym2.mk_isDiag_iff] at hd
      rw [kwOrderedSplitWeight_eq_one_of_projection_diag G _
        (by simpa [kwOrderedSplitEdgeProjection_mk] using hd)]
      rw [kwOrderedSplitEdgeClass, kwOrderedSplitEdgeProjection_mk,
        hd, hdiag, surfaceHomologyCharacter_zero]
  · rw [kwOrderedSplitWeight_eq_projection_of_not_diag
      G order _ hedge hd]
    rfl



theorem kwOrderedSplitEdges_surfaceSubgraphHomology
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (edgeClass : Sym2 V → SurfaceHomology 1)
    (hdiag : ∀ v, edgeClass s(v, v) = 0)
    (b : KWDartEdgeBits G) (y : KWPortChainField G) :
    surfaceSubgraphHomology (kwOrderedSplitEdgeClass edgeClass)
        (kwOrderedSplitEdges G order b y) =
      surfaceSubgraphHomology edgeClass (kwDartEdgeBitsFinset G b) := by
  apply surfaceHomology_one_ext_character
  intro lambda
  unfold surfaceSubgraphHomology
  rw [surfaceHomologyCharacter_finset_sum,
    surfaceHomologyCharacter_finset_sum]
  calc
    (∏ edge ∈ kwOrderedSplitEdges G order b y,
        surfaceHomologyCharacter lambda
          (kwOrderedSplitEdgeClass edgeClass edge)) =
        ∏ edge ∈ kwOrderedSplitEdges G order b y,
          kwOrderedSplitWeight G
            (fun e => surfaceHomologyCharacter lambda (edgeClass e)) edge := by
      apply Finset.prod_congr rfl
      intro edge hedge
      symm
      apply kwOrderedSplitWeight_character G order edgeClass hdiag lambda
      exact (Finset.filter_subset _ _) hedge
    _ = ∏ edge ∈ kwDartEdgeBitsFinset G b,
          surfaceHomologyCharacter lambda (edgeClass edge) :=
      kwOrderedSplitEdges_weight_prod G order
        (fun e => surfaceHomologyCharacter lambda (edgeClass e)) b y



theorem surfaceQuadraticEvenPolynomial_eq_sum_actual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1) (weight : Sym2 V → Complex) :
    surfaceQuadraticEvenPolynomial G edgeClass lambda weight =
      ∑ F : KWActualEvenSubgraph G,
        (surfaceParitySign
          (surfaceQuadraticParity lambda
            (surfaceSubgraphHomology edgeClass F.1)) : Complex) *
          ∏ edge ∈ F.1, weight edge := by
  unfold surfaceQuadraticEvenPolynomial KWActualEvenSubgraph
  exact Finset.sum_subtype
    (G.edgeFinset.powerset.filter StatMech.Ising.IsEvenSubgraph)
    (fun F => Iff.rfl)
    (fun F =>
      (surfaceParitySign
        (surfaceQuadraticParity lambda
          (surfaceSubgraphHomology edgeClass F)) : Complex) *
        ∏ edge ∈ F, weight edge)



theorem kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (edgeClass : Sym2 V → SurfaceHomology 1)
    (hdiag : ∀ v, edgeClass s(v, v) = 0)
    (lambda : SurfaceSpinStructure 1) (weight : Sym2 V → Complex) :
    surfaceQuadraticEvenPolynomial (kwOrderedDartPortSplitGraph G order)
        (kwOrderedSplitEdgeClass edgeClass) lambda
        (kwOrderedSplitWeight G weight) =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  rw [surfaceQuadraticEvenPolynomial_eq_sum_actual,
    surfaceQuadraticEvenPolynomial_eq_sum_actual]
  symm
  apply Fintype.sum_equiv (kwOrderedSplitEvenSubgraphEquiv G order)
  intro F
  have hdata := F.2
  change F.1 ∈ G.edgeFinset.powerset.filter
    StatMech.Ising.IsEvenSubgraph at hdata
  rw [Finset.mem_filter, Finset.mem_powerset] at hdata
  let b := kwFinsetDartEdgeBits G F.1
  let y := kwOrderedCanonicalPortChainField G order b
  have hhom := kwOrderedSplitEdges_surfaceSubgraphHomology
    G order edgeClass hdiag b y
  have hprod := kwOrderedSplitEdges_weight_prod G order weight b y
  have hFset : kwDartEdgeBitsFinset G b = F.1 :=
    kwDartEdgeBitsFinset_finset G F.1 hdata.1
  rw [hFset] at hhom hprod
  simpa [kwOrderedSplitEvenSubgraphEquiv,
    kwActualEvenSubgraphEquivBits, kwOriginalEvenBitsEquivOrderedSplit,
    kwActualOrderedSplitEvenEquivBits, Equiv.trans_apply, b, y,
    hhom, hprod]

end

end StatMech.FrontierA
