/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianFourColorFamilies
import Code.FrontierA.IsingGaussianFourCurrentTree
import Code.FrontierA.GrahamFourColorEdgecopyBridge
import Code.FrontierA.GrahamWeightedLemmaOneResummation
import Code.FrontierA.GrahamWeightedLemmaOneCardBridge










open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeFourCurrentPatternSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop)
    (z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat))) : Real :=
  weight G beta J (ofEdgeFun G z.1.1) *
    weight G beta J (ofEdgeFun G z.1.2) *
    weight G beta J (ofEdgeFun G z.2.1) *
    weight G beta J (ofEdgeFun G z.2.2) *
    (if P z.1.1 z.1.2 z.2.1 z.2.2 then 1 else 0)



noncomputable def finiteTreeFourColorCoefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat)
    (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop) : Real :=
  ∑ split : GrahamFourSplit G total,
    grahamFourSplitMultiplicity G total split *
      (if P split.1.1 split.1.2.1 split.1.2.2
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)
        then 1 else 0)




theorem finiteTreeFourCurrentPattern_resum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (P : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> Prop)
    (hsum : Summable (finiteTreeFourCurrentPatternSummand G beta J P))
    (hnonneg : ∀ z, 0 <= finiteTreeFourCurrentPatternSummand G beta J P z) :
    Summable (fun total : G.edgeFinset -> Nat =>
      finiteTreeFourColorCoefficient G total P *
        weight G beta J (ofEdgeFun G total)) ∧
      (∑' z, finiteTreeFourCurrentPatternSummand G beta J P z) =
        ∑' total : G.edgeFinset -> Nat,
          finiteTreeFourColorCoefficient G total P *
            weight G beta J (ofEdgeFun G total) := by
  let Q := grahamPairPairEquivSigma (E := G.edgeFinset)
  let f := finiteTreeFourCurrentPatternSummand G beta J P
  have hF : Summable (fun s => f (Q.symm s)) :=
    Q.symm.summable_iff.mpr hsum
  have hFnonneg : ∀ s, 0 <= f (Q.symm s) := fun s => hnonneg _
  have houter : Summable (fun total =>
      ∑' split : GrahamFourSplit G total, f (Q.symm ⟨total, split⟩)) :=
    (summable_sigma_of_nonneg hFnonneg).mp hF |>.2
  have hfiber (total : G.edgeFinset -> Nat) :
      (∑' split : GrahamFourSplit G total, f (Q.symm ⟨total, split⟩)) =
        finiteTreeFourColorCoefficient G total P *
          weight G beta J (ofEdgeFun G total) := by
    rw [tsum_fintype]
    unfold finiteTreeFourColorCoefficient
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro split hsplit
    change finiteTreeFourCurrentPatternSummand G beta J P
        (Q.symm ⟨total, split⟩) = _
    dsimp [finiteTreeFourCurrentPatternSummand, Q,
      grahamPairPairEquivSigma, grahamQuadEquivSigma,
      grahamFourthProfile]
    rw [show grahamFourthProfile total split.1.1 split.1.2.1
        split.1.2.2 =
        (fun e => total e - split.1.1 e - split.1.2.1 e - split.1.2.2 e) by
      rfl]
    rw [grahamWeight_split4_eq_binom G beta J total
      split.1.1 split.1.2.1 split.1.2.2 split.2]
    simp only [grahamFourSplitMultiplicity]
    ring
  have hcoeff : Summable (fun total : G.edgeFinset -> Nat =>
      finiteTreeFourColorCoefficient G total P *
        weight G beta J (ofEdgeFun G total)) :=
    houter.congr hfiber
  refine ⟨hcoeff, ?_⟩
  change (∑' z, f z) = _
  calc
    (∑' z, f z) = ∑' z, f (Q.symm (Q z)) := by
      apply tsum_congr
      intro z
      rw [Equiv.symm_apply_apply]
    _ = ∑' s, f (Q.symm s) := Q.tsum_eq (fun s => f (Q.symm s))
    _ = ∑' total, ∑' split : GrahamFourSplit G total,
        f (Q.symm ⟨total, split⟩) := by
      exact hF.tsum_sigma
    _ = _ := by
      apply tsum_congr
      exact hfiber


def finiteTreeMixedCurrentPattern
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j k l : V)
    (a b c d : G.edgeFinset -> Nat) : Prop :=
  sources G (ofEdgeFun G a) = {i, j} ∧
    sources G (ofEdgeFun G b) = {k, l} ∧
    sources G (ofEdgeFun G c) = ∅ ∧
    sources G (ofEdgeFun G d) = ∅ ∧
    CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) i k


def finiteTreeSeparatedCurrentPattern
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j k l y : V)
    (a b c d : G.edgeFinset -> Nat) : Prop :=
  sources G (ofEdgeFun G a) = {i, j} ∧
    sources G (ofEdgeFun G b) = ∅ ∧
    sources G (ofEdgeFun G c) = {k, l} ∧
    sources G (ofEdgeFun G d) = ∅ ∧
    CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) i y ∧
    CurrentConnected G (ofEdgeFun G (fun e => c e + d e)) k y

private theorem finiteTreePairSupport_eq_pair {x y : V} (hxy : x ≠ y) :
    grahamPairSupport x y = {x, y} := by
  ext z
  simp only [grahamPairSupport, Finset.mem_symmDiff,
    Finset.mem_singleton, Finset.mem_insert]
  by_cases hzx : z = x <;> by_cases hzy : z = y <;>
    simp_all [eq_comm]



theorem finiteTreeMixedFourMass_resum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    Summable (fun total : G.edgeFinset -> Nat =>
      finiteTreeFourColorCoefficient G total
          (finiteTreeMixedCurrentPattern G i j k l) *
        weight G beta J (ofEdgeFun G total)) ∧
      finiteTreeMixedFourMass G beta J i j k l =
        ∑' total : G.edgeFinset -> Nat,
          finiteTreeFourColorCoefficient G total
              (finiteTreeMixedCurrentPattern G i j k l) *
            weight G beta J (ofEdgeFun G total) := by
  let P := finiteTreeMixedCurrentPattern G i j k l
  have hij' := finiteTreePairSupport_eq_pair hij
  have hkl' := finiteTreePairSupport_eq_pair hkl
  let C : Current V -> Prop := fun n => CurrentConnected G n i k
  have hpair := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport i j) (grahamPairSupport k l) C
  have hvac := summable_gatedSourcePairSummand G beta J ∅ ∅ (fun _ => True)
  have hprod := summable_mul_of_summable_norm hpair.norm hvac.norm
  have hpoint : ∀ z,
      finiteTreeFourCurrentPatternSummand G beta J P z =
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
            then weight G beta J (ofEdgeFun G z.2.2) else 0)) := by
    intro z
    unfold finiteTreeFourCurrentPatternSummand
    dsimp only [P]
    simp only [finiteTreeMixedCurrentPattern, hij', hkl']
    by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
      by_cases h2 : sources G (ofEdgeFun G z.1.2) = {k, l} <;>
      by_cases h3 : sources G (ofEdgeFun G z.2.1) = ∅ <;>
      by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅ <;>
      by_cases h5 : CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i k <;>
      simp [h1, h2, h3, h4, h5] <;> ring
  have hsum : Summable
      (finiteTreeFourCurrentPatternSummand G beta J P) := by
    apply hprod.congr
    intro z
    dsimp only [C]
    simp only [if_true, mul_one]
    exact (hpoint z).symm
  have hnonneg : ∀ z,
      0 <= finiteTreeFourCurrentPatternSummand G beta J P z := by
    intro z
    unfold finiteTreeFourCurrentPatternSummand
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _)
            (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _))
          (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _))
        (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _))
      (by split <;> norm_num)
  have hres := finiteTreeFourCurrentPattern_resum G beta J P hsum hnonneg
  refine ⟨by simpa only [P] using hres.1, ?_⟩
  calc
    finiteTreeMixedFourMass G beta J i j k l =
        ∑' z, finiteTreeFourCurrentPatternSummand G beta J P z := by
      unfold finiteTreeMixedFourMass
      apply tsum_congr
      intro z
      exact (hpoint z).symm
    _ = _ := by simpa only [P] using hres.2



theorem finiteTreeSeparatedFourMass_resum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) (y : V) :
    Summable (fun total : G.edgeFinset -> Nat =>
      finiteTreeFourColorCoefficient G total
          (finiteTreeSeparatedCurrentPattern G i j k l y) *
        weight G beta J (ofEdgeFun G total)) ∧
      finiteTreeSeparatedFourMass G beta J i j k l y =
        ∑' total : G.edgeFinset -> Nat,
          finiteTreeFourColorCoefficient G total
              (finiteTreeSeparatedCurrentPattern G i j k l y) *
            weight G beta J (ofEdgeFun G total) := by
  let P := finiteTreeSeparatedCurrentPattern G i j k l y
  have hij' := finiteTreePairSupport_eq_pair hij
  have hkl' := finiteTreePairSupport_eq_pair hkl
  let C : Current V -> Prop := fun n => CurrentConnected G n i y
  let D : Current V -> Prop := fun n => CurrentConnected G n k y
  have hleft := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport i j) ∅ C
  have hright := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport k l) ∅ D
  have hprod := summable_mul_of_summable_norm hleft.norm hright.norm
  have hpoint : ∀ z,
      finiteTreeFourCurrentPatternSummand G beta J P z =
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
            then 1 else 0)) := by
    intro z
    unfold finiteTreeFourCurrentPatternSummand
    dsimp only [P]
    simp only [finiteTreeSeparatedCurrentPattern, hij', hkl']
    by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
      by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
      by_cases h3 : sources G (ofEdgeFun G z.2.1) = {k, l} <;>
      by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅ <;>
      by_cases h5 : CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y <;>
      by_cases h6 : CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y <;>
      simp [h1, h2, h3, h4, h5, h6] <;> ring
  have hsum : Summable
      (finiteTreeFourCurrentPatternSummand G beta J P) := by
    apply hprod.congr
    intro z
    dsimp only [C, D]
    exact (hpoint z).symm
  have hnonneg : ∀ z,
      0 <= finiteTreeFourCurrentPatternSummand G beta J P z := by
    intro z
    unfold finiteTreeFourCurrentPatternSummand
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _)
            (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _))
          (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _))
        (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _))
      (by split <;> norm_num)
  have hres := finiteTreeFourCurrentPattern_resum G beta J P hsum hnonneg
  refine ⟨by simpa only [P] using hres.1, ?_⟩
  calc
    finiteTreeSeparatedFourMass G beta J i j k l y =
        ∑' z, finiteTreeFourCurrentPatternSummand G beta J P z := by
      unfold finiteTreeSeparatedFourMass
      apply tsum_congr
      intro z
      exact (hpoint z).symm
    _ = _ := by simpa only [P] using hres.2

set_option maxHeartbeats 4000000 in

private theorem finiteTreeMixedProfileIndicator_eq_mem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (i j k l : V)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    (if finiteTreeMixedCurrentPattern G i j k l
          (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3)
          (grahamFourthProfile total
            (profileFlux G total q.color1)
            (profileFlux G total q.color2)
            (profileFlux G total q.color3))
      then (1 : Real) else 0) =
      if q ∈ finiteTreeMixedColorings (endsM G total)
          Finset.univ i j k l then (1 : Real) else 0 := by
  have h4 : grahamFourthProfile total
      (profileFlux G total q.color1)
      (profileFlux G total q.color2)
      (profileFlux G total q.color3) =
      profileFlux G total (q.color4 Finset.univ) := by
    symm
    exact grahamFourColor_profile_color4 G total q hq
  have h12 : Disjoint q.color1 q.color2 := hq.2.2.2.1
  have hp12 := graham_profileFlux_union_disjoint G total
    q.color1 q.color2 h12
  have hc12 : CurrentConnected G
      (ofEdgeFun G (fun e => profileFlux G total q.color1 e +
        profileFlux G total q.color2 e)) i k ↔
      connK (endsM G total) (q.color1 ∪ q.color2) i k := by
    rw [connK_iff, hp12]
  simp only [mem_finiteTreeMixedColorings, hq, true_and]
  unfold finiteTreeMixedCurrentPattern
  rw [← sources_eq G total q.color1,
    ← sources_eq G total q.color2,
    ← sources_eq G total q.color3, h4,
    ← sources_eq G total (q.color4 Finset.univ)]
  by_cases h1 : RandomCurrent.sources (endsM G total) q.color1 = {i, j} <;>
    by_cases h2 : RandomCurrent.sources (endsM G total) q.color2 = {k, l} <;>
    by_cases h3 : RandomCurrent.sources (endsM G total) q.color3 = ∅ <;>
    by_cases h4s : RandomCurrent.sources (endsM G total)
      (q.color4 Finset.univ) = ∅ <;>
    by_cases h5 : connK (endsM G total) (q.color1 ∪ q.color2) i k <;>
    simp [h1, h2, h3, h4s, h5, hc12]

set_option maxHeartbeats 4000000 in



theorem finiteTreeMixedFourColorCoefficient_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (i j k l : V) :
    finiteTreeFourColorCoefficient G total
        (finiteTreeMixedCurrentPattern G i j k l) =
      (#(finiteTreeMixedColorings (endsM G total)
        Finset.univ i j k l) : Real) := by
  let Theta : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> Real := fun a b c =>
    if finiteTreeMixedCurrentPattern G i j k l a b c
        (grahamFourthProfile total a b c) then 1 else 0
  have hbridge := grahamFourColor_edgecopy_bridge
    (M := Real) G total Theta
  calc
    finiteTreeFourColorCoefficient G total
        (finiteTreeMixedCurrentPattern G i j k l) =
        ∑ s : GrahamFourSplit G total,
          grahamFourSplitMultiplicityNat G total s •
            Theta s.1.1 s.1.2.1 s.1.2.2 := by
      unfold finiteTreeFourColorCoefficient
      apply Finset.sum_congr rfl
      intro s hs
      rw [grahamFourSplitMultiplicity_eq_natCast G total s]
      simp only [Theta, nsmul_eq_mul]
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        Theta (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3) := hbridge
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        (if q ∈ finiteTreeMixedColorings (endsM G total)
            Finset.univ i j k l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      change (if finiteTreeMixedCurrentPattern G i j k l
          (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3)
          (grahamFourthProfile total
            (profileFlux G total q.color1)
            (profileFlux G total q.color2)
            (profileFlux G total q.color3))
        then (1 : Real) else 0) = _
      exact finiteTreeMixedProfileIndicator_eq_mem
        G total i j k l q (by simpa using hq)
    _ = (#(finiteTreeMixedColorings (endsM G total)
        Finset.univ i j k l) : Real) := by
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Finset.filter_subset _ _ h, h⟩

set_option maxHeartbeats 4000000 in

private theorem finiteTreeSeparatedProfileIndicator_eq_mem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (i j k l y : V)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    (if finiteTreeSeparatedCurrentPattern G i j k l y
          (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3)
          (grahamFourthProfile total
            (profileFlux G total q.color1)
            (profileFlux G total q.color2)
            (profileFlux G total q.color3))
      then (1 : Real) else 0) =
      if q ∈ finiteTreeSeparatedBranchColorings (endsM G total)
          Finset.univ i j k l y then (1 : Real) else 0 := by
  have h4 : grahamFourthProfile total
      (profileFlux G total q.color1)
      (profileFlux G total q.color2)
      (profileFlux G total q.color3) =
      profileFlux G total (q.color4 Finset.univ) := by
    symm
    exact grahamFourColor_profile_color4 G total q hq
  have h12 : Disjoint q.color1 q.color2 := hq.2.2.2.1
  have hp12 := graham_profileFlux_union_disjoint G total
    q.color1 q.color2 h12
  have hc12 : CurrentConnected G
      (ofEdgeFun G (fun e => profileFlux G total q.color1 e +
        profileFlux G total q.color2 e)) i y ↔
      connK (endsM G total) (q.color1 ∪ q.color2) i y := by
    rw [connK_iff, hp12]
  have h34 : Disjoint q.color3 (q.color4 Finset.univ) := by
    rw [Finset.disjoint_left]
    intro x hx3 hx4
    have hxnot := (Finset.mem_sdiff.mp hx4).2
    apply hxnot
    exact Finset.mem_union_right _ hx3
  have hp34 := graham_profileFlux_union_disjoint G total
    q.color3 (q.color4 Finset.univ) h34
  have hc34 : CurrentConnected G
      (ofEdgeFun G (fun e => profileFlux G total q.color3 e +
        profileFlux G total (q.color4 Finset.univ) e)) k y ↔
      connK (endsM G total) (q.color3 ∪ q.color4 Finset.univ) k y := by
    rw [connK_iff, hp34]
  simp only [mem_finiteTreeSeparatedBranchColorings, hq, true_and]
  unfold finiteTreeSeparatedCurrentPattern
  rw [← sources_eq G total q.color1,
    ← sources_eq G total q.color2,
    ← sources_eq G total q.color3, h4,
    ← sources_eq G total (q.color4 Finset.univ)]
  by_cases h1 : RandomCurrent.sources (endsM G total) q.color1 = {i, j} <;>
    by_cases h2 : RandomCurrent.sources (endsM G total) q.color2 = ∅ <;>
    by_cases h3 : RandomCurrent.sources (endsM G total) q.color3 = {k, l} <;>
    by_cases h4s : RandomCurrent.sources (endsM G total)
      (q.color4 Finset.univ) = ∅ <;>
    by_cases h5 : connK (endsM G total) (q.color1 ∪ q.color2) i y <;>
    by_cases h6 : connK (endsM G total)
      (q.color3 ∪ q.color4 Finset.univ) k y <;>
    simp [h1, h2, h3, h4s, h5, h6, hc12, hc34]

set_option maxHeartbeats 4000000 in



theorem finiteTreeSeparatedFourColorCoefficient_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (i j k l y : V) :
    finiteTreeFourColorCoefficient G total
        (finiteTreeSeparatedCurrentPattern G i j k l y) =
      (#(finiteTreeSeparatedBranchColorings (endsM G total)
        Finset.univ i j k l y) : Real) := by
  let Theta : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> Real := fun a b c =>
    if finiteTreeSeparatedCurrentPattern G i j k l y a b c
        (grahamFourthProfile total a b c) then 1 else 0
  have hbridge := grahamFourColor_edgecopy_bridge
    (M := Real) G total Theta
  calc
    finiteTreeFourColorCoefficient G total
        (finiteTreeSeparatedCurrentPattern G i j k l y) =
        ∑ s : GrahamFourSplit G total,
          grahamFourSplitMultiplicityNat G total s •
            Theta s.1.1 s.1.2.1 s.1.2.2 := by
      unfold finiteTreeFourColorCoefficient
      apply Finset.sum_congr rfl
      intro s hs
      rw [grahamFourSplitMultiplicity_eq_natCast G total s]
      simp only [Theta, nsmul_eq_mul]
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        Theta (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3) := hbridge
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        (if q ∈ finiteTreeSeparatedBranchColorings (endsM G total)
            Finset.univ i j k l y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      change (if finiteTreeSeparatedCurrentPattern G i j k l y
          (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3)
          (grahamFourthProfile total
            (profileFlux G total q.color1)
            (profileFlux G total q.color2)
            (profileFlux G total q.color3))
        then (1 : Real) else 0) = _
      exact finiteTreeSeparatedProfileIndicator_eq_mem
        G total i j k l y q (by simpa using hq)
    _ = (#(finiteTreeSeparatedBranchColorings (endsM G total)
        Finset.univ i j k l y) : Real) := by
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Finset.filter_subset _ _ h, h⟩



theorem finiteTreeMixedFourMass_eq_card_tsum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    Summable (fun total : G.edgeFinset -> Nat =>
      (#(finiteTreeMixedColorings (endsM G total)
          Finset.univ i j k l) : Real) *
        weight G beta J (ofEdgeFun G total)) ∧
      finiteTreeMixedFourMass G beta J i j k l =
        ∑' total : G.edgeFinset -> Nat,
          (#(finiteTreeMixedColorings (endsM G total)
              Finset.univ i j k l) : Real) *
            weight G beta J (ofEdgeFun G total) := by
  have hres := finiteTreeMixedFourMass_resum G beta J hbeta hJ hij hkl
  constructor
  · apply hres.1.congr
    intro total
    rw [finiteTreeMixedFourColorCoefficient_eq_card]
  · rw [hres.2]
    apply tsum_congr
    intro total
    rw [finiteTreeMixedFourColorCoefficient_eq_card]



theorem finiteTreeSeparatedFourMass_eq_card_tsum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) (y : V) :
    Summable (fun total : G.edgeFinset -> Nat =>
      (#(finiteTreeSeparatedBranchColorings (endsM G total)
          Finset.univ i j k l y) : Real) *
        weight G beta J (ofEdgeFun G total)) ∧
      finiteTreeSeparatedFourMass G beta J i j k l y =
        ∑' total : G.edgeFinset -> Nat,
          (#(finiteTreeSeparatedBranchColorings (endsM G total)
              Finset.univ i j k l y) : Real) *
            weight G beta J (ofEdgeFun G total) := by
  have hres := finiteTreeSeparatedFourMass_resum
    G beta J hbeta hJ hij hkl y
  constructor
  · apply hres.1.congr
    intro total
    rw [finiteTreeSeparatedFourColorCoefficient_eq_card]
  · rw [hres.2]
    apply tsum_congr
    intro total
    rw [finiteTreeSeparatedFourColorCoefficient_eq_card]



def FiniteTreeColoringCardBound
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j k l : V) : Prop :=
  ∀ total : G.edgeFinset -> Nat,
    #(finiteTreeMixedColorings (endsM G total)
        Finset.univ i j k l) <=
      ∑ y : V, #(finiteTreeSeparatedBranchColorings (endsM G total)
        Finset.univ i j k l y)



theorem finiteTreeMixedFourMass_le_sum_separated_of_cardBound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (hcard : FiniteTreeColoringCardBound G i j k l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
  let fm : (G.edgeFinset -> Nat) -> Real := fun total =>
    (#(finiteTreeMixedColorings (endsM G total)
        Finset.univ i j k l) : Real) *
      weight G beta J (ofEdgeFun G total)
  let fs : V -> (G.edgeFinset -> Nat) -> Real := fun y total =>
    (#(finiteTreeSeparatedBranchColorings (endsM G total)
        Finset.univ i j k l y) : Real) *
      weight G beta J (ofEdgeFun G total)
  have hmix := finiteTreeMixedFourMass_eq_card_tsum
    G beta J hbeta hJ hij hkl
  have hsep (y : V) := finiteTreeSeparatedFourMass_eq_card_tsum
    G beta J hbeta hJ hij hkl y
  have hmixSum : Summable fm := by simpa only [fm] using hmix.1
  have hsepSum : ∀ y, Summable (fs y) := by
    intro y
    simpa only [fs] using (hsep y).1
  have hsepOuter : Summable (fun total => ∑ y : V, fs y total) := by
    let S : Finset V := Finset.univ
    have hfinite : ∀ T : Finset V,
        Summable (fun total => ∑ y ∈ T, fs y total) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using
          (summable_zero : Summable
            (fun _ : G.edgeFinset -> Nat => (0 : Real)))
      | @insert y T hyT ih =>
          simpa [Finset.sum_insert hyT] using (hsepSum y).add ih
    simpa [S] using hfinite S
  have hpoint : ∀ total, fm total <= ∑ y : V, fs y total := by
    intro total
    dsimp only [fm, fs]
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hcard total
    · exact StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _
  calc
    finiteTreeMixedFourMass G beta J i j k l = ∑' total, fm total := by
      simpa only [fm] using hmix.2
    _ <= ∑' total, ∑ y : V, fs y total :=
      hmixSum.tsum_le_tsum hpoint hsepOuter
    _ = ∑ y : V, ∑' total, fs y total := by
      exact Summable.tsum_finsetSum (s := (Finset.univ : Finset V))
        (fun y _ => hsepSum y)
    _ = ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
      apply Finset.sum_congr rfl
      intro y hy
      simpa only [fs] using (hsep y).2.symm

end StatMech.FrontierA
