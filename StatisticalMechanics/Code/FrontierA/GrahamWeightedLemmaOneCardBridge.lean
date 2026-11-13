/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamFourColorEdgecopyBridge
import Code.FrontierA.GrahamWeightedLemmaOneResummation

open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem grahamFourSplitMultiplicity_eq_natCast
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (s : GrahamFourSplit G total) :
    grahamFourSplitMultiplicity G total s =
      (grahamFourSplitMultiplicityNat G total s : Real) := by
  unfold grahamFourSplitMultiplicity grahamFourSplitMultiplicityNat
  norm_cast


noncomputable def grahamMixedProfileIndicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total a b c : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  (if sources G (ofEdgeFun G a) = {j, k} then 1 else 0) *
    (if sources G (ofEdgeFun G b) = {k, l} then 1 else 0) *
    (if sources G (ofEdgeFun G c) = ∅ then 1 else 0) *
    (if sources G (ofEdgeFun G (grahamFourthProfile total a b c)) = ∅
      then 1 else 0) *
    (if ¬ CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) k m
      then 1 else 0)


noncomputable def grahamSeparatedProfileIndicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total a b c : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  (if sources G (ofEdgeFun G a) = {j, k} then 1 else 0) *
    (if sources G (ofEdgeFun G b) = ∅ then 1 else 0) *
    (if sources G (ofEdgeFun G c) = {k, l} then 1 else 0) *
    (if sources G (ofEdgeFun G (grahamFourthProfile total a b c)) = ∅
      then 1 else 0) *
    (if ¬ CurrentConnected G (ofEdgeFun G (fun e => a e + b e)) k m
      then 1 else 0) *
    (if ¬ CurrentConnected G
        (ofEdgeFun G (fun e => c e + grahamFourthProfile total a b c e)) k m
      then 1 else 0)

set_option maxHeartbeats 2000000 in
theorem grahamMixedProfileIndicator_eq_mem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    grahamMixedProfileIndicator G total
        (profileFlux G total q.color1)
        (profileFlux G total q.color2)
        (profileFlux G total q.color3) j k l m =
      if q ∈ grahamLemmaOneMixedColorings (endsM G total)
          Finset.univ j k l m then 1 else 0 := by
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
        profileFlux G total q.color2 e)) k m <->
      RandomCurrent.connK (endsM G total) (q.color1 ∪ q.color2) k m := by
    rw [connK_iff, hp12]
  simp only [mem_grahamLemmaOneMixedColorings, hq, true_and]
  unfold grahamMixedProfileIndicator
  rw [← sources_eq G total q.color1,
    ← sources_eq G total q.color2,
    ← sources_eq G total q.color3, h4,
    ← sources_eq G total (q.color4 Finset.univ)]
  by_cases h1 : RandomCurrent.sources (endsM G total) q.color1 = {j, k} <;>
    by_cases h2 : RandomCurrent.sources (endsM G total) q.color2 = {k, l} <;>
    by_cases h3 : RandomCurrent.sources (endsM G total) q.color3 = ∅ <;>
    by_cases h4s : RandomCurrent.sources (endsM G total)
      (q.color4 Finset.univ) = ∅ <;>
    by_cases h5 : RandomCurrent.connK (endsM G total)
      (q.color1 ∪ q.color2) k m <;>
    simp [h1, h2, h3, h4s, h5, hc12]

set_option maxHeartbeats 2000000 in
theorem grahamLemmaOneMixedProfileCoefficient_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V) :
    grahamLemmaOneMixedProfileCoefficient G total j k l m =
      (#(grahamLemmaOneMixedColorings (endsM G total)
        Finset.univ j k l m) : Real) := by
  let Theta : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> Real := fun a b c =>
    grahamMixedProfileIndicator G total a b c j k l m
  have hbridge := grahamFourColor_edgecopy_bridge
    (M := Real) G total Theta
  calc
    grahamLemmaOneMixedProfileCoefficient G total j k l m =
        ∑ s : GrahamFourSplit G total,
          grahamFourSplitMultiplicityNat G total s •
            Theta s.1.1 s.1.2.1 s.1.2.2 := by
      unfold grahamLemmaOneMixedProfileCoefficient
      apply Finset.sum_congr rfl
      intro s hs
      rw [grahamFourSplitMultiplicity_eq_natCast G total s]
      simp only [Theta, grahamMixedProfileIndicator, nsmul_eq_mul]
      ring
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        Theta (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3) := hbridge
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        (if q ∈ grahamLemmaOneMixedColorings (endsM G total)
            Finset.univ j k l m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply grahamMixedProfileIndicator_eq_mem G total j k l m q
      simpa using hq
    _ = (#(grahamLemmaOneMixedColorings (endsM G total)
        Finset.univ j k l m) : Real) := by
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Finset.filter_subset _ _ h, h⟩

set_option maxHeartbeats 2000000 in
theorem grahamSeparatedProfileIndicator_eq_mem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    grahamSeparatedProfileIndicator G total
        (profileFlux G total q.color1)
        (profileFlux G total q.color2)
        (profileFlux G total q.color3) j k l m =
      if q ∈ grahamLemmaOneSeparatedColorings (endsM G total)
          Finset.univ j k l m then 1 else 0 := by
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
        profileFlux G total q.color2 e)) k m <->
      RandomCurrent.connK (endsM G total) (q.color1 ∪ q.color2) k m := by
    rw [connK_iff, hp12]
  have h34 : Disjoint q.color3 (q.color4 Finset.univ) := by
    rw [Finset.disjoint_left]
    intro x hx3 hx4
    have hxnot := (Finset.mem_sdiff.mp hx4).2
    apply hxnot
    simp only [Finset.mem_union]
    exact Or.inr hx3
  have hp34 := graham_profileFlux_union_disjoint G total
    q.color3 (q.color4 Finset.univ) h34
  have hc34 : CurrentConnected G
      (ofEdgeFun G (fun e => profileFlux G total q.color3 e +
        profileFlux G total (q.color4 Finset.univ) e)) k m <->
      RandomCurrent.connK (endsM G total)
        (q.color3 ∪ q.color4 Finset.univ) k m := by
    rw [connK_iff, hp34]
  simp only [mem_grahamLemmaOneSeparatedColorings, hq, true_and]
  unfold grahamSeparatedProfileIndicator
  rw [← sources_eq G total q.color1,
    ← sources_eq G total q.color2,
    ← sources_eq G total q.color3, h4,
    ← sources_eq G total (q.color4 Finset.univ)]
  by_cases h1 : RandomCurrent.sources (endsM G total) q.color1 = {j, k} <;>
    by_cases h2 : RandomCurrent.sources (endsM G total) q.color2 = ∅ <;>
    by_cases h3 : RandomCurrent.sources (endsM G total) q.color3 = {k, l} <;>
    by_cases h4s : RandomCurrent.sources (endsM G total)
      (q.color4 Finset.univ) = ∅ <;>
    by_cases h5 : RandomCurrent.connK (endsM G total)
      (q.color1 ∪ q.color2) k m <;>
    by_cases h6 : RandomCurrent.connK (endsM G total)
      (q.color3 ∪ q.color4 Finset.univ) k m <;>
    simp [h1, h2, h3, h4s, h5, h6, hc12, hc34]

set_option maxHeartbeats 2000000 in
theorem grahamLemmaOneSeparatedProfileCoefficient_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V) :
    grahamLemmaOneSeparatedProfileCoefficient G total j k l m =
      (#(grahamLemmaOneSeparatedColorings (endsM G total)
        Finset.univ j k l m) : Real) := by
  let Theta : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> Real := fun a b c =>
    grahamSeparatedProfileIndicator G total a b c j k l m
  have hbridge := grahamFourColor_edgecopy_bridge
    (M := Real) G total Theta
  calc
    grahamLemmaOneSeparatedProfileCoefficient G total j k l m =
        ∑ s : GrahamFourSplit G total,
          grahamFourSplitMultiplicityNat G total s •
            Theta s.1.1 s.1.2.1 s.1.2.2 := by
      unfold grahamLemmaOneSeparatedProfileCoefficient
      apply Finset.sum_congr rfl
      intro s hs
      rw [grahamFourSplitMultiplicity_eq_natCast G total s]
      simp only [Theta, grahamSeparatedProfileIndicator, nsmul_eq_mul]
      ring
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        Theta (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3) := hbridge
    _ = ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        (if q ∈ grahamLemmaOneSeparatedColorings (endsM G total)
            Finset.univ j k l m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply grahamSeparatedProfileIndicator_eq_mem G total j k l m q
      simpa using hq
    _ = (#(grahamLemmaOneSeparatedColorings (endsM G total)
        Finset.univ j k l m) : Real) := by
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Finset.filter_subset _ _ h, h⟩

end StatMech.FrontierA
