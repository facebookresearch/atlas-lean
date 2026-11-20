/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianClusterConfinement
import Code.FrontierA.IsingGaussianIntersectionUnionBound
import Code.FrontierA.GrahamWeightedAuxiliaryAlgebra












open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev DisentangleFourProfiles
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
    ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat))

noncomputable def finiteTreePairVacuumWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V)
    (pq : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) : Real :=
  (if sources G (ofEdgeFun G pq.1) = A
    then weight G beta J (ofEdgeFun G pq.1) else 0) *
  (if sources G (ofEdgeFun G pq.2) = ∅
    then weight G beta J (ofEdgeFun G pq.2) else 0)

noncomputable def finiteTreeIndependentDisjointSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : DisentangleFourProfiles G) : Real :=
  finiteTreePairVacuumWeight G beta J {i, j} z.1 *
    finiteTreePairVacuumWeight G beta J {k, l} z.2 *
      (if ¬ ∃ y : V,
        CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
        CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
      then 1 else 0)


noncomputable def finiteTreeIndependentDisjointFourCurrentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : DisentangleFourProfiles G,
    finiteTreeIndependentDisjointSummand G beta J i j k l z

private theorem summable_finiteTreePairVacuumWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V) :
    Summable (finiteTreePairVacuumWeight G beta J A) := by
  have h := summable_gatedSourcePairSummand G beta J A ∅ (fun _ => True)
  apply h.congr
  rintro ⟨p, q⟩
  simp [finiteTreePairVacuumWeight]

theorem summable_finiteTreeIndependentDisjointSummand_fourCurrent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    Summable (finiteTreeIndependentDisjointSummand G beta J i j k l) := by
  have hleft := summable_finiteTreePairVacuumWeight
    G beta J ({i, j} : Finset V)
  have hright := summable_finiteTreePairVacuumWeight
    G beta J ({k, l} : Finset V)
  have hmajor : Summable (fun z : DisentangleFourProfiles G =>
      ‖finiteTreePairVacuumWeight G beta J {i, j} z.1‖ *
        ‖finiteTreePairVacuumWeight G beta J {k, l} z.2‖) :=
    hleft.norm.mul_of_nonneg hright.norm
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_norm
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro z
  unfold finiteTreeIndependentDisjointSummand
  by_cases h : ¬ ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
  · simp [h, norm_mul]
  · simp [h]
    positivity

noncomputable def finiteTreeDisjointComponentSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (S : Finset V) (z : DisentangleFourProfiles G) : Real :=
  finiteTreePairVacuumWeight G beta J {i, j} z.1 *
    finiteTreePairVacuumWeight G beta J {k, l} z.2 *
      (if notConnComp G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i = S ∧
        k ∈ finiteTreeSafeRegion G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) Sᶜ
      then 1 else 0)

private theorem finiteTreeDisjointComponent_tsum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) (S : Finset V) :
    Summable (finiteTreeDisjointComponentSummand G beta J i j k l S) ∧
    (∑' z : DisentangleFourProfiles G,
      finiteTreeDisjointComponentSummand G beta J i j k l S z) =
      grahamFirstComponentFiber G beta J S i {i, j} ∅ *
        finiteTreeClusterConfinementMass G beta J k l S := by
  let P : Current V -> Prop := fun n => notConnComp G n i = S
  let Q : Current V -> Prop := fun n =>
    k ∈ finiteTreeSafeRegion G n Sᶜ
  have hleft := summable_gatedSourcePairSummand G beta J {i, j} ∅ P
  have hright := summable_gatedSourcePairSummand G beta J {k, l} ∅ Q
  have hprod := summable_mul_of_summable_norm hleft.norm hright.norm
  have hpoint : ∀ z : DisentangleFourProfiles G,
      finiteTreeDisjointComponentSummand G beta J i j k l S z =
        (((if sources G (ofEdgeFun G z.1.1) = {i, j}
            then weight G beta J (ofEdgeFun G z.1.1) else 0) *
          (if sources G (ofEdgeFun G z.1.2) = ∅
            then weight G beta J (ofEdgeFun G z.1.2) else 0) *
          (if P (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e))
            then 1 else 0)) *
        ((if sources G (ofEdgeFun G z.2.1) = {k, l}
            then weight G beta J (ofEdgeFun G z.2.1) else 0) *
          (if sources G (ofEdgeFun G z.2.2) = ∅
            then weight G beta J (ofEdgeFun G z.2.2) else 0) *
          (if Q (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e))
            then 1 else 0))) := by
    intro z
    unfold finiteTreeDisjointComponentSummand finiteTreePairVacuumWeight
    dsimp only [P, Q]
    by_cases hP : notConnComp G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i = S <;>
      by_cases hQ : k ∈ finiteTreeSafeRegion G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) Sᶜ <;>
      simp [hP, hQ]
  have hsum : Summable
      (finiteTreeDisjointComponentSummand G beta J i j k l S) := by
    apply hprod.congr
    intro z
    exact (hpoint z).symm
  refine ⟨hsum, ?_⟩
  unfold grahamFirstComponentFiber finiteTreeClusterConfinementMass
  unfold gatedSourcePairSum
  rw [Summable.tsum_mul_tsum hleft hright hprod]
  apply tsum_congr
  intro z
  exact hpoint z

private theorem finiteTreeDisjointComponent_pointwise
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (z : DisentangleFourProfiles G) :
    (∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
      finiteTreeDisjointComponentSummand G beta J i j k l S z) =
      finiteTreeIndependentDisjointSummand G beta J i j k l z := by
  let m := ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)
  let n := ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)
  by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
    by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G z.2.1) = {k, l} <;>
    by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅
  all_goals try
    simp [finiteTreeDisjointComponentSummand,
      finiteTreeIndependentDisjointSummand, finiteTreePairVacuumWeight,
      h1, h2, h3, h4]
  have hijP := currentConnected_of_sources_pair G z.1.1 hij h1
  have hijM : CurrentConnected G m i j := by
    exact grahamCurrentConnected_add_right G z.1.1 z.1.2 hijP
  have hklP := currentConnected_of_sources_pair G z.2.1 hkl h3
  have hklN : CurrentConnected G n k l := by
    exact grahamCurrentConnected_add_right G z.2.1 z.2.2 hklP
  by_cases hd : ¬ ∃ y : V,
      CurrentConnected G m i y ∧ CurrentConnected G n k y
  · let S0 := notConnComp G m i
    have hiS : i ∉ S0 := by
      change i ∉ notConnComp G m i
      rw [mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m i)
    have hjS : j ∉ S0 := by
      change j ∉ notConnComp G m i
      rw [mem_notConnComp]
      exact not_not.mpr hijM
    have hkS : k ∈ S0 := by
      change k ∈ notConnComp G m i
      rw [mem_notConnComp]
      intro hik
      exact hd ⟨k, hik, CurrentConnected.refl G n k⟩
    have hlS : l ∈ S0 := by
      change l ∈ notConnComp G m i
      rw [mem_notConnComp]
      intro hil
      exact hd ⟨l, hil, hklN⟩
    have hS0 : S0 ∈ grahamFirstAdmissibleComponentComplements i j k l k := by
      rw [grahamFirstAdmissibleComponentComplements, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hiS, hjS, hkS, hlS, hkS⟩
    have hkSafe : k ∈ finiteTreeSafeRegion G n S0ᶜ := by
      rw [mem_finiteTreeSafeRegion]
      intro g hg hgk
      have hgNot : g ∉ S0 := by simpa using hg
      have hig : CurrentConnected G m i g := by
        change g ∉ notConnComp G m i at hgNot
        rw [mem_notConnComp] at hgNot
        exact not_not.mp hgNot
      exact hd ⟨g, hig, CurrentConnected.symm G hgk⟩
    rw [Finset.sum_eq_single S0]
    · rw [if_pos (by
          refine ⟨rfl, ?_⟩
          intro g hg
          exact (mem_finiteTreeSafeRegion G n S0ᶜ k).mp hkSafe g
            (by simpa using hg))]
      rw [if_pos (by
        intro x hix hkx
        exact hd ⟨x, hix, hkx⟩)]
    · intro S hS hne
      have hneq : notConnComp G m i ≠ S := by
        intro heq
        exact hne (by simpa [S0] using heq.symm)
      rw [if_neg (fun h => hneq h.1)]
    · intro hnotmem
      exact (hnotmem hS0).elim
  · have hinter : ∃ y : V,
        CurrentConnected G m i y ∧ CurrentConnected G n k y :=
      not_not.mp hd
    rw [Finset.sum_eq_zero]
    · rw [if_neg (by
        intro hall
        obtain ⟨y, hiy, hky⟩ := hinter
        exact hall y hiy hky)]
    · intro S hS
      have hnot : ¬ (notConnComp G m i = S ∧
          k ∈ finiteTreeSafeRegion G n Sᶜ) := by
        rintro ⟨heq, hkSafe⟩
        obtain ⟨y, hiy, hky⟩ := hinter
        have hyNot : y ∉ S := by
          rw [← heq, mem_notConnComp]
          exact not_not.mpr hiy
        have hyRoot : y ∈ Sᶜ := by simpa using hyNot
        exact (mem_finiteTreeSafeRegion G n Sᶜ k).mp hkSafe y hyRoot
          (CurrentConnected.symm G hky)
      rw [if_neg (by
        rintro ⟨heq, hall⟩
        apply hnot
        refine ⟨heq, ?_⟩
        rw [mem_finiteTreeSafeRegion]
        intro g hg
        exact hall g (by simpa using hg))]




theorem finiteTreeIndependentDisjointFourMass_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentDisjointFourCurrentMass G beta J i j k l =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
        grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          finiteTreeClusterConfinementMass G beta J k l S := by
  let A := grahamFirstAdmissibleComponentComplements i j k l k
  have hcomp (S : Finset V) :=
    finiteTreeDisjointComponent_tsum G beta J i j k l S
  have hsum : ∀ S ∈ A,
      Summable (finiteTreeDisjointComponentSummand G beta J i j k l S) :=
    fun S _ => (hcomp S).1
  unfold finiteTreeIndependentDisjointFourCurrentMass
  calc
    (∑' z : DisentangleFourProfiles G,
        finiteTreeIndependentDisjointSummand G beta J i j k l z) =
        ∑' z : DisentangleFourProfiles G,
          ∑ S ∈ A,
            finiteTreeDisjointComponentSummand G beta J i j k l S z := by
      apply tsum_congr
      intro z
      exact (finiteTreeDisjointComponent_pointwise
        G beta J hij hkl z).symm
    _ = ∑ S ∈ A, ∑' z : DisentangleFourProfiles G,
          finiteTreeDisjointComponentSummand G beta J i j k l S z := by
      exact Summable.tsum_finsetSum hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (hcomp S).2



theorem finiteTreeIndependentDisjointFourMass_le_mixedDisconnection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentDisjointFourCurrentMass G beta J i j k l <=
      sourcePairDisconnSum G beta J {i, j} {k, l} i k *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTreeIndependentDisjointFourMass_eq_componentSum
    G beta J hij hkl]
  calc
    (∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
        grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          finiteTreeClusterConfinementMass G beta J k l S) <=
        ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
          (expectationJ G beta (couplingIn J S) {k, l} *
            grahamFirstComponentFiber G beta J S i {i, j} ∅) *
              currentSum G beta J ∅ ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have hfirst := gatedSourcePairSum_nonneg G beta J hbeta hJ
        {i, j} ∅ (fun n => notConnComp G n i = S)
      change 0 <= grahamFirstComponentFiber G beta J S i {i, j} ∅ at hfirst
      have hconf := finiteTreeClusterConfinementMass_le
        G beta J hbeta hJ hkl S
      have hmul := mul_le_mul_of_nonneg_left hconf hfirst
      calc
        grahamFirstComponentFiber G beta J S i {i, j} ∅ *
            finiteTreeClusterConfinementMass G beta J k l S <=
          grahamFirstComponentFiber G beta J S i {i, j} ∅ *
            (expectationJ G beta (couplingIn J S) {k, l} *
              currentSum G beta J ∅ ^ 2) := hmul
        _ = (expectationJ G beta (couplingIn J S) {k, l} *
            grahamFirstComponentFiber G beta J S i {i, j} ∅) *
              currentSum G beta J ∅ ^ 2 := by ring
    _ = sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 := by
      rw [← Finset.sum_mul]
      rw [← finiteTree_mixedDisconnection_eq_componentReplacement
        G beta J hij hkl]

private theorem finiteTreePairSupport_eq_pair {x y : V} (hxy : x ≠ y) :
    grahamPairSupport x y = {x, y} := by
  ext z
  simp only [grahamPairSupport, Finset.mem_symmDiff,
    Finset.mem_singleton, Finset.mem_insert]
  by_cases hzx : z = x <;> by_cases hzy : z = y <;>
    simp_all [eq_comm]



theorem finiteTreeMixed_add_disconnection_eq_total
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 =
      currentSum G beta J {i, j} * currentSum G beta J {k, l} *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTreeMixedFourMass_eq,
    finiteTreePairSupport_eq_pair hij,
    finiteTreePairSupport_eq_pair hkl]
  have hsplit := StatMech.Walls.gc37_sourcePairSum_conn_add_disconn
    G beta J ({i, j} : Finset V) ({k, l} : Finset V) i k
  rw [gc37_sourcePairConnSum_eq_gated] at hsplit
  calc
    gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) * currentSum G beta J ∅ ^ 2 +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 =
      (gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k) *
          currentSum G beta J ∅ ^ 2 := by ring
    _ = sourcePairSum G beta J {i, j} {k, l} *
          currentSum G beta J ∅ ^ 2 := by rw [← hsplit]
    _ = _ := by rw [sourcePairSum_eq_mul]

private theorem finiteTreeIndependentIndicator_complement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (z : DisentangleFourProfiles G) :
    finiteTreeIndependentIntersectionSummand G beta J i j k l z +
      finiteTreeIndependentDisjointSummand G beta J i j k l z =
        finiteTreePairVacuumWeight G beta J {i, j} z.1 *
          finiteTreePairVacuumWeight G beta J {k, l} z.2 := by
  unfold finiteTreeIndependentIntersectionSummand
  unfold finiteTreeIndependentDisjointSummand finiteTreePairVacuumWeight
  rw [finiteTreePairSupport_eq_pair hij,
    finiteTreePairSupport_eq_pair hkl]
  by_cases h : ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y <;>
    simp [h]



theorem finiteTreeIndependentIntersection_add_disjoint_eq_total
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentIntersectionFourMass G beta J i j k l +
        finiteTreeIndependentDisjointFourCurrentMass G beta J i j k l =
      currentSum G beta J {i, j} * currentSum G beta J {k, l} *
        currentSum G beta J ∅ ^ 2 := by
  have hinter := summable_finiteTreeIndependentIntersectionSummand
    G beta J i j k l
  have hdisjoint := summable_finiteTreeIndependentDisjointSummand_fourCurrent
    G beta J i j k l
  have hleft := summable_finiteTreePairVacuumWeight
    G beta J ({i, j} : Finset V)
  have hright := summable_finiteTreePairVacuumWeight
    G beta J ({k, l} : Finset V)
  have hprod := summable_mul_of_summable_norm hleft.norm hright.norm
  unfold finiteTreeIndependentIntersectionFourMass
  unfold finiteTreeIndependentDisjointFourCurrentMass
  rw [← Summable.tsum_add hinter hdisjoint]
  calc
    (∑' z : DisentangleFourProfiles G,
        (finiteTreeIndependentIntersectionSummand G beta J i j k l +
          finiteTreeIndependentDisjointSummand G beta J i j k l) z) =
      ∑' z : DisentangleFourProfiles G,
        finiteTreePairVacuumWeight G beta J {i, j} z.1 *
          finiteTreePairVacuumWeight G beta J {k, l} z.2 := by
      apply tsum_congr
      exact finiteTreeIndependentIndicator_complement G beta J hij hkl
    _ = (∑' p, finiteTreePairVacuumWeight G beta J {i, j} p) *
          (∑' q, finiteTreePairVacuumWeight G beta J {k, l} q) := by
      rw [Summable.tsum_mul_tsum hleft hright hprod]
    _ = sourcePairSum G beta J {i, j} ∅ *
          sourcePairSum G beta J {k, l} ∅ := by rfl
    _ = _ := by
      rw [sourcePairSum_eq_mul, sourcePairSum_eq_mul]
      ring




theorem finiteTreeMixedFourMass_le_independentIntersection_fourCurrent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      finiteTreeIndependentIntersectionFourMass G beta J i j k l := by
  have hdisjoint := finiteTreeIndependentDisjointFourMass_le_mixedDisconnection
    G beta J hbeta hJ hij hkl
  have hmixed := finiteTreeMixed_add_disconnection_eq_total
    G beta J hij hkl
  have hindependent := finiteTreeIndependentIntersection_add_disjoint_eq_total
    G beta J hij hkl
  linarith


theorem finiteTreeMixedFourMass_le_sum_separated_fourCurrent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y :=
  (finiteTreeMixedFourMass_le_independentIntersection_fourCurrent
    G beta J hbeta hJ hij hkl).trans
      (finiteTreeIndependentIntersectionFourMass_le_sum_separated
        G beta J hbeta hJ i j k l)



theorem finiteIsing_treeDiagram_bound_fourCurrent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    0 <= -finiteIsingFourthUrsell G beta J i j k l ∧
      -finiteIsingFourthUrsell G beta J i j k l <=
        2 * finiteCurrentTreeDiagram G beta J i j k l := by
  have hmass := finiteTreeMixedFourMass_le_sum_separated_fourCurrent
    G beta J hbeta hJ hij hkl
  rw [finiteTreeMixedFourMass_eq_allThree G beta J
      hij hik hil hjk hjl hkl,
    sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass] at hmass
  exact finiteIsing_treeDiagram_bound_of_mass G beta J hbeta hJ
    hij hik hil hjk hjl hkl hmass

end StatMech.FrontierA
