/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianClusterConfinement
import Code.FrontierA.IsingGaussianIntersectionUnionBound
import Code.FrontierA.GrahamWeightedEq22Refinement











open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def finiteTreeIndependentDisjointComponentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
    grahamFirstComponentFiber G beta J S i {i, j} ∅ *
      finiteTreeClusterConfinementMass G beta J k l S



theorem finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentDisjointComponentMass G beta J i j k l <=
      sourcePairDisconnSum G beta J {i, j} {k, l} i k *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTree_mixedDisconnection_eq_componentReplacement
    G beta J hij hkl]
  rw [Finset.sum_mul]
  unfold finiteTreeIndependentDisjointComponentMass
  apply Finset.sum_le_sum
  intro S hS
  rw [grahamFirstAdmissibleComponentComplements,
    Finset.mem_filter] at hS
  have hfirst : 0 <= grahamFirstComponentFiber
      G beta J S i {i, j} ∅ :=
    gatedSourcePairSum_nonneg G beta J hbeta hJ {i, j} ∅
      (fun n => notConnComp G n i = S)
  have hconf := finiteTreeClusterConfinementMass_le
    G beta J hbeta hJ hkl S
  calc
    grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          finiteTreeClusterConfinementMass G beta J k l S
        <= grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          (expectationJ G beta (couplingIn J S) {k, l} *
            currentSum G beta J ∅ ^ 2) :=
      mul_le_mul_of_nonneg_left hconf hfirst
    _ = (expectationJ G beta (couplingIn J S) {k, l} *
          grahamFirstComponentFiber G beta J S i {i, j} ∅) *
            currentSum G beta J ∅ ^ 2 := by ring

private abbrev IndependentPairProfiles
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)

private abbrev IndependentFourProfiles
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  IndependentPairProfiles G × IndependentPairProfiles G

private noncomputable def finiteTreeFirstComponentSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j : V) (S : Finset V)
    (pq : IndependentPairProfiles G) : Real :=
  ((if sources G (ofEdgeFun G pq.1) = {i, j}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)) *
    (if notConnComp G
        (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) i = S then 1 else 0)

private noncomputable def finiteTreeConfinementSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V)
    (pq : IndependentPairProfiles G) : Real :=
  ((if sources G (ofEdgeFun G pq.1) = {k, l}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)) *
    (if k ∈ finiteTreeSafeRegion G
        (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) Sᶜ then 1 else 0)

private noncomputable def finiteTreeIndependentDisjointSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : IndependentFourProfiles G) : Real :=
    ((if sources G (ofEdgeFun G z.1.1) = {i, j}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0)) *
    (if ¬ ∃ y : V,
        CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
        CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
      then 1 else 0)



noncomputable def finiteTreeIndependentDisjointFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : IndependentFourProfiles G,
    finiteTreeIndependentDisjointSummand G beta J i j k l z

private theorem independentClusters_disjoint_iff_safeRegion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m n : Current V) (i k : V) :
    (¬ ∃ y : V, CurrentConnected G m i y ∧ CurrentConnected G n k y) ↔
      k ∈ finiteTreeSafeRegion G n (notConnComp G m i)ᶜ := by
  rw [mem_finiteTreeSafeRegion]
  constructor
  · intro h g hg hgn
    rw [Finset.mem_compl, mem_notConnComp] at hg
    push Not at hg
    exact h ⟨g, hg, CurrentConnected.symm G hgn⟩
  · intro h
    rintro ⟨y, hiy, hky⟩
    have hy : y ∈ (notConnComp G m i)ᶜ := by
      rw [Finset.mem_compl, mem_notConnComp]
      exact not_not.mpr hiy
    exact h y hy (CurrentConnected.symm G hky)

private theorem independentDisjoint_admissible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q r s : G.edgeFinset -> Nat)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {i, j})
    (hq : sources G (ofEdgeFun G q) = ∅)
    (hr : sources G (ofEdgeFun G r) = {k, l})
    (hs : sources G (ofEdgeFun G s) = ∅)
    (hdisj : ¬ ∃ y : V,
      CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i y ∧
      CurrentConnected G (ofEdgeFun G (fun e => r e + s e)) k y) :
    notConnComp G (ofEdgeFun G (fun e => p e + q e)) i ∈
      grahamFirstAdmissibleComponentComplements i j k l k := by
  let m := ofEdgeFun G (fun e => p e + q e)
  let n := ofEdgeFun G (fun e => r e + s e)
  have hijp := currentConnected_of_sources_pair G p hij hp
  have hijm : CurrentConnected G m i j :=
    grahamCurrentConnected_add_right G p q hijp
  have hklr := currentConnected_of_sources_pair G r hkl hr
  have hkln : CurrentConnected G n k l :=
    grahamCurrentConnected_add_right G r s hklr
  rw [grahamFirstAdmissibleComponentComplements, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_notConnComp]
    exact not_not.mpr (CurrentConnected.refl G m i)
  · rw [mem_notConnComp]
    exact not_not.mpr hijm
  · rw [mem_notConnComp]
    intro hik
    exact hdisj ⟨k, hik, CurrentConnected.refl G n k⟩
  · rw [mem_notConnComp]
    intro hil
    exact hdisj ⟨l, hil, hkln⟩
  · rw [mem_notConnComp]
    intro hik
    exact hdisj ⟨k, hik, CurrentConnected.refl G n k⟩

private theorem independentDisjointSummand_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (z : IndependentFourProfiles G) :
    finiteTreeIndependentDisjointSummand G beta J i j k l z =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
        finiteTreeFirstComponentSummand G beta J i j S z.1 *
          finiteTreeConfinementSummand G beta J k l S z.2 := by
  let m := ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)
  let n := ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)
  let S₀ := notConnComp G m i
  by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
    by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G z.2.1) = {k, l} <;>
    by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅
  · by_cases hd : ¬ ∃ y : V,
        CurrentConnected G m i y ∧ CurrentConnected G n k y
    · have hS₀ : S₀ ∈
          grahamFirstAdmissibleComponentComplements i j k l k := by
        exact independentDisjoint_admissible G z.1.1 z.1.2 z.2.1 z.2.2
          hij hkl h1 h2 h3 h4 (by simpa only [m, n] using hd)
      have hsafe : k ∈ finiteTreeSafeRegion G n S₀ᶜ :=
        (independentClusters_disjoint_iff_safeRegion G m n i k).mp hd
      have hsum :
          (∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
            finiteTreeFirstComponentSummand G beta J i j S z.1 *
              finiteTreeConfinementSummand G beta J k l S z.2) =
            finiteTreeFirstComponentSummand G beta J i j S₀ z.1 *
              finiteTreeConfinementSummand G beta J k l S₀ z.2 := by
        apply Finset.sum_eq_single S₀
        · intro S hS hne
          simp [finiteTreeFirstComponentSummand, S₀, m, hne.symm]
        · intro hnot
          exact (hnot hS₀).elim
      rw [hsum]
      simp [finiteTreeIndependentDisjointSummand,
          finiteTreeFirstComponentSummand,
          finiteTreeConfinementSummand, h1, h2, h3, h4, hd,
          m, n, S₀, hsafe]
    · have hnotSafe : k ∉ finiteTreeSafeRegion G n S₀ᶜ := by
        intro hsafe
        exact hd ((independentClusters_disjoint_iff_safeRegion
          G m n i k).mpr hsafe)
      have hex : ∃ y : V,
          CurrentConnected G m i y ∧ CurrentConnected G n k y :=
        not_not.mp hd
      rw [finiteTreeIndependentDisjointSummand]
      simp [h1, h2, h3, h4, m, n, hex]
      symm
      apply Finset.sum_eq_zero
      intro S hS
      by_cases heq : S₀ = S
      · subst S
        simp [finiteTreeFirstComponentSummand,
          finiteTreeConfinementSummand, h1, h2, h3, h4,
          S₀, m, n, hnotSafe]
      · simp [finiteTreeFirstComponentSummand, S₀, m, heq]
  all_goals
    simp [finiteTreeIndependentDisjointSummand,
      finiteTreeFirstComponentSummand,
      finiteTreeConfinementSummand, h1, h2, h3, h4]

private theorem grahamFirstComponentFiber_eq_tsum_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j : V) (S : Finset V) :
    grahamFirstComponentFiber G beta J S i {i, j} ∅ =
      ∑' pq : IndependentPairProfiles G,
        finiteTreeFirstComponentSummand G beta J i j S pq := by
  rfl

private theorem finiteTreeClusterConfinementMass_eq_tsum_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V) :
    finiteTreeClusterConfinementMass G beta J k l S =
      ∑' pq : IndependentPairProfiles G,
        finiteTreeConfinementSummand G beta J k l S pq := by
  rfl



theorem finiteTreeIndependentDisjointComponentMass_eq_fourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentDisjointComponentMass G beta J i j k l =
      finiteTreeIndependentDisjointFourMass G beta J i j k l := by
  let A := grahamFirstAdmissibleComponentComplements i j k l k
  have hf (S : Finset V) : Summable
      (finiteTreeFirstComponentSummand G beta J i j S) := by
    simpa only [finiteTreeFirstComponentSummand] using
      (summable_gatedSourcePairSummand G beta J {i, j} ∅
        (fun n => notConnComp G n i = S))
  have hg (S : Finset V) : Summable
      (finiteTreeConfinementSummand G beta J k l S) := by
    simpa only [finiteTreeConfinementSummand] using
      (summable_gatedSourcePairSummand G beta J {k, l} ∅
        (fun n => k ∈ finiteTreeSafeRegion G n Sᶜ))
  have hprod (S : Finset V) : Summable (fun z : IndependentFourProfiles G =>
      finiteTreeFirstComponentSummand G beta J i j S z.1 *
        finiteTreeConfinementSummand G beta J k l S z.2) :=
    summable_mul_of_summable_norm (hf S).norm (hg S).norm
  unfold finiteTreeIndependentDisjointComponentMass
  calc
    (∑ S ∈ A,
        grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          finiteTreeClusterConfinementMass G beta J k l S) =
        ∑ S ∈ A, ∑' z : IndependentFourProfiles G,
          finiteTreeFirstComponentSummand G beta J i j S z.1 *
            finiteTreeConfinementSummand G beta J k l S z.2 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [grahamFirstComponentFiber_eq_tsum_summand,
        finiteTreeClusterConfinementMass_eq_tsum_summand]
      exact Summable.tsum_mul_tsum (hf S) (hg S) (hprod S)
    _ = ∑' z : IndependentFourProfiles G, ∑ S ∈ A,
          finiteTreeFirstComponentSummand G beta J i j S z.1 *
            finiteTreeConfinementSummand G beta J k l S z.2 := by
      exact (Summable.tsum_finsetSum (s := A)
        (fun S _ => hprod S)).symm
    _ = ∑' z : IndependentFourProfiles G,
          finiteTreeIndependentDisjointSummand G beta J i j k l z := by
      apply tsum_congr
      intro z
      exact (independentDisjointSummand_eq_componentSum
        G beta J hij hkl z).symm
    _ = finiteTreeIndependentDisjointFourMass
          G beta J i j k l := rfl

theorem summable_finiteTreeIndependentDisjointSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    Summable (finiteTreeIndependentDisjointSummand
      G beta J i j k l) := by
  let A := grahamFirstAdmissibleComponentComplements i j k l k
  have hf (S : Finset V) : Summable
      (finiteTreeFirstComponentSummand G beta J i j S) := by
    simpa only [finiteTreeFirstComponentSummand] using
      (summable_gatedSourcePairSummand G beta J {i, j} ∅
        (fun n => notConnComp G n i = S))
  have hg (S : Finset V) : Summable
      (finiteTreeConfinementSummand G beta J k l S) := by
    simpa only [finiteTreeConfinementSummand] using
      (summable_gatedSourcePairSummand G beta J {k, l} ∅
        (fun n => k ∈ finiteTreeSafeRegion G n Sᶜ))
  have hprod (S : Finset V) : Summable (fun z : IndependentFourProfiles G =>
      finiteTreeFirstComponentSummand G beta J i j S z.1 *
        finiteTreeConfinementSummand G beta J k l S z.2) :=
    summable_mul_of_summable_norm (hf S).norm (hg S).norm
  have hsum : Summable (fun z : IndependentFourProfiles G =>
      ∑ S ∈ A, finiteTreeFirstComponentSummand G beta J i j S z.1 *
        finiteTreeConfinementSummand G beta J k l S z.2) := by
    have hfinite : ∀ T : Finset (Finset V), Summable
        (fun z : IndependentFourProfiles G =>
          ∑ S ∈ T, finiteTreeFirstComponentSummand G beta J i j S z.1 *
            finiteTreeConfinementSummand G beta J k l S z.2) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using
          (summable_zero : Summable
            (fun _ : IndependentFourProfiles G => (0 : Real)))
      | @insert S T hST ih =>
          simpa [Finset.sum_insert hST] using (hprod S).add ih
    exact hfinite A
  apply hsum.congr
  intro z
  exact (independentDisjointSummand_eq_componentSum
    G beta J hij hkl z).symm

private noncomputable def finiteTreeIndependentTotalSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : IndependentFourProfiles G) : Real :=
  ((if sources G (ofEdgeFun G z.1.1) = {i, j}
      then weight G beta J (ofEdgeFun G z.1.1) else 0) *
    (if sources G (ofEdgeFun G z.1.2) = ∅
      then weight G beta J (ofEdgeFun G z.1.2) else 0)) *
  ((if sources G (ofEdgeFun G z.2.1) = {k, l}
      then weight G beta J (ofEdgeFun G z.2.1) else 0) *
    (if sources G (ofEdgeFun G z.2.2) = ∅
      then weight G beta J (ofEdgeFun G z.2.2) else 0))

private theorem independentIntersection_add_disjoint_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (z : IndependentFourProfiles G) :
    finiteTreeIndependentIntersectionSummand G beta J i j k l z +
      finiteTreeIndependentDisjointSummand G beta J i j k l z =
        finiteTreeIndependentTotalSummand G beta J i j k l z := by
  have hij' : grahamPairSupport i j = {i, j} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp_all [eq_comm]
  have hkl' : grahamPairSupport k l = {k, l} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [eq_comm]
  unfold finiteTreeIndependentIntersectionSummand
  unfold finiteTreeIndependentDisjointSummand
  unfold finiteTreeIndependentTotalSummand
  rw [hij', hkl']
  by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
    by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G z.2.1) = {k, l} <;>
    by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅ <;>
    by_cases h : ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y <;>
    simp [h1, h2, h3, h4, h] <;> ring

private theorem finiteTreeIndependentTotal_eq_sourcePairProducts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    (∑' z : IndependentFourProfiles G,
      finiteTreeIndependentTotalSummand G beta J i j k l z) =
      sourcePairSum G beta J {i, j} ∅ *
        sourcePairSum G beta J {k, l} ∅ := by
  let f : IndependentPairProfiles G -> Real := fun pq =>
    (if sources G (ofEdgeFun G pq.1) = {i, j}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)
  let g : IndependentPairProfiles G -> Real := fun pq =>
    (if sources G (ofEdgeFun G pq.1) = {k, l}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)
  have hf : Summable f := by
    simpa only [f, if_true, mul_one] using
      (summable_gatedSourcePairSummand G beta J {i, j} ∅ (fun _ => True))
  have hg : Summable g := by
    simpa only [g, if_true, mul_one] using
      (summable_gatedSourcePairSummand G beta J {k, l} ∅ (fun _ => True))
  have hprod : Summable (fun z : IndependentFourProfiles G =>
      f z.1 * g z.2) :=
    summable_mul_of_summable_norm hf.norm hg.norm
  change (∑' z : IndependentFourProfiles G, f z.1 * g z.2) =
    (∑' pq : IndependentPairProfiles G, f pq) *
      ∑' pq : IndependentPairProfiles G, g pq
  exact (Summable.tsum_mul_tsum hf hg hprod).symm



theorem finiteTreeIndependentIntersection_add_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentIntersectionFourMass G beta J i j k l +
      finiteTreeIndependentDisjointFourMass G beta J i j k l =
        sourcePairSum G beta J {i, j} ∅ *
          sourcePairSum G beta J {k, l} ∅ := by
  have hi := summable_finiteTreeIndependentIntersectionSummand
    G beta J i j k l
  have hd := summable_finiteTreeIndependentDisjointSummand
    G beta J hij hkl
  rw [finiteTreeIndependentIntersectionFourMass,
    finiteTreeIndependentDisjointFourMass,
    ← Summable.tsum_add hi hd]
  calc
    (∑' z : IndependentFourProfiles G,
      (finiteTreeIndependentIntersectionSummand G beta J i j k l z +
        finiteTreeIndependentDisjointSummand G beta J i j k l z)) =
      ∑' z : IndependentFourProfiles G,
        finiteTreeIndependentTotalSummand G beta J i j k l z := by
          apply tsum_congr
          exact independentIntersection_add_disjoint_summand
            G beta J hij hkl
    _ = _ := finiteTreeIndependentTotal_eq_sourcePairProducts
      G beta J i j k l



theorem finiteTreeMixedFourMass_add_disconnection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 =
      sourcePairSum G beta J {i, j} ∅ *
        sourcePairSum G beta J {k, l} ∅ := by
  have hij' : grahamPairSupport i j = {i, j} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp_all [eq_comm]
  have hkl' : grahamPairSupport k l = {k, l} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [eq_comm]
  have hsplit := gatedSourcePairSum_split G beta J {i, j} {k, l}
    (fun _ => True) (fun n => CurrentConnected G n i k)
  have hpartition :
      gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k =
      sourcePairSum G beta J {i, j} {k, l} := by
    rw [gatedSourcePairSum_true] at hsplit
    have hconn : gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => True ∧ CurrentConnected G n i k) =
        gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) := by
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      simp
    have hdisc : gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => True ∧ ¬ CurrentConnected G n i k) =
        sourcePairDisconnSum G beta J {i, j} {k, l} i k := by
      change gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => True ∧ ¬ CurrentConnected G n i k) =
          gatedSourcePairSum G beta J {i, j} {k, l}
            (fun n => ¬ CurrentConnected G n i k)
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      simp
    rw [hconn, hdisc] at hsplit
    exact hsplit.symm
  rw [finiteTreeMixedFourMass_eq, hij', hkl']
  calc
    gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) *
          currentSum G beta J ∅ ^ 2 +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 =
      (gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k) *
          currentSum G beta J ∅ ^ 2 := by ring
    _ = sourcePairSum G beta J {i, j} {k, l} *
          currentSum G beta J ∅ ^ 2 := by rw [hpartition]
    _ = sourcePairSum G beta J {i, j} ∅ *
          sourcePairSum G beta J {k, l} ∅ := by
      rw [sourcePairSum_eq_mul, sourcePairSum_eq_mul,
        sourcePairSum_eq_mul]
      ring




theorem finiteTreeMixedFourMass_le_independentIntersection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      finiteTreeIndependentIntersectionFourMass G beta J i j k l := by
  have hdisj :=
    finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection
      G beta J hbeta hJ hij hkl
  rw [finiteTreeIndependentDisjointComponentMass_eq_fourMass
    G beta J hij hkl] at hdisj
  have hmix := finiteTreeMixedFourMass_add_disconnection
    G beta J hij hkl
  have hinter := finiteTreeIndependentIntersection_add_disjoint
    G beta J hij hkl
  linarith



theorem finiteTreeMixedFourMass_le_sum_separated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y :=
  (finiteTreeMixedFourMass_le_independentIntersection
    G beta J hbeta hJ hij hkl).trans
      (finiteTreeIndependentIntersectionFourMass_le_sum_separated
        G beta J hbeta hJ i j k l)


theorem finiteIsing_treeDiagram_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    0 <= -finiteIsingFourthUrsell G beta J i j k l ∧
      -finiteIsingFourthUrsell G beta J i j k l <=
        2 * finiteCurrentTreeDiagram G beta J i j k l := by
  have hfour := finiteTreeMixedFourMass_le_sum_separated
    G beta J hbeta hJ hij hkl
  have hmass :
      gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => grahamAllThreeConnected G m i j k l) *
            currentSum G beta J ∅ ^ 2 <=
        finiteCurrentTreeDiagramMass G beta J i j k l := by
    rw [← finiteTreeMixedFourMass_eq_allThree G beta J
      hij hik hil hjk hjl hkl]
    rw [← sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass]
    exact hfour
  exact finiteIsing_treeDiagram_bound_of_mass G beta J hbeta hJ
    hij hik hil hjk hjl hkl hmass

end StatMech.FrontierA
