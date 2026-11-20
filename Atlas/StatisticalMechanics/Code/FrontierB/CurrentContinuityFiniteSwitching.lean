/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FiniteBoundarySourceLaw
import Code.Sharpness.SwitchingDichotomy

open scoped symmDiff

namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance currentContinuityFiniteSwitchingPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p




theorem boundarySourceGatedPairSum_empty_pair_switching
    (beta : Real) (J : Sym2 V -> Real) (interior : Finset V)
    {u v : V} (huv : u ≠ v)
    (hu : u ∈ interior) (hv : v ∈ interior)
    (P : Current V -> Prop) [DecidablePred P] :
    boundarySourceGatedPairSum G beta J interior ∅ {u, v} P =
      boundarySourceGatedPairSum G beta J interior {u, v} ∅
        (fun m => P m ∧ CurrentConnected G m u v) := by
  let U : Finset V := {u, v}
  have hU : U ⊆ interior := by
    intro x hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  unfold boundarySourceGatedPairSum
  change (∑ A : Finset V,
      if A ∩ interior = ∅ then gatedSourcePairSum G beta J A U P else 0) = _
  calc
    (∑ A : Finset V,
        if A ∩ interior = ∅ then gatedSourcePairSum G beta J A U P else 0) =
        ∑ A : Finset V,
          if (A ∆ U) ∩ interior = ∅ then
            gatedSourcePairSum G beta J (A ∆ U) U P
          else 0 := by
      symm
      exact (sourceToggleEquiv U).sum_comp
        (fun A : Finset V =>
          if A ∩ interior = ∅ then
            gatedSourcePairSum G beta J A U P
          else 0)
    _ = ∑ A : Finset V,
        if A ∩ interior = U then
          gatedSourcePairSum G beta J A ∅
            (fun m => P m ∧ CurrentConnected G m u v)
        else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      have hinter : (A ∆ U) ∩ interior = ∅ ↔ A ∩ interior = U := by
        rw [← sourceToggle_inter_eq_iff interior U (A ∆ U) hU]
        simp only [symmDiff_symmDiff_cancel_right]
      rw [if_congr hinter rfl rfl]
      by_cases hA : A ∩ interior = U
      · simp only [hA, if_true]
        simpa only [U] using
          (gatedSourcePairSum_switching G beta J A huv P)
      · simp only [hA, if_false]
    _ = _ := rfl



theorem boundarySourceGatedPairSum_true_eq_mul
    (beta : Real) (J : Sym2 V -> Real)
    (interior internalSources exactSecondSources : Finset V) :
    boundarySourceGatedPairSum G beta J interior internalSources
        exactSecondSources (fun _ => True) =
      boundarySourceCurrentSum G beta J interior internalSources *
        currentSum G beta J exactSecondSources := by
  have hgate : forall A : Finset V,
      gatedSourcePairSum G beta J A exactSecondSources (fun _ => True) =
        sourcePairSum G beta J A exactSecondSources := by
    intro A
    unfold gatedSourcePairSum sourcePairSum
    congr 1
    funext pq
    simp
  rw [boundarySourceCurrentSum_eq_boundarySourceSectorSum]
  unfold boundarySourceGatedPairSum boundarySourceSectorSum
  simp_rw [hgate, sourcePairSum_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A _
  split <;> simp_all



theorem boundarySourceGatedPairSum_conn_add_notConn
    (beta : Real) (J : Sym2 V -> Real)
    (interior internalSources exactSecondSources : Finset V)
    (u v : V) :
    boundarySourceGatedPairSum G beta J interior internalSources
        exactSecondSources (fun m => CurrentConnected G m u v) +
      boundarySourceGatedPairSum G beta J interior internalSources
        exactSecondSources (fun m => ¬ CurrentConnected G m u v) =
      boundarySourceGatedPairSum G beta J interior internalSources
        exactSecondSources (fun _ => True) := by
  unfold boundarySourceGatedPairSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hsector : A ∩ interior = internalSources
  · simp only [hsector, if_true]
    unfold gatedSourcePairSum
    rw [← Summable.tsum_add
      (summable_gatedSourcePairSummand G beta J A exactSecondSources
        (fun m => CurrentConnected G m u v))
      (summable_gatedSourcePairSummand G beta J A exactSecondSources
        (fun m => ¬ CurrentConnected G m u v))]
    apply tsum_congr
    intro pq
    by_cases hconn : CurrentConnected G
        (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) u v <;>
      simp [hconn]
  · simp [hsector]




theorem boundarySource_twoPoint_gap_eq_notConnected
    (beta : Real) (J : Sym2 V -> Real) (interior : Finset V)
    {u v : V} (huv : u ≠ v)
    (hu : u ∈ interior) (hv : v ∈ interior) :
    boundarySourceCurrentSum G beta J interior {u, v} *
          currentSum G beta J ∅ -
        boundarySourceCurrentSum G beta J interior ∅ *
          currentSum G beta J {u, v} =
      boundarySourceGatedPairSum G beta J interior {u, v} ∅
        (fun m => ¬ CurrentConnected G m u v) := by
  have hswitch := boundarySourceGatedPairSum_empty_pair_switching
    G beta J interior huv hu hv (fun _ => True)
  simp only [true_and] at hswitch
  have htotalEmpty := boundarySourceGatedPairSum_true_eq_mul
    G beta J interior ∅ {u, v}
  have htotalPair := boundarySourceGatedPairSum_true_eq_mul
    G beta J interior {u, v} ∅
  have hpartition := boundarySourceGatedPairSum_conn_add_notConn
    G beta J interior {u, v} ∅ u v
  rw [htotalEmpty] at hswitch
  rw [htotalPair] at hpartition
  rw [← hswitch] at hpartition
  linarith


theorem exists_ne_source_currentConnected
    (m : EdgeCurrent G) (u : V)
    (hu : u ∈ sources G (ofEdgeFun G m)) :
    ∃ z : V, z ∈ sources G (ofEdgeFun G m) ∧ z ≠ u ∧
      CurrentConnected G (ofEdgeFun G m) u z := by
  let U : Finset (FluxEdgeCopy.Copy G m) := Finset.univ
  let C := RandomCurrent.compOddVertices (FluxEdgeCopy.endsM G m) U u
  have hsrcU : RandomCurrent.sources (FluxEdgeCopy.endsM G m) U =
      sources G (ofEdgeFun G m) := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
  have huC : u ∈ C := by
    apply RandomCurrent.compOddVertices_mem_of_source
    · rw [hsrcU]
      exact hu
    · exact Relation.ReflTransGen.refl
  have heven : Even C.card := by
    exact RandomCurrent.even_compOddVertices
      (FluxEdgeCopy.endsM G m) U
      (fun i _ => FluxEdgeCopy.endsM_not_isDiag G m i) u
  have hex : ∃ z ∈ C, z ≠ u := by
    by_contra h
    push Not at h
    have hC : C = {u} := by
      apply Finset.Subset.antisymm
      · intro z hz
        simpa using h z hz
      · intro z hz
        rw [Finset.mem_singleton] at hz
        subst z
        exact huC
    rw [hC, Finset.card_singleton] at heven
    exact (by decide : ¬ Even 1) heven
  obtain ⟨z, hzC, hzu⟩ := hex
  have hz := (RandomCurrent.mem_compOddVertices.mp hzC)
  refine ⟨z, ?_, hzu, ?_⟩
  · rw [← hsrcU]
    exact RandomCurrent.mem_sources.mpr hz.2
  · simpa only [U, FluxEdgeCopy.connK_univ_iff] using hz.1


theorem currentConnected_add_right
    (m n : EdgeCurrent G) {x y : V}
    (h : CurrentConnected G (ofEdgeFun G m) x y) :
    CurrentConnected G (ofEdgeFun G (fun e => m e + n e)) x y := by
  exact SimpleGraph.Reachable.mono (fun a b hab => by
    refine ⟨hab.1, ?_⟩
    have hedge : s(a, b) ∈ G.edgeFinset := by
      simpa [SimpleGraph.mem_edgeFinset] using hab.1
    calc
      1 ≤ ofEdgeFun G m s(a, b) := hab.2
      _ = m ⟨s(a, b), hedge⟩ := by simp [ofEdgeFun, hedge]
      _ ≤ m ⟨s(a, b), hedge⟩ + n ⟨s(a, b), hedge⟩ :=
        Nat.le_add_right _ _
      _ = ofEdgeFun G (fun e => m e + n e) s(a, b) := by
        simp [ofEdgeFun, hedge]) h



theorem boundarySource_notConnected_reaches_exterior
    (interior : Finset V) {u v : V} (huv : u ≠ v)
    (m n : EdgeCurrent G)
    (hsrc : sources G (ofEdgeFun G m) ∩ interior = {u, v})
    (hnot : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => m e + n e)) u v) :
    ∃ z : V, z ∉ interior ∧
      CurrentConnected G (ofEdgeFun G (fun e => m e + n e)) u z := by
  have huInterior : u ∈ interior := by
    have : u ∈ sources G (ofEdgeFun G m) ∩ interior := by
      rw [hsrc]
      simp
    exact (Finset.mem_inter.mp this).2
  have huSource : u ∈ sources G (ofEdgeFun G m) := by
    have : u ∈ sources G (ofEdgeFun G m) ∩ interior := by
      rw [hsrc]
      simp
    exact (Finset.mem_inter.mp this).1
  obtain ⟨z, hzSource, hzu, huz⟩ :=
    exists_ne_source_currentConnected G m u huSource
  have huzSum := currentConnected_add_right G m n huz
  refine ⟨z, ?_, huzSum⟩
  intro hzInterior
  have hzPair : z ∈ ({u, v} : Finset V) := by
    rw [← hsrc]
    exact Finset.mem_inter.mpr ⟨hzSource, hzInterior⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
  rcases hzPair with rfl | rfl
  · exact hzu rfl
  · exact hnot huzSum

end StatMech.FrontierB
