/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPortChainGeneral










open scoped BigOperators

namespace StatMech.FrontierA

open SimpleGraph Finset




structure KWLocalAngularData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  order : KWPortOrder G
  root : KWDartPort G -> Complex
  phase : G.Dart -> G.Dart -> Complex
  phase_eq_portRoots_of_rank_lt :
    forall (d e : G.Dart), d.snd = e.fst ->
      kwOrderedPortRank order (kwPortOfDart G d.symm) <
        kwOrderedPortRank order (kwPortOfDart G e) ->
      phase d e =
        -Complex.I * (root (kwPortOfDart G d.symm))⁻¹ *
          root (kwPortOfDart G e)
  phase_eq_portRoots_of_rank_gt :
    forall (d e : G.Dart), d.snd = e.fst ->
      kwOrderedPortRank order (kwPortOfDart G e) <
        kwOrderedPortRank order (kwPortOfDart G d.symm) ->
      phase d e =
        Complex.I * (root (kwPortOfDart G d.symm))⁻¹ *
          root (kwPortOfDart G e)
  root_ne_zero : forall p, root p ≠ 0
  root_sq_symm : forall d : G.Dart,
    root (kwPortOfDart G d.symm) ^ 2 =
      -(root (kwPortOfDart G d) ^ 2)








noncomputable def kwLocalAngularSplitPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d e : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) : ℂ :=
  if _hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    if _he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm then 1
    else if kwOrderedPortRank (data.order) e.fst <
        kwOrderedPortRank (data.order) e.snd then
      -Complex.I * (data.root e.fst)⁻¹
    else
      Complex.I * (data.root e.fst)⁻¹
  else if _he : kwDartOfPort G e.snd =
      (kwDartOfPort G e.fst).symm then
    data.root e.fst
  else 1

@[simp] theorem kwLocalAngularSplitPhase_external_internal_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hrank : kwOrderedPortRank (data.order) e.1.fst <
      kwOrderedPortRank (data.order) e.1.snd) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 =
      -Complex.I * (data.root e.1.fst)⁻¹ := by
  unfold kwLocalAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, hrank]

@[simp] theorem kwLocalAngularSplitPhase_external_internal_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hrank : kwOrderedPortRank (data.order) e.1.snd <
      kwOrderedPortRank (data.order) e.1.fst) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 =
      Complex.I * (data.root e.1.fst)⁻¹ := by
  unfold kwLocalAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, not_lt_of_ge (le_of_lt hrank)]

@[simp] theorem kwLocalAngularSplitPhase_internal_external
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) :
    kwLocalAngularSplitPhase data d.1
        (kwOrderedExternalSplitDartOfDart G
          (data.order) e).1 =
      data.root (kwPortOfDart G e) := by
  unfold kwLocalAngularSplitPhase
  simp [d.2]

@[simp] theorem kwLocalAngularSplitPhase_internal_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d e : KWOrderedInternalSplitDart G (data.order)) :
    kwLocalAngularSplitPhase data d.1 e.1 = 1 := by
  unfold kwLocalAngularSplitPhase
  simp [d.2, e.2]




theorem kwLocalAngularSplitPhase_endpointProduct_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (data.order)
        (kwPortOfDart G d.symm) <
      kwOrderedPortRank (data.order)
        (kwPortOfDart G e))
    (first last : KWOrderedInternalSplitDart G
      (data.order))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (data.order)
        first.1.fst <
      kwOrderedPortRank (data.order) first.1.snd) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 first.1 *
      kwLocalAngularSplitPhase data last.1
        (kwOrderedExternalSplitDartOfDart G
          (data.order) e).1 =
      data.phase d e := by
  rw [kwLocalAngularSplitPhase_external_internal_of_rank_lt
      data d first hfirstRank,
    kwLocalAngularSplitPhase_internal_external]
  rw [data.phase_eq_portRoots_of_rank_lt d e hde hrank]
  simp only [hfirst]



theorem kwLocalAngularSplitPhase_endpointProduct_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (data.order)
        (kwPortOfDart G e) <
      kwOrderedPortRank (data.order)
        (kwPortOfDart G d.symm))
    (first last : KWOrderedInternalSplitDart G
      (data.order))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (data.order)
        first.1.snd <
      kwOrderedPortRank (data.order) first.1.fst) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 first.1 *
      kwLocalAngularSplitPhase data last.1
        (kwOrderedExternalSplitDartOfDart G
          (data.order) e).1 =
      data.phase d e := by
  rw [kwLocalAngularSplitPhase_external_internal_of_rank_gt
      data d first hfirstRank,
    kwLocalAngularSplitPhase_internal_external]
  rw [data.phase_eq_portRoots_of_rank_gt d e hde hrank]
  simp only [hfirst]



theorem kwLocalAngularSplit_internalPhase_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :
    kwOrderedInternalPhase G (data.order)
        (kwLocalAngularSplitPhase data) = fun _ _ ↦ 1 := by
  funext d e
  unfold kwOrderedInternalPhase
  exact kwLocalAngularSplitPhase_internal_internal data
    ((kwOrderedInternalSplitDartEquiv G
      (data.order)).symm d)
    ((kwOrderedInternalSplitDartEquiv G
      (data.order)).symm e)




theorem kwLocalAngularSplit_internalBlock_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (data.order))
    (hstep : KWOrderedInternalDartStep G
      (data.order) d e) :
    kwOrderedSplitInternalBlock G (data.order)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (data.order))
          (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)) d e =
      1 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge at hstep
  rw [if_pos hstep,
    kwOrderedSplitWeight_internal G weight
      (data.order) d,
    kwLocalAngularSplitPhase_internal_internal]
  exact one_mul 1


theorem kwLocalAngularSplit_internalBlock_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (data.order))
    (hstep : ¬KWOrderedInternalDartStep G
      (data.order) d e) :
    kwOrderedSplitInternalBlock G (data.order)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (data.order))
          (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)) d e =
      0 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change ¬(d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge) at hstep
  rw [if_neg hstep]



theorem kwLocalAngularSplit_enterBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₁₂ d e =
      weight d.edge * kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect, by
      exact kwOrderedExternalSplitDart_edge_ne_internal G
        (data.order) d e⟩,
    kwOrderedSplitWeight_matching]

theorem kwLocalAngularSplit_enterBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₁₂ d e = 0 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]



theorem kwLocalAngularSplit_exitBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₂₁ d e =
      data.root (kwPortOfDart G e) := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect,
      (kwOrderedExternalSplitDart_edge_ne_internal G
        (data.order) e d).symm⟩,
    kwOrderedSplitWeight_internal, kwLocalAngularSplitPhase_internal_external,
    one_mul]

theorem kwLocalAngularSplit_exitBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₂₁ d e = 0 := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]


noncomputable def kwLocalAngularSplitBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ) :=
  kwOrderedSplitTransitionInBlocks G (data.order)
    (kwGraphTransition
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data))

theorem kwLocalAngularSplitBlocks_internal_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (data.order))
    (hstep : KWOrderedInternalDartStep G
      (data.order) d e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d e = 1 :=
  kwLocalAngularSplit_internalBlock_apply_of_step data weight d e hstep

theorem kwLocalAngularSplitBlocks_internal_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (data.order))
    (hstep : ¬KWOrderedInternalDartStep G
      (data.order) d e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d e = 0 :=
  kwLocalAngularSplit_internalBlock_apply_of_not_step data weight d e hstep

theorem kwLocalAngularSplitBlocks_enter_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d e =
      weight d.edge * kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 :=
  kwLocalAngularSplit_enterBlock_apply_of_connect
    data weight d e hconnect

theorem kwLocalAngularSplitBlocks_enter_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d e = 0 :=
  kwLocalAngularSplit_enterBlock_apply_of_not_connect
    data weight d e hconnect

theorem kwLocalAngularSplitBlocks_exit_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ d e =
      data.root (kwPortOfDart G e) :=
  kwLocalAngularSplit_exitBlock_apply_of_connect
    data weight d e hconnect

theorem kwLocalAngularSplitBlocks_exit_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ d e = 0 :=
  kwLocalAngularSplit_exitBlock_apply_of_not_connect
    data weight d e hconnect




noncomputable def kwLocalAngularInternalExitSolution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :
    Matrix (KWOrderedInternalSplitDart G (data.order))
      G.Dart ℂ := fun d e ↦ by
        classical
        exact if KWOrderedInternalDartFacesPort (data.order)
            d (kwPortOfDart G e) then
          data.root (kwPortOfDart G e) else 0

theorem kwLocalAngularInternalExitSolution_of_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart)
    (hfaces : KWOrderedInternalDartFacesPort
      (data.order) d (kwPortOfDart G e)) :
    kwLocalAngularInternalExitSolution data d e =
      data.root (kwPortOfDart G e) := by
  unfold kwLocalAngularInternalExitSolution
  rw [if_pos hfaces]

theorem kwLocalAngularInternalExitSolution_of_not_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart)
    (hfaces : ¬KWOrderedInternalDartFacesPort
      (data.order) d (kwPortOfDart G e)) :
    kwLocalAngularInternalExitSolution data d e = 0 := by
  unfold kwLocalAngularInternalExitSolution
  rw [if_neg hfaces]



theorem kwLocalAngularSplit_internal_mul_exitSolution_of_faces_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart)
    (hfaces : KWOrderedInternalDartFacesPort
      (data.order) d (kwPortOfDart G e))
    (hne : d.1.snd ≠ kwPortOfDart G e) :
    ((kwLocalAngularSplitBlocks data weight).toBlocks₂₂ *
      kwLocalAngularInternalExitSolution data) d e =
      data.root (kwPortOfDart G e) := by
  classical
  rw [Matrix.mul_apply]
  have hddata := kwOrderedInternalSplitDart_adj_data G
    (data.order) d
  have hrankne : kwOrderedPortRank (data.order) d.1.snd ≠
      kwOrderedPortRank (data.order)
        (kwPortOfDart G e) := by
    intro hrank
    apply hne
    exact kwDartPort_eq_of_fst_of_orderRank
      (data.order) hfaces.1 hrank
  rcases hfaces.2 with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩
  · have htarget : kwOrderedPortRank (data.order) d.1.snd <
        kwOrderedPortRank (data.order)
          (kwPortOfDart G e) := by omega
    have hqcard := ((data.order)
      (kwPortOfDart G e).1 (kwPortOfDart G e).2).isLt
    change kwOrderedPortRank (data.order)
      (kwPortOfDart G e) <
        Fintype.card (KWOutgoingDart (G := G) (kwPortOfDart G e).1) at hqcard
    have hcardeq :
        Fintype.card (KWOutgoingDart (G := G) d.1.snd.1) =
          Fintype.card (KWOutgoingDart (G := G) (kwPortOfDart G e).1) :=
      congrArg (fun v ↦ Fintype.card (KWOutgoingDart (G := G) v)) hfaces.1
    have hbound : kwOrderedPortRank (data.order) d.1.snd + 1 <
        Fintype.card (KWOutgoingDart (G := G) d.1.snd.1) := by omega
    let next := kwOrderedIncreasingInternalDartFrom G
      (data.order) d.1.snd hbound
    have hstep : KWOrderedInternalDartStep G
        (data.order) d next :=
      kwOrderedInternalDartStep_increasingFrom G
        (data.order) d hdinc hbound
    have hnextfaces : KWOrderedInternalDartFacesPort
        (data.order) next (kwPortOfDart G e) :=
      kwOrderedInternalDartFacesPort_step G
        (data.order) hstep
        ⟨hfaces.1, Or.inl ⟨hdinc, hdtarget⟩⟩ hne
    calc
      ∑ f, (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d f *
          kwLocalAngularInternalExitSolution data f e =
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d next *
            kwLocalAngularInternalExitSolution data next e := by
        apply Fintype.sum_eq_single next
        intro f hfn
        by_cases hs : KWOrderedInternalDartStep G
            (data.order) d f
        · have hnf := kwOrderedInternalDartStep_rightUnique G
            (data.order) hstep hs
          exact (hfn hnf.symm).elim
        · rw [kwLocalAngularSplitBlocks_internal_apply_of_not_step
            data weight d f hs, zero_mul]
      _ = data.root (kwPortOfDart G e) := by
        rw [kwLocalAngularSplitBlocks_internal_apply_of_step
            data weight d next hstep, one_mul,
          kwLocalAngularInternalExitSolution_of_faces
            data next e hnextfaces]
  · have htarget : kwOrderedPortRank (data.order)
          (kwPortOfDart G e) <
        kwOrderedPortRank (data.order) d.1.snd := by omega
    have hbound : 0 <
        kwOrderedPortRank (data.order) d.1.snd := by omega
    let next := kwOrderedDecreasingInternalDartFrom G
      (data.order) d.1.snd hbound
    have hstep : KWOrderedInternalDartStep G
        (data.order) d next :=
      kwOrderedInternalDartStep_decreasingFrom G
        (data.order) d hddec hbound
    have hnextfaces : KWOrderedInternalDartFacesPort
        (data.order) next (kwPortOfDart G e) :=
      kwOrderedInternalDartFacesPort_step G
        (data.order) hstep
        ⟨hfaces.1, Or.inr ⟨hddec, hdtarget⟩⟩ hne
    calc
      ∑ f, (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d f *
          kwLocalAngularInternalExitSolution data f e =
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d next *
            kwLocalAngularInternalExitSolution data next e := by
        apply Fintype.sum_eq_single next
        intro f hfn
        by_cases hs : KWOrderedInternalDartStep G
            (data.order) d f
        · have hnf := kwOrderedInternalDartStep_rightUnique G
            (data.order) hstep hs
          exact (hfn hnf.symm).elim
        · rw [kwLocalAngularSplitBlocks_internal_apply_of_not_step
            data weight d f hs, zero_mul]
      _ = data.root (kwPortOfDart G e) := by
        rw [kwLocalAngularSplitBlocks_internal_apply_of_step
            data weight d next hstep, one_mul,
          kwLocalAngularInternalExitSolution_of_faces
            data next e hnextfaces]



theorem kwLocalAngularSplit_internal_mul_exitSolution_of_snd_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hsnd : d.1.snd = kwPortOfDart G e) :
    ((kwLocalAngularSplitBlocks data weight).toBlocks₂₂ *
      kwLocalAngularInternalExitSolution data) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  by_cases hstep : KWOrderedInternalDartStep G
      (data.order) d f
  · have hnot : ¬KWOrderedInternalDartFacesPort
        (data.order) f (kwPortOfDart G e) := by
      intro hfaces
      apply kwOrderedInternalDartStep_not_faces_snd G
        (data.order) hstep
      rwa [hsnd]
    rw [kwLocalAngularSplitBlocks_internal_apply_of_step
        data weight d f hstep, one_mul,
      kwLocalAngularInternalExitSolution_of_not_faces data f e hnot]
  · rw [kwLocalAngularSplitBlocks_internal_apply_of_not_step
        data weight d f hstep, zero_mul]



theorem kwLocalAngularSplit_internal_mul_exitSolution_of_not_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart)
    (hfaces : ¬KWOrderedInternalDartFacesPort
      (data.order) d (kwPortOfDart G e)) :
    ((kwLocalAngularSplitBlocks data weight).toBlocks₂₂ *
      kwLocalAngularInternalExitSolution data) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  by_cases hstep : KWOrderedInternalDartStep G
      (data.order) d f
  · have hfnot : ¬KWOrderedInternalDartFacesPort
        (data.order) f (kwPortOfDart G e) := by
      intro hffaces
      apply hfaces
      exact kwOrderedInternalDartFacesPort_of_step G
        (data.order) hstep hffaces
    rw [kwLocalAngularSplitBlocks_internal_apply_of_step
        data weight d f hstep, one_mul,
      kwLocalAngularInternalExitSolution_of_not_faces data f e hfnot]
  · rw [kwLocalAngularSplitBlocks_internal_apply_of_not_step
        data weight d f hstep, zero_mul]


theorem kwLocalAngularSplit_exitSolution_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ) :
    (1 - (kwLocalAngularSplitBlocks data weight).toBlocks₂₂) *
        kwLocalAngularInternalExitSolution data =
      (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  ext d e
  by_cases hsnd : d.1.snd = kwPortOfDart G e
  · have hfaces := kwOrderedInternalDartFacesPort_of_snd_eq G
      (data.order) d (kwPortOfDart G e) hsnd
    rw [Matrix.sub_apply,
      kwLocalAngularInternalExitSolution_of_faces data d e hfaces,
      kwLocalAngularSplit_internal_mul_exitSolution_of_snd_eq
        data weight d e hsnd,
      kwLocalAngularSplitBlocks_exit_apply_of_connect
        data weight d e hsnd,
      sub_zero]
  · by_cases hfaces : KWOrderedInternalDartFacesPort
        (data.order) d (kwPortOfDart G e)
    · rw [Matrix.sub_apply,
        kwLocalAngularInternalExitSolution_of_faces data d e hfaces,
        kwLocalAngularSplit_internal_mul_exitSolution_of_faces_of_ne
          data weight d e hfaces hsnd,
        kwLocalAngularSplitBlocks_exit_apply_of_not_connect
          data weight d e hsnd,
        sub_self]
    · rw [Matrix.sub_apply,
        kwLocalAngularInternalExitSolution_of_not_faces data d e hfaces,
        kwLocalAngularSplit_internal_mul_exitSolution_of_not_faces
          data weight d e hfaces,
        kwLocalAngularSplitBlocks_exit_apply_of_not_connect
          data weight d e hsnd,
        sub_zero]



theorem kwLocalAngularSplit_resolvent_mul_exit_eq_solution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (n : ℕ)
    (hpow : (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ ^ n = 0) :
    kwNilpotentResolvent
        (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n *
        (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ =
      kwLocalAngularInternalExitSolution data := by
  calc
    kwNilpotentResolvent
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n *
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ =
        kwNilpotentResolvent
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n *
          ((1 - (kwLocalAngularSplitBlocks data weight).toBlocks₂₂) *
            kwLocalAngularInternalExitSolution data) := by
      rw [kwLocalAngularSplit_exitSolution_equation data weight]
    _ = (kwNilpotentResolvent
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n *
          (1 - (kwLocalAngularSplitBlocks data weight).toBlocks₂₂)) *
          kwLocalAngularInternalExitSolution data := by
      rw [Matrix.mul_assoc]
    _ = kwLocalAngularInternalExitSolution data := by
      rw [kwNilpotentResolvent_mul _ n hpow, Matrix.one_mul]




theorem kwLocalAngularSplit_enter_mul_exitSolution_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : G.Dart) (hde : d.snd = e.fst) (hnb : d.edge ≠ e.edge) :
    ((kwLocalAngularSplitBlocks data weight).toBlocks₁₂ *
      kwLocalAngularInternalExitSolution data) d e =
      weight d.edge * data.phase d e := by
  classical
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hpqfirst : p.1 = q.1 := hpfirst.trans (hde.trans hqfirst.symm)
  have hpq : p ≠ q := by
    intro hpq
    have hdart := congrArg (kwDartOfPort G) hpq
    apply hnb
    have heq : d.symm = e := by simpa [p, q] using hdart
    rw [← heq]
    exact d.edge_symm.symm
  have hrankne : kwOrderedPortRank (data.order) p ≠
      kwOrderedPortRank (data.order) q := by
    intro hrank
    exact hpq (kwDartPort_eq_of_fst_of_orderRank
      (data.order) hpqfirst hrank)
  rw [Matrix.mul_apply]
  rcases lt_or_gt_of_ne hrankne with hrank | hrank
  · have hqcard := ((data.order) q.1 q.2).isLt
    change kwOrderedPortRank (data.order) q <
      Fintype.card (KWOutgoingDart (G := G) q.1) at hqcard
    have hcardeq : Fintype.card (KWOutgoingDart (G := G) p.1) =
        Fintype.card (KWOutgoingDart (G := G) q.1) :=
      congrArg (fun v ↦ Fintype.card (KWOutgoingDart (G := G) v)) hpqfirst
    have hbound : kwOrderedPortRank (data.order) p + 1 <
        Fintype.card (KWOutgoingDart (G := G) p.1) := by omega
    let first := kwOrderedIncreasingInternalDartFrom G
      (data.order) p hbound
    have hfaces : KWOrderedInternalDartFacesPort
        (data.order) first q :=
      kwOrderedIncreasingInternalDartFrom_faces G
        (data.order) p q hpqfirst hrank hbound
    have hconnect : p = first.1.fst := by simp [first]
    calc
      ∑ f, (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d f *
          kwLocalAngularInternalExitSolution data f e =
          (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d first *
            kwLocalAngularInternalExitSolution data first e := by
        apply Fintype.sum_eq_single first
        intro f hne
        by_cases hfconnect : p = f.1.fst
        · by_cases hffaces : KWOrderedInternalDartFacesPort
              (data.order) f q
          · have hffirst := kwOrderedInternalDart_eq_of_fst_eq_of_faces G
                (data.order)
                (hfconnect.symm.trans hconnect) hffaces hfaces
            exact (hne hffirst).elim
          · rw [kwLocalAngularInternalExitSolution_of_not_faces
                data f e (by simpa [q] using hffaces), mul_zero]
        · rw [kwLocalAngularSplitBlocks_enter_apply_of_not_connect
              data weight d f (by simpa [p] using hfconnect), zero_mul]
      _ = weight d.edge * data.phase d e := by
        rw [kwLocalAngularSplitBlocks_enter_apply_of_connect
            data weight d first (by simpa [p] using hconnect),
          kwLocalAngularInternalExitSolution_of_faces
            data first e (by simpa [q] using hfaces)]
        have hphase := kwLocalAngularSplitPhase_endpointProduct_of_rank_lt
          data d e hde (by simpa [p, q] using hrank) first first
          (by simpa [p] using hconnect.symm)
          (by simp [first])
        rw [kwLocalAngularSplitPhase_internal_external] at hphase
        rw [← hphase]
        ring
  · have hbound : 0 <
        kwOrderedPortRank (data.order) p := by omega
    let first := kwOrderedDecreasingInternalDartFrom G
      (data.order) p hbound
    have hfaces : KWOrderedInternalDartFacesPort
        (data.order) first q :=
      kwOrderedDecreasingInternalDartFrom_faces G
        (data.order) p q hpqfirst hrank hbound
    have hconnect : p = first.1.fst := by simp [first]
    calc
      ∑ f, (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d f *
          kwLocalAngularInternalExitSolution data f e =
          (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d first *
            kwLocalAngularInternalExitSolution data first e := by
        apply Fintype.sum_eq_single first
        intro f hne
        by_cases hfconnect : p = f.1.fst
        · by_cases hffaces : KWOrderedInternalDartFacesPort
              (data.order) f q
          · have hffirst := kwOrderedInternalDart_eq_of_fst_eq_of_faces G
                (data.order)
                (hfconnect.symm.trans hconnect) hffaces hfaces
            exact (hne hffirst).elim
          · rw [kwLocalAngularInternalExitSolution_of_not_faces
                data f e (by simpa [q] using hffaces), mul_zero]
        · rw [kwLocalAngularSplitBlocks_enter_apply_of_not_connect
              data weight d f (by simpa [p] using hfconnect), zero_mul]
      _ = weight d.edge * data.phase d e := by
        rw [kwLocalAngularSplitBlocks_enter_apply_of_connect
            data weight d first (by simpa [p] using hconnect),
          kwLocalAngularInternalExitSolution_of_faces
            data first e (by simpa [q] using hfaces)]
        have hphase := kwLocalAngularSplitPhase_endpointProduct_of_rank_gt
          data d e hde (by simpa [p, q] using hrank) first first
          (by simpa [p] using hconnect.symm)
          (by
            have hs := kwOrderedDecreasingInternalDartFrom_rank_snd G
              (data.order) p hbound
            change kwOrderedPortRank (data.order) first.1.snd <
              kwOrderedPortRank (data.order) first.1.fst
            simp only [first, kwOrderedDecreasingInternalDartFrom_fst]
            omega)
        rw [kwLocalAngularSplitPhase_internal_external] at hphase
        rw [← hphase]
        ring



theorem kwLocalAngularSplit_enter_mul_exitSolution_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : G.Dart) (hstep : ¬(d.snd = e.fst ∧ d.edge ≠ e.edge)) :
    ((kwLocalAngularSplitBlocks data weight).toBlocks₁₂ *
      kwLocalAngularInternalExitSolution data) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  by_cases hconnect : p = f.1.fst
  · by_cases hfaces : KWOrderedInternalDartFacesPort
        (data.order) f q
    · exfalso
      apply hstep
      have hpfirst : p.1 = d.snd := by
        have h := kwDartOfPort_fst G p
        simpa [p] using h.symm
      have hqfirst : q.1 = e.fst := by
        have h := kwDartOfPort_fst G q
        simpa [q] using h.symm
      have hfdata := kwOrderedInternalSplitDart_adj_data G
        (data.order) f
      have hde : d.snd = e.fst := by
        rw [← hpfirst, ← hqfirst, hconnect]
        exact hfdata.1.trans hfaces.1
      refine ⟨hde, ?_⟩
      intro hedge
      rw [SimpleGraph.dart_edge_eq_iff] at hedge
      rcases hedge with hedge | hedge
      · rw [hedge] at hde
        exact e.fst_ne_snd hde.symm
      · have hpq : p = q := by
          apply kwDartOfPort_injective G
          simp [p, q, hedge]
        apply kwOrderedInternalDart_not_faces_fst G
          (data.order) f
        have htarget : q = f.1.fst := hpq.symm.trans hconnect
        rwa [← htarget]
    · rw [kwLocalAngularInternalExitSolution_of_not_faces
          data f e (by simpa [q] using hfaces), mul_zero]
  · rw [kwLocalAngularSplitBlocks_enter_apply_of_not_connect
        data weight d f (by simpa [p] using hconnect), zero_mul]



theorem kwLocalAngularSplit_enter_mul_exitSolution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ *
        kwLocalAngularInternalExitSolution data =
      kwGraphTransition G weight data.phase := by
  ext d e
  unfold kwGraphTransition
  by_cases hstep : d.snd = e.fst ∧ d.edge ≠ e.edge
  · rw [if_pos hstep,
      kwLocalAngularSplit_enter_mul_exitSolution_of_step
        data weight d e hstep.1 hstep.2]
  · rw [if_neg hstep,
      kwLocalAngularSplit_enter_mul_exitSolution_of_not_step
        data weight d e hstep]



theorem kwLocalAngularSplit_pathEffective_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (n : ℕ)
    (hpow : (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ ^ n = 0) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ *
        kwNilpotentResolvent
          (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n *
        (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ =
      kwGraphTransition G weight data.phase := by
  rw [Matrix.mul_assoc,
    kwLocalAngularSplit_resolvent_mul_exit_eq_solution
      data weight n hpow,
    kwLocalAngularSplit_enter_mul_exitSolution]





theorem kwLocalAngularSplit_det_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)).det =
      (1 - kwGraphTransition G weight data.phase).det := by
  classical
  let M := kwGraphTransition
    (kwOrderedDartPortSplitGraph G (data.order))
    (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)
  let R := kwLocalAngularSplitBlocks data weight
  obtain ⟨n, hn⟩ := kwOrderedSplitInternalBlock_isNilpotent G
    (data.order) (kwOrderedSplitWeight G weight)
    (kwLocalAngularSplitPhase data)
  change R.toBlocks₂₂ ^ n = 0 at hn
  have hzero : R.toBlocks₁₁ = 0 := by
    exact kwOrderedSplit_externalBlock_eq_zero G
      (data.order) (kwOrderedSplitWeight G weight)
      (kwLocalAngularSplitPhase data)
  have hpath : R.toBlocks₁₂ * kwNilpotentResolvent R.toBlocks₂₂ n *
      R.toBlocks₂₁ = kwGraphTransition G weight data.phase := by
    exact kwLocalAngularSplit_pathEffective_eq_original data weight n hn
  have hsub : kwOrderedSplitTransitionInBlocks G
      (data.order) (1 - M) = 1 - R := by
    ext i j
    simp [kwOrderedSplitTransitionInBlocks, Matrix.reindex_apply,
      Matrix.one_apply, R, M, kwLocalAngularSplitBlocks]
  change (1 - M).det = (1 - kwGraphTransition G weight data.phase).det
  calc
    (1 - M).det =
        (kwOrderedSplitTransitionInBlocks G
          (data.order) (1 - M)).det :=
      (kwOrderedSplitTransitionInBlocks_det G
        (data.order) (1 - M)).symm
    _ = (1 - R).det := by rw [hsub]
    _ = (1 - Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = (1 - kwInternalGadgetTransition 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [hzero]
      rfl
    _ = (1 - kwEliminateAcyclicInternal 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n).det :=
      kw_det_eliminateAcyclicInternal 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n hn
    _ = (1 - kwGraphTransition G weight data.phase).det := by
      unfold kwEliminateAcyclicInternal
      rw [zero_add, hpath]



end StatMech.FrontierA
