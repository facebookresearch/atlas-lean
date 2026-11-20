/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABFiniteAssembly

open Filter Finset Set SimpleGraph Topology
open Asymptotics

namespace StatMech
namespace Sharpness

open ConfigSpace

section FiniteProduct

variable {E : Type*} [Fintype E] [DecidableEq E]


set_option maxHeartbeats 800000 in

theorem abgr_sum_configWeightV (p : E -> Real) :
    ∑ omega : ConfigSpace E, configWeightV p omega = 1 := by
  unfold configWeightV edgeWeightV
  calc
    (∑ omega : E -> Bool, ∏ e : E, if omega e then p e else 1 - p e) =
        ∏ e : E, ∑ b : Bool, if b then p e else 1 - p e :=
      (Fintype.prod_sum (fun e b => if b = true then p e else 1 - p e)).symm
    _ = 1 := by simp


set_option maxHeartbeats 800000 in


theorem abgr_probV_allClosed (p : E -> Real) (t : Finset E) :
    probV p {omega | ∀ e ∈ t, omega e = false} = ∏ e ∈ t, (1 - p e) := by
  let f : E -> Bool -> Real := fun e b =>
    if e ∈ t then (if b then 0 else 1 - p e)
    else (if b then p e else 1 - p e)
  unfold probV configWeightV edgeWeightV
  calc
    (∑ omega : ConfigSpace E,
        {omega | ∀ e ∈ t, omega e = false}.indicator (fun _ => (1 : Real)) omega *
          ∏ e : E, if omega e then p e else 1 - p e) =
        ∑ omega : ConfigSpace E, ∏ e : E, f e (omega e) := by
            apply Finset.sum_congr rfl
            intro omega _
            by_cases hclosed : ∀ e ∈ t, omega e = false
            · have hmem : omega ∈ {omega | ∀ e ∈ t, omega e = false} := hclosed
              rw [Set.indicator_of_mem hmem, one_mul]
              apply Finset.prod_congr rfl
              intro e _
              by_cases he : e ∈ t
              · simp [f, he, hclosed e he]
              · simp [f, he]
            · have hmem : omega ∉ {omega | ∀ e ∈ t, omega e = false} := hclosed
              rw [Set.indicator_of_notMem hmem, zero_mul]
              push_neg at hclosed
              obtain ⟨e, he, hopen⟩ := hclosed
              symm
              apply Finset.prod_eq_zero (Finset.mem_univ e)
              have hopen' : omega e = true := by
                cases h : omega e <;> simp_all
              simp [f, he, hopen']
    _ = ∏ e : E, ∑ b : Bool, f e b := (Fintype.prod_sum f).symm
    _ = ∏ e ∈ t, (1 - p e) := by
      classical
      simp [f]


theorem abgr_probV_anyOpen (p : E -> Real) (t : Finset E) :
    probV p {omega | ∃ e ∈ t, omega e = true} =
      1 - ∏ e ∈ t, (1 - p e) := by
  have hcompl : {omega : ConfigSpace E | ∃ e ∈ t, omega e = true}ᶜ =
      {omega | ∀ e ∈ t, omega e = false} := by
    ext omega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    push_neg
    simp
  have htotal : probV p {omega : ConfigSpace E | ∃ e ∈ t, omega e = true} +
      probV p ({omega : ConfigSpace E | ∃ e ∈ t, omega e = true}ᶜ) = 1 := by
    unfold probV
    rw [← Finset.sum_add_distrib]
    calc
      (∑ omega : ConfigSpace E,
          ({omega | ∃ e ∈ t, omega e = true}.indicator (fun _ => (1 : Real)) omega *
              configWeightV p omega +
            {omega | ∃ e ∈ t, omega e = true}ᶜ.indicator (fun _ => (1 : Real)) omega *
              configWeightV p omega)) =
          ∑ omega : ConfigSpace E, configWeightV p omega := by
            apply Finset.sum_congr rfl
            intro omega _
            by_cases h : ∃ e ∈ t, omega e = true <;> simp [h]
      _ = 1 := abgr_sum_configWeightV p
  rw [hcompl, abgr_probV_allClosed] at htotal
  linarith


noncomputable def abgrMerge (s : Finset E) (gamma : {e // e ∈ s} -> Bool)
    (eta : {e // e ∉ s} -> Bool) : ConfigSpace E :=
  (Equiv.piEquivPiSubtypeProd (fun e : E => e ∈ s) (fun _ => Bool)).symm (gamma, eta)

@[simp] theorem abgrMerge_mem (s : Finset E) (gamma : {e // e ∈ s} -> Bool)
    (eta : {e // e ∉ s} -> Bool) (e : {e // e ∈ s}) :
    abgrMerge s gamma eta e = gamma e := by
  simp [abgrMerge]

@[simp] theorem abgrMerge_notMem (s : Finset E) (gamma : {e // e ∈ s} -> Bool)
    (eta : {e // e ∉ s} -> Bool) (e : {e // e ∉ s}) :
    abgrMerge s gamma eta e = eta e := by
  change (if h : (e : E) ∈ s then gamma ⟨e, h⟩ else eta ⟨e, h⟩) = eta e
  rw [dif_neg e.property]

set_option maxHeartbeats 800000 in


theorem abgr_probV_split (s : Finset E) (q : Real) (p : E -> Real)
    (A : Set (ConfigSpace E)) :
    probV (paramOn s q p) A =
      ∑ eta : {e // e ∉ s} -> Bool,
        (∏ e : {e // e ∉ s}, if eta e then p e else 1 - p e) *
          probV (fun _ : {e // e ∈ s} => q)
            {gamma | abgrMerge s gamma eta ∈ A} := by
  unfold probV
  rw [← Equiv.sum_comp
    (Equiv.piEquivPiSubtypeProd (fun e : E => e ∈ s) (fun _ => Bool)).symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro gamma _
  rw [configWeightV_paramOn_factor]
  unfold configWeightV edgeWeightV
  rw [Finset.prod_subtype (p := fun e : E => e ∈ s) s (by simp)]
  rw [Finset.prod_subtype (p := fun e : E => e ∉ s) (Finset.univ \ s) (by simp)]
  change
    A.indicator (fun _ => (1 : Real)) (abgrMerge s gamma eta) *
        ((∏ e : {e // e ∈ s}, if abgrMerge s gamma eta e then q else 1 - q) *
          (∏ e : {e // e ∉ s},
            if abgrMerge s gamma eta e then p e else 1 - p e)) =
      (∏ e : {e // e ∉ s}, if eta e then p e else 1 - p e) *
        ({gamma | abgrMerge s gamma eta ∈ A}.indicator (fun _ => (1 : Real)) gamma *
          ∏ e : {e // e ∈ s}, if gamma e then q else 1 - q)
  simp only [abgrMerge_mem, abgrMerge_notMem]
  by_cases hA : abgrMerge s gamma eta ∈ A <;> simp [hA] <;> ring

end FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abgrKeepGhost (x : V) (omega : ConfigSpace (Sym2 (Option V))) :
    ConfigSpace (Sym2 (Option V)) := fun e =>
  if e = s(some x, none) then omega e
  else if e ∈ FieldGhostDict.ghostEdges V then false else omega e


noncomputable def abgrCloseGhost (omega : ConfigSpace (Sym2 (Option V))) :
    ConfigSpace (Sym2 (Option V)) := fun e =>
  if e ∈ FieldGhostDict.ghostEdges V then false else omega e

@[simp] theorem abgrKeepGhost_chosen (x : V) (omega : ConfigSpace (Sym2 (Option V))) :
    abgrKeepGhost x omega s(some x, none) = omega s(some x, none) := by
  simp [abgrKeepGhost]

@[simp] theorem abgrKeepGhost_physical (x a b : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    abgrKeepGhost x omega s(some a, some b) = omega s(some a, some b) := by
  simp [abgrKeepGhost, FieldGhostDict.ghostEdges, Sym2.eq_iff]

theorem abgrKeepGhost_le (x : V) (omega : ConfigSpace (Sym2 (Option V))) :
    abgrKeepGhost x omega <= omega := by
  intro e
  unfold abgrKeepGhost
  split_ifs <;> simp_all

@[simp] theorem abgrCloseGhost_ghost (x : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    abgrCloseGhost omega s(some x, none) = false := by
  simp [abgrCloseGhost, FieldGhostDict.ghostEdges]

@[simp] theorem abgrCloseGhost_physical (a b : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    abgrCloseGhost omega s(some a, some b) = omega s(some a, some b) := by
  simp [abgrCloseGhost, FieldGhostDict.ghostEdges]

theorem abgrCloseGhost_le (omega : ConfigSpace (Sym2 (Option V))) :
    abgrCloseGhost omega <= omega := by
  intro e
  unfold abgrCloseGhost
  split_ifs <;> simp_all



private theorem abgr_exists_keepGhost_walk (omega : ConfigSpace (Sym2 (Option V)))
    {u v : Option V} (p : (openSub (withGhost G) omega).Walk u v) :
    ∀ a : V, u = some a -> v = none ->
      ∃ x : V, omega s(some x, none) = true ∧
        (openSub (withGhost G) (abgrKeepGhost x omega)).Reachable u v := by
  induction p with
  | nil =>
      intro a ha hv
      simp_all
  | @cons u v w huv q ih =>
      intro a ha hw
      subst u
      subst w
      rcases v with _ | b
      · have hopen : omega s(some a, none) = true := by
          simpa [openSub] using huv.2
        refine ⟨a, hopen, ?_⟩
        exact (show (openSub (withGhost G) (abgrKeepGhost a omega)).Adj
          (some a) none from ⟨huv.1, by simpa using hopen⟩).reachable
      · obtain ⟨x, hxopen, hxconn⟩ := ih b rfl rfl
        refine ⟨x, hxopen, ?_⟩
        have hstep :
            (openSub (withGhost G) (abgrKeepGhost x omega)).Adj (some a) (some b) := by
          refine ⟨huv.1, ?_⟩
          simpa using huv.2
        exact hstep.reachable.trans hxconn



private theorem abgr_exists_closeGhost_walk (omega : ConfigSpace (Sym2 (Option V)))
    {u v : Option V} (p : (openSub (withGhost G) omega).Walk u v) :
    ∀ a : V, u = some a -> v = none ->
      ∃ x : V, omega s(some x, none) = true ∧
        (openSub (withGhost G) (abgrCloseGhost omega)).Reachable u (some x) := by
  induction p with
  | nil =>
      intro a ha hv
      simp_all
  | @cons u v w huv q ih =>
      intro a ha hw
      subst u
      subst w
      rcases v with _ | b
      · have hopen : omega s(some a, none) = true := by
          simpa [openSub] using huv.2
        exact ⟨a, hopen, Reachable.refl _⟩
      · obtain ⟨x, hxopen, hxconn⟩ := ih b rfl rfl
        refine ⟨x, hxopen, ?_⟩
        have hstep :
            (openSub (withGhost G) (abgrCloseGhost omega)).Adj (some a) (some b) := by
          refine ⟨huv.1, ?_⟩
          simpa using huv.2
        exact hstep.reachable.trans hxconn




theorem abgr_connEvent_iff_exists_keepGhost (o : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ x : V, omega s(some x, none) = true ∧
        abgrKeepGhost x omega ∈ connEvent (withGhost G) Set.univ (some o) {none} := by
  constructor
  · rintro ⟨ho, b, hb, hbg, hconn⟩
    simp only [Set.mem_singleton_iff] at hbg
    subst b
    obtain ⟨p⟩ := hconn
    let q := p.map (SimpleGraph.Embedding.induce Set.univ).toHom
    obtain ⟨x, hxopen, hxconn⟩ :=
      abgr_exists_keepGhost_walk G omega q o rfl rfl
    exact ⟨x, hxopen, ho, none, Set.mem_univ _, Set.mem_singleton _,
      hxconn.elim fun walk => ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩
  · rintro ⟨x, hxopen, hxconn⟩
    exact isIncreasing_connEvent (withGhost G) Set.univ (some o) {none}
      (abgrKeepGhost_le x omega) hxconn


theorem abgr_connEvent_iff_exists_physical (o : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ x : V, omega s(some x, none) = true ∧
        abgrCloseGhost omega ∈
          connEvent (withGhost G) Set.univ (some o) {some x} := by
  constructor
  · rintro ⟨ho, b, hb, hbg, hconn⟩
    simp only [Set.mem_singleton_iff] at hbg
    subst b
    obtain ⟨p⟩ := hconn
    let q := p.map (SimpleGraph.Embedding.induce Set.univ).toHom
    obtain ⟨x, hxopen, hxconn⟩ :=
      abgr_exists_closeGhost_walk G omega q o rfl rfl
    exact ⟨x, hxopen, Set.mem_univ _, some x, Set.mem_univ _, Set.mem_singleton _,
      hxconn.elim fun walk => ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩
  · rintro ⟨x, hxopen, ho, b, hb, hbx, hconn⟩
    simp only [Set.mem_singleton_iff] at hbx
    subst b
    obtain ⟨p⟩ := hconn
    let q := p.map (SimpleGraph.Embedding.induce Set.univ).toHom
    have hstep : (openSub (withGhost G) omega).Adj (some x) none :=
      ⟨withGhost_adj_some_ghost G x, hxopen⟩
    have hq : (openSub (withGhost G) omega).Reachable (some o) (some x) := by
      exact q.reachable.mono (openSub_mono (withGhost G) (abgrCloseGhost_le omega))
    exact ⟨Set.mem_univ _, none, Set.mem_univ _, Set.mem_singleton _,
      (hq.trans hstep.reachable).elim fun walk =>
        ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩


noncomputable def abgrActive (o : V) (omega : ConfigSpace (Sym2 (Option V))) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun x =>
      abgrCloseGhost omega ∈ connEvent (withGhost G) Set.univ (some o) {some x}

theorem abgr_connEvent_iff_exists_active (o : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ x ∈ abgrActive (G := G) o omega, omega s(some x, none) = true := by
  rw [abgr_connEvent_iff_exists_physical G o omega]
  simp only [abgrActive, Finset.mem_filter, Finset.mem_univ, true_and]
  aesop


noncomputable def abgrGhostEdgeEquiv :
    V ≃ {e : Sym2 (Option V) // e ∈ FieldGhostDict.ghostEdges V} :=
  Equiv.ofBijective
    (fun x : V => (⟨s(some x, none), by
      simp [FieldGhostDict.ghostEdges]⟩ :
        {e : Sym2 (Option V) // e ∈ FieldGhostDict.ghostEdges V}))
    ⟨by
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      rw [Sym2.eq_iff] at hxy
      rcases hxy with hxy | hxy
      · exact Option.some.inj hxy.1
      · simp at hxy,
    by
      intro e
      rcases e with ⟨e, he⟩
      simp only [FieldGhostDict.ghostEdges, Finset.mem_image,
        Finset.mem_univ, true_and] at he
      obtain ⟨x, rfl⟩ := he
      exact ⟨x, rfl⟩⟩

@[simp] theorem abgrGhostEdgeEquiv_apply (x : V) :
    (abgrGhostEdgeEquiv (V := V) x : Sym2 (Option V)) = s(some x, none) := rfl



theorem abgrCloseGhost_merge_eq
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    abgrCloseGhost (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) =
      abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta := by
  funext e
  by_cases he : e ∈ FieldGhostDict.ghostEdges V
  · rw [show abgrCloseGhost
        (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) e = false by
          simp [abgrCloseGhost, he]]
    exact (abgrMerge_mem (FieldGhostDict.ghostEdges V) (fun _ => false) eta ⟨e, he⟩).symm
  · rw [show abgrCloseGhost
        (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) e =
          abgrMerge (FieldGhostDict.ghostEdges V) gamma eta e by
          simp [abgrCloseGhost, he]]
    rw [abgrMerge_notMem (FieldGhostDict.ghostEdges V) gamma eta ⟨e, he⟩]
    rw [abgrMerge_notMem (FieldGhostDict.ghostEdges V) (fun _ => false) eta ⟨e, he⟩]


noncomputable def abgrActiveGhost (o : V)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    Finset {e // e ∈ FieldGhostDict.ghostEdges V} :=
  (abgrActive (G := G) o
    (abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta)).map
      (abgrGhostEdgeEquiv (V := V)).toEmbedding

theorem abgrActive_merge_eq (o : V)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    abgrActive (G := G) o
        (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) =
      abgrActive (G := G) o
        (abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta) := by
  unfold abgrActive
  rw [abgrCloseGhost_merge_eq gamma eta]
  rw [abgrCloseGhost_merge_eq (fun _ => false) eta]



theorem abgr_section_iff_anyOpen (o : V)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈
        connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ e ∈ abgrActiveGhost G o eta, gamma e = true := by
  rw [abgr_connEvent_iff_exists_active G o]
  constructor
  · rintro ⟨x, hx, hopen⟩
    rw [abgrActive_merge_eq G o gamma eta] at hx
    refine ⟨abgrGhostEdgeEquiv (V := V) x, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · rw [← abgrMerge_mem (FieldGhostDict.ghostEdges V) gamma eta
          (abgrGhostEdgeEquiv (V := V) x)]
      simpa only [abgrGhostEdgeEquiv_apply] using hopen
  · rintro ⟨e, he, hopen⟩
    rw [abgrActiveGhost, Finset.mem_map] at he
    obtain ⟨x, hx, hxe⟩ := he
    subst e
    refine ⟨x, ?_, ?_⟩
    · rwa [abgrActive_merge_eq G o gamma eta]
    · calc
        abgrMerge (FieldGhostDict.ghostEdges V) gamma eta s(some x, none) =
            gamma (abgrGhostEdgeEquiv (V := V) x) := by
              rw [← abgrGhostEdgeEquiv_apply x]
              exact abgrMerge_mem (FieldGhostDict.ghostEdges V) gamma eta
                (abgrGhostEdgeEquiv (V := V) x)
        _ = true := hopen



theorem abgr_abfaMag_eq_cluster_mixture (J : Sym2 V -> Real) (o : V)
    (beta h : Real) :
    abfaMag G J o beta h =
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        (∏ e : {e // e ∉ FieldGhostDict.ghostEdges V},
          if eta e then pBeta (abfaLiftCoupling G J e) beta
          else 1 - pBeta (abfaLiftCoupling G J e) beta) *
        (1 - (1 - qField h) ^ (abgrActiveGhost G o eta).card) := by
  unfold abfaMag abfaParams abpdBetaFieldParams
  rw [abgr_probV_split]
  apply Finset.sum_congr rfl
  intro eta _
  congr 1
  have hset :
      {gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool |
          abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈
            connEvent (withGhost G) Set.univ (some o) {none}} =
        {gamma | ∃ e ∈ abgrActiveGhost G o eta, gamma e = true} := by
    ext gamma
    exact abgr_section_iff_anyOpen G o gamma eta
  rw [hset, abgr_probV_anyOpen]
  simp


noncomputable def abgrOffWeight (J : Sym2 V -> Real) (beta : Real)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) : Real :=
  ∏ e : {e // e ∉ FieldGhostDict.ghostEdges V},
    if eta e then pBeta (abfaLiftCoupling G J e) beta
    else 1 - pBeta (abfaLiftCoupling G J e) beta

theorem abgr_sum_offWeight (J : Sym2 V -> Real) (beta : Real) :
    ∑ eta, abgrOffWeight G J beta eta = 1 := by
  simpa [abgrOffWeight, configWeightV, edgeWeightV] using
    (abgr_sum_configWeightV
      (fun e : {e // e ∉ FieldGhostDict.ghostEdges V} =>
        pBeta (abfaLiftCoupling G J e) beta))

theorem abgr_offWeight_nonneg (J : Sym2 V -> Real) (beta : Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (hbeta : 0 ≤ beta)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    0 ≤ abgrOffWeight G J beta eta := by
  unfold abgrOffWeight
  apply Finset.prod_nonneg
  intro e _
  have hcoupling := abfaLiftCoupling_nonneg G J hJ e
  by_cases hopen : eta e
  · simp only [hopen, if_true]
    exact pBeta_nonneg (mul_nonneg hbeta hcoupling)
  · simp only [hopen]
    exact sub_nonneg.mpr (pBeta_lt_one (abfaLiftCoupling G J e) beta).le



theorem abgr_cluster_profile_eq_exp (h : Real) (k : Nat) :
    1 - (1 - qField h) ^ k = 1 - Real.exp (-(h * k)) := by
  simp only [qField, sub_sub_cancel]
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring


theorem abgr_hasDerivAt_abfaMag_field (J : Sym2 V -> Real) (o : V)
    (beta h : Real) :
    HasDerivAt (fun t => abfaMag G J o beta t)
      (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          ((abgrActiveGhost G o eta).card *
            Real.exp (-(h * (abgrActiveGhost G o eta).card)))) h := by
  have hfun : (fun t => abfaMag G J o beta t) =
      fun t => ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (1 - Real.exp (-(t * (abgrActiveGhost G o eta).card))) := by
    funext t
    rw [abgr_abfaMag_eq_cluster_mixture]
    apply Finset.sum_congr rfl
    intro eta _
    rw [abgr_cluster_profile_eq_exp]
    rfl
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro eta _
  let k : Real := (abgrActiveGhost G o eta).card
  have hexp : HasDerivAt (fun t => Real.exp (-(t * k))) (-k * Real.exp (-(h * k))) h := by
    convert (Real.hasDerivAt_exp (-(h * k))).comp h
      (((hasDerivAt_id h).mul_const k).neg) using 1 <;> ring
  have hprofile : HasDerivAt (fun t => 1 - Real.exp (-(t * k)))
      (k * Real.exp (-(h * k))) h := by
    convert (hasDerivAt_const h (1 : Real)).sub hexp using 1 <;> ring
  convert hprofile.const_mul (abgrOffWeight G J beta eta) using 1 <;> rfl


theorem abgr_hasDerivAt_deriv_abfaMag_field (J : Sym2 V -> Real) (o : V)
    (beta h : Real) :
    HasDerivAt (fun t => deriv (fun u => abfaMag G J o beta u) t)
      (-(∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (((abgrActiveGhost G o eta).card : Real) ^ 2 *
            Real.exp (-(h * (abgrActiveGhost G o eta).card))))) h := by
  have hderiv : (fun t => deriv (fun u => abfaMag G J o beta u) t) =
      fun t => ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          ((abgrActiveGhost G o eta).card *
            Real.exp (-(t * (abgrActiveGhost G o eta).card))) := by
    funext t
    exact (abgr_hasDerivAt_abfaMag_field G J o beta t).deriv
  rw [hderiv]
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro eta _
  let k : Real := (abgrActiveGhost G o eta).card
  have hexp : HasDerivAt (fun t => Real.exp (-(t * k))) (-k * Real.exp (-(h * k))) h := by
    convert (Real.hasDerivAt_exp (-(h * k))).comp h
      (((hasDerivAt_id h).mul_const k).neg) using 1 <;> ring
  convert (hexp.const_mul k).const_mul (abgrOffWeight G J beta eta) using 1 <;> ring


theorem abgr_nat_mul_exp_le_inv (h : Real) (hh : 0 < h) (k : Nat) :
    (k : Real) * Real.exp (-(h * k)) ≤ 1 / h := by
  have hbase := Real.mul_exp_neg_le_exp_neg_one (h * (k : Real))
  have hexp : Real.exp (-(1 : Real)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by norm_num)
  rw [le_div_iff₀ hh]
  calc
    (k : Real) * Real.exp (-(h * k)) * h =
        (h * (k : Real)) * Real.exp (-(h * k)) := by ring
    _ ≤ Real.exp (-(1 : Real)) := hbase
    _ ≤ 1 := hexp


theorem abgr_nat_sq_mul_exp_le (h : Real) (hh : 0 < h) (k : Nat) :
    (k : Real) ^ 2 * Real.exp (-(h * k)) ≤ 2 / h ^ 2 := by
  let y : Real := h * (k : Real)
  have hy : 0 ≤ y := mul_nonneg hh.le (Nat.cast_nonneg k)
  have hquad : y ^ 2 / 2 ≤ Real.exp y := by
    have h := Real.quadratic_le_exp_of_nonneg hy
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-y)).le
  have hdecay : y ^ 2 * Real.exp (-y) ≤ 2 := by
    have hexpcancel : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hexpcancel] at hm
    nlinarith
  rw [div_eq_mul_inv, le_mul_inv_iff₀ (sq_pos_of_pos hh)]
  calc
    (k : Real) ^ 2 * Real.exp (-(h * k)) * h ^ 2 =
        y ^ 2 * Real.exp (-y) := by simp [y]; ring
    _ ≤ 2 := hdecay



theorem abgr_deriv_abfaMag_field_le (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (o : V)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 < h) :
    deriv (fun t => abfaMag G J o beta t) h ≤ 1 / h := by
  rw [(abgr_hasDerivAt_abfaMag_field G J o beta h).deriv]
  calc
    (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          ((abgrActiveGhost G o eta).card *
            Real.exp (-(h * (abgrActiveGhost G o eta).card)))) ≤
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta * (1 / h) := by
          apply Finset.sum_le_sum
          intro eta _
          exact mul_le_mul_of_nonneg_left
            (abgr_nat_mul_exp_le_inv h hh (abgrActiveGhost G o eta).card)
            (abgr_offWeight_nonneg G J beta hJ hbeta eta)
    _ = 1 / h := by
      rw [← Finset.sum_mul, abgr_sum_offWeight]
      ring



theorem abgr_abs_deriv_deriv_abfaMag_field_le (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (o : V)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 < h) :
    |deriv (fun t => deriv (fun u => abfaMag G J o beta u) t) h| ≤ 2 / h ^ 2 := by
  rw [(abgr_hasDerivAt_deriv_abfaMag_field G J o beta h).deriv]
  rw [abs_neg]
  have hsum_nonneg : 0 ≤
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (((abgrActiveGhost G o eta).card : Real) ^ 2 *
            Real.exp (-(h * (abgrActiveGhost G o eta).card))) := by
    apply Finset.sum_nonneg
    intro eta _
    exact mul_nonneg (abgr_offWeight_nonneg G J beta hJ hbeta eta)
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  rw [abs_of_nonneg hsum_nonneg]
  calc
    (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (((abgrActiveGhost G o eta).card : Real) ^ 2 *
            Real.exp (-(h * (abgrActiveGhost G o eta).card)))) ≤
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta * (2 / h ^ 2) := by
          apply Finset.sum_le_sum
          intro eta _
          exact mul_le_mul_of_nonneg_left
            (abgr_nat_sq_mul_exp_le h hh (abgrActiveGhost G o eta).card)
            (abgr_offWeight_nonneg G J beta hJ hbeta eta)
    _ = 2 / h ^ 2 := by
      rw [← Finset.sum_mul, abgr_sum_offWeight]
      ring



theorem abgr_taylor_remainder_le (f : Real -> Real) (x y K : Real)
    (hK : 0 <= K)
    (hfdiff : forall (z : Real), z ∈ Set.uIcc x y -> DifferentiableAt Real f z)
    (hf'diff : forall (z : Real), z ∈ Set.uIcc x y ->
      DifferentiableAt Real (fun t => deriv f t) z)
    (hf'bound : forall (z : Real), z ∈ Set.uIcc x y ->
      |deriv (fun t => deriv f t) z| <= K) :
    |f y - f x - deriv f x * (y - x)| <= K * |y - x| ^ 2 := by
  have hderivLip : forall (z : Real), z ∈ Set.uIcc x y ->
      |deriv f z - deriv f x| <= K * |z - x| := by
    intro z hz
    have hsub : Set.uIcc x z ⊆ Set.uIcc x y :=
      uIcc_subset_uIcc left_mem_uIcc hz
    have hmvt := (convex_uIcc x z).norm_image_sub_le_of_norm_deriv_le
      (f := fun t => deriv f t) (C := K)
      (fun u hu => hf'diff u (hsub hu))
      (fun u hu => by
        rw [Real.norm_eq_abs]
        exact hf'bound u (hsub hu))
      left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using hmvt
  let g : Real -> Real := fun z => f z - deriv f x * z
  have hgdiff : forall (z : Real), z ∈ Set.uIcc x y -> DifferentiableAt Real g z := by
    intro z hz
    exact (hfdiff z hz).sub ((differentiableAt_const (c := deriv f x)).mul
      differentiableAt_id)
  have hgderiv : forall (z : Real), z ∈ Set.uIcc x y ->
      deriv g z = deriv f z - deriv f x := by
    intro z hz
    have hconst : HasDerivAt (fun t : Real => deriv f x * t) (deriv f x) z := by
      simpa using (hasDerivAt_id z).const_mul (deriv f x)
    exact ((hfdiff z hz).hasDerivAt.sub hconst).deriv
  have hgbound : forall (z : Real), z ∈ Set.uIcc x y ->
      ‖deriv g z‖ <= K * |y - x| := by
    intro z hz
    rw [hgderiv z hz, Real.norm_eq_abs]
    exact (hderivLip z hz).trans
      (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz) hK)
  have hmvt := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le
    (f := g) (C := K * |y - x|) hgdiff hgbound
    left_mem_uIcc right_mem_uIcc
  change |(f y - deriv f x * y) - (f x - deriv f x * x)| <=
    (K * |y - x|) * |y - x| at hmvt
  convert hmvt using 1 <;> ring




theorem abgr_hasDerivAt_limit_of_taylor
    (f : Nat -> Real -> Real) (g : Real -> Real) (d : Nat -> Real)
    (x r K : Real) (hr : 0 < r) (hK : 0 <= K)
    (hlim : forall y, |y - x| < r -> Tendsto (fun n => f n y) atTop (nhds (g y)))
    (htaylor : forall n y, |y - x| < r ->
      |f n y - f n x - d n * (y - x)| <= K * |y - x| ^ 2) :
    exists L, HasDerivAt g L x := by
  have hdCauchy : CauchySeq d := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    let delta : Real := min (r / 2) (epsilon / (6 * (K + 1)))
    have hK1 : 0 < K + 1 := by linarith
    have hdelta : 0 < delta := by
      dsimp [delta]
      positivity
    have hdeltar : delta < r := by
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let y : Real := x + delta
    have hy : |y - x| < r := by
      simp [y, abs_of_pos hdelta, hdeltar]
    let slope : Nat -> Real := fun n => (f n y - f n x) / delta
    have hslope : Tendsto slope atTop (nhds ((g y - g x) / delta)) := by
      apply Tendsto.div_const
      exact (hlim y hy).sub (hlim x (by simpa using hr))
    have hslopeCauchy : CauchySeq slope := hslope.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hslopeCauchy)
      (epsilon / 3) (by linarith)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hslopeDist : |slope m - slope n| < epsilon / 3 := by
      simpa [Real.dist_eq] using hN m hm n hn
    have hclose : forall j, |d j - slope j| <= K * delta := by
      intro j
      have hrem := htaylor j y hy
      have habsdelta : |delta| = delta := abs_of_pos hdelta
      dsimp [slope]
      rw [show d j - (f j y - f j x) / delta =
          -(f j y - f j x - d j * (y - x)) / delta by
            simp [y]; field_simp]
      rw [abs_div, abs_neg, habsdelta]
      apply (div_le_iff₀ hdelta).mpr
      simpa [y, habsdelta, pow_two, mul_assoc] using hrem
    have hKdelta : K * delta <= epsilon / 6 := by
      have hdeltaBound : delta <= epsilon / (6 * (K + 1)) := min_le_right _ _
      have hmul : (K + 1) * delta <= epsilon / 6 := by
        apply (le_div_iff₀ (by positivity : 0 < (6 : Real))).mpr
        have := (mul_le_mul_of_nonneg_left hdeltaBound
          (show 0 <= 6 * (K + 1) by positivity))
        field_simp at this ⊢
        nlinarith
      exact (mul_le_mul_of_nonneg_right (by linarith : K <= K + 1)
        hdelta.le).trans hmul
    rw [Real.dist_eq]
    calc
      |d m - d n| <= |d m - slope m| + |slope m - slope n| +
          |slope n - d n| := by
        calc
          |d m - d n| <= |d m - slope m| + |slope m - d n| := abs_sub_le _ _ _
          _ <= |d m - slope m| +
              (|slope m - slope n| + |slope n - d n|) := by
                gcongr
                exact abs_sub_le _ _ _
          _ = _ := by ring
      _ < epsilon := by
        have hnclose : |slope n - d n| <= K * delta := by
          rw [abs_sub_comm]
          exact hclose n
        linarith [hclose m, hslopeDist, hKdelta]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hdCauchy
  refine ⟨L, HasDerivAt.of_isLittleO ?_⟩
  have hrem : forall y, |y - x| < r ->
      |g y - g x - (y - x) * L| <= K * |y - x| ^ 2 := by
    intro y hy
    have htend : Tendsto
        (fun n => |f n y - f n x - d n * (y - x)|) atTop
        (nhds |g y - g x - L * (y - x)|) :=
      (((hlim y hy).sub (hlim x (by simpa using hr))).sub
        (hL.mul_const (y - x))).abs
    have hbound := le_of_tendsto htend
      (Filter.Eventually.of_forall (fun n => htaylor n y hy))
    simpa [mul_comm] using hbound
  have hbig : (fun y => g y - g x - (y - x) * L) =O[nhds x]
      (fun y => ‖y - x‖ ^ 2) := by
    apply IsBigO.of_bound K
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    simpa [Real.norm_eq_abs, abs_nonneg] using hrem y hy
  exact hbig.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

end Sharpness
end StatMech
