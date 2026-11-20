/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardArbitraryValenceReduction
import Code.FrontierA.SurfaceKacWardTwist

















open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u



def KWGraphWeightedCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex) : Prop :=
  (forall {root : V} (p : G.Walk root root), p.IsCycle ->
      kwGraphFormalLogCoeff G phase
        (ons_finsetExponent p.edges.toFinset) =
      cycleCoeff p.edges.toFinset) /\
  (forall (S : Finset (Sym2 V)),
      kwGraphFormalLogCoeff G phase (ons_finsetExponent S) ≠ 0 ->
        exists (root : V) (p : G.Walk root root),
          p.IsCycle /\ p.edges.toFinset = S)



noncomputable def kwWeightedCycleComponentSeries
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex) : MvPowerSeries (Sym2 V) Complex :=
  ∑ i : I, MvPowerSeries.monomial
    (ons_finsetExponent (cycle i).edges.toFinset) (coefficient i)

theorem kwWeightedCycleComponentSeries_coeff
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex) (m : Sym2 V →₀ Nat) :
    MvPowerSeries.coeff m
        (kwWeightedCycleComponentSeries base cycle coefficient) =
      ∑ i : I, if ons_finsetExponent (cycle i).edges.toFinset = m then
        coefficient i else 0 := by
  classical
  unfold kwWeightedCycleComponentSeries
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPowerSeries.coeff_monomial]
  by_cases heq : ons_finsetExponent (cycle i).edges.toFinset = m
  · rw [if_pos heq.symm, if_pos heq]
  · rw [if_neg (Ne.symm heq), if_neg heq]

theorem kwWeightedCycleComponentSeries_coeff_piece
    {V I : Type u} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset)) (j : I) :
    MvPowerSeries.coeff
        (ons_finsetExponent (cycle j).edges.toFinset)
        (kwWeightedCycleComponentSeries base cycle coefficient) =
      coefficient j := by
  classical
  rw [kwWeightedCycleComponentSeries_coeff, Fintype.sum_eq_single j]
  · simp
  · intro i hij
    rw [if_neg]
    intro heq
    apply hij
    apply ons_cycle_decomposition_edgeSet_injective base cycle hcycle hdisj
    exact ons_finsetExponent_injective heq

theorem kwWeightedCycleComponentSeries_hasSubst
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle) :
    PowerSeries.HasSubst
      (kwWeightedCycleComponentSeries base cycle coefficient) := by
  classical
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
    kwWeightedCycleComponentSeries_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  intro heq
  apply (ons_cycle_edges_toFinset_nonempty (cycle i) (hcycle i)).ne_empty
  apply ons_finsetExponent_injective
  simpa [ons_finsetExponent] using heq



theorem kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag
    {V I : Type u} {K : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [DecidableEq K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex)
    (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G)
    (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (hcycle : forall i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i => (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset))
    (T : Finset K) (g : K →₀ Sym2 V →₀ Nat)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : K} (hi : i ∈ T) :
    kwGraphFormalLogCoeff G phase (g i) =
      MvPowerSeries.coeff (g i)
        (kwWeightedCycleComponentSeries base cycle
          (fun j => cycleCoeff (cycle j).edges.toFinset)) := by
  classical
  have hcomponent :=
    ons_finsuppAntidiag_finsetExponent_component T S g hg hi
  by_cases hexists : exists j : I,
      (g i).support = (cycle j).edges.toFinset
  · obtain ⟨j, hj⟩ := hexists
    have hgi : g i = ons_finsetExponent (cycle j).edges.toFinset := by
      calc
        g i = ons_finsetExponent (g i).support := hcomponent
        _ = ons_finsetExponent (cycle j).edges.toFinset := congrArg _ hj
    rw [hgi, hlog.1 (cycle j) (hcycle j)]
    exact (kwWeightedCycleComponentSeries_coeff_piece
      base cycle (fun j => cycleCoeff (cycle j).edges.toFinset)
        hcycle hdisj j).symm
  · have hleft : kwGraphFormalLogCoeff G phase (g i) = 0 := by
      by_contra hne
      have hcoeffEq : kwGraphFormalLogCoeff G phase
          (ons_finsetExponent (g i).support) ≠ 0 := by
        rw [← hcomponent]
        exact hne
      obtain ⟨root, q, hq, hqedges⟩ := hlog.2 (g i).support hcoeffEq
      have hqsub : q.edges.toFinset ⊆ S := by
        rw [hqedges]
        exact ons_finsuppAntidiag_finsetExponent_support_subset
          T S g hg hi
      obtain ⟨j, hjedges⟩ := ons_cycle_edges_eq_decomposition_piece
        G hdeg S hS base cycle hcycle hcover q hq hqsub
      exact hexists ⟨j, hqedges.symm.trans hjedges⟩
    have hright : MvPowerSeries.coeff (g i)
        (kwWeightedCycleComponentSeries base cycle
          (fun j => cycleCoeff (cycle j).edges.toFinset)) = 0 := by
      rw [kwWeightedCycleComponentSeries_coeff]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro heq
      apply hexists
      refine ⟨j, ?_⟩
      apply ons_finsetExponent_injective
      calc
        ons_finsetExponent (g i).support = g i := hcomponent.symm
        _ = ons_finsetExponent (cycle j).edges.toFinset := heq.symm
    rw [hleft, hright]

theorem kwWeightedCycleComponentSeries_pow_coeff
    {V I : Type u} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (S : Finset (Sym2 V)) (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i => (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset)) (n : Nat) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        ((kwWeightedCycleComponentSeries base cycle coefficient) ^ n) =
      if n = Fintype.card I then
        (n.factorial : Complex) * ∏ i, coefficient i
      else 0 := by
  classical
  let exponent : I -> Sym2 V →₀ Nat :=
    fun i => ons_finsetExponent (cycle i).edges.toFinset
  have hnonempty : forall i, ((cycle i).edges.toFinset).Nonempty :=
    fun i => ons_cycle_edges_toFinset_nonempty (cycle i) (hcycle i)
  have hexponent (f : Fin n -> I) :
      (∑ k, exponent (f k)) = ons_finsetExponent S ↔
        Function.Bijective f := by
    exact ons_sum_finsetExponent_eq_iff_bijective S
      (fun i => (cycle i).edges.toFinset) hcover hdisj hnonempty n f
  have hprod (f : Fin n -> I) :
      (∏ k, MvPowerSeries.monomial
        (exponent (f k)) (coefficient (f k))) =
        MvPowerSeries.monomial (∑ k, exponent (f k))
          (∏ k, coefficient (f k)) := by
    simpa using MvPowerSeries.prod_monomial
      (fun k => exponent (f k)) (fun k => coefficient (f k)) Finset.univ
  have hsumForm :
      MvPowerSeries.coeff (ons_finsetExponent S)
          ((kwWeightedCycleComponentSeries base cycle coefficient) ^ n) =
        ∑ f : Fin n -> I,
          if Function.Bijective f then ∏ k, coefficient (f k) else 0 := by
    unfold kwWeightedCycleComponentSeries
    change MvPowerSeries.coeff (ons_finsetExponent S)
      ((∑ i, MvPowerSeries.monomial (exponent i) (coefficient i)) ^ n) = _
    rw [Fintype.sum_pow, map_sum]
    apply Finset.sum_congr rfl
    intro f hf
    rw [hprod, MvPowerSeries.coeff_monomial]
    rw [if_congr (by simpa only [eq_comm] using hexponent f) rfl rfl]
  rw [hsumForm]
  by_cases hn : n = Fintype.card I
  · rw [if_pos hn, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hcardEq : Fintype.card (Fin n) = Fintype.card I := by simpa using hn
    let e : Fin n ≃ I := Fintype.equivOfCardEq hcardEq
    have hcardBij :
        Fintype.card {f : Fin n -> I // Function.Bijective f} =
          n.factorial := by
      calc
        Fintype.card {f : Fin n -> I // Function.Bijective f} =
            Fintype.card (Fin n ≃ I) :=
          Fintype.card_congr Equiv.bijectiveEquiv
        _ = (Fintype.card (Fin n)).factorial := Fintype.card_equiv e
        _ = n.factorial := by simp
    have hcardFilter :
        #{f : Fin n -> I | Function.Bijective f} = n.factorial := by
      rw [← Fintype.card_subtype]
      exact hcardBij
    calc
      (∑ f : Fin n -> I with Function.Bijective f,
          ∏ k, coefficient (f k)) =
          ∑ f : Fin n -> I with Function.Bijective f,
            ∏ i, coefficient i := by
        apply Finset.sum_congr rfl
        intro f hf
        exact (Finset.mem_filter.mp hf).2.prod_comp coefficient
      _ = (n.factorial : Complex) * ∏ i, coefficient i := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardFilter]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro f hf
    rw [if_neg]
    intro hbij
    apply hn
    have hcard := Fintype.card_congr (Equiv.ofBijective f hbij)
    simpa using hcard

theorem kwWeightedCycleComponentExp_coeff
    {V I : Type u} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (S : Finset (Sym2 V)) (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i => (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst
          (kwWeightedCycleComponentSeries base cycle coefficient)
          (PowerSeries.exp Complex)) =
      ∏ i, coefficient i := by
  classical
  rw [PowerSeries.coeff_subst
    (kwWeightedCycleComponentSeries_hasSubst
      base cycle coefficient hcycle)]
  rw [finsum_eq_single _ (Fintype.card I)]
  · rw [kwWeightedCycleComponentSeries_pow_coeff
      S base cycle coefficient hcycle hcover hdisj, if_pos rfl]
    simp only [PowerSeries.coeff_exp, smul_eq_mul]
    rw [one_div, map_inv₀, map_natCast]
    have hfac : ((Fintype.card I).factorial : Complex) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (Fintype.card I)
    field_simp
  · intro n hn
    rw [kwWeightedCycleComponentSeries_pow_coeff
      S base cycle coefficient hcycle hcover hdisj, if_neg hn, smul_zero]


theorem kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex)
    (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    exists (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (base : I -> V)
      (cycle : (i : I) -> G.Walk (base i) (base i)),
      (forall i, (cycle i).IsCycle) /\
      S = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset) /\
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
        (fun i => (cycle i).edges.toFinset) /\
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
        (fun i => (cycle i).toSubgraph.verts) /\
      MvPowerSeries.coeff (ons_finsetExponent S)
          (kwGraphFormalRoot G phase) =
        ∏ i, cycleCoeff (cycle i).edges.toFinset := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hweight⟩ :=
    kw_trivalent_even_cycle_weight_decomposition G hdeg S hS
      (fun _ => (1 : Complex))
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  refine ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
    hedgeDisjoint, hvertDisjoint, ?_⟩
  let component := kwWeightedCycleComponentSeries base cycle
    (fun i => cycleCoeff (cycle i).edges.toFinset)
  have heq : MvPowerSeries.coeff (ons_finsetExponent S)
      (kwGraphFormalRoot G phase) =
      MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst component (PowerSeries.exp Complex)) := by
    unfold kwGraphFormalRoot
    rw [PowerSeries.coeff_subst (kwGraphFormalLog_hasSubst G phase),
      PowerSeries.coeff_subst
        (kwWeightedCycleComponentSeries_hasSubst base cycle _ hcycle)]
    apply finsum_congr
    intro n
    congr 1
    apply kwMvPowerSeries_coeff_pow_eq_of_antidiag
    intro g hg i hi
    change kwGraphFormalLogCoeff G phase (g i) = _
    exact kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag
      (G := G) (phase := phase) (cycleCoeff := cycleCoeff)
      (hlog := hlog) (hdeg := hdeg) (S := S) (hS := hS)
      (base := base) (cycle := cycle) (hcycle := hcycle)
      (hcover := hcover) (hdisj := hedgeDisjoint)
      (T := Finset.range n) (g := g) hg hi
  rw [heq]
  exact kwWeightedCycleComponentExp_coeff
    S base cycle _ hcycle hcover hedgeDisjoint

theorem surfaceIntersection_add_right {g : Nat}
    (h k l : SurfaceHomology g) :
    surfaceIntersection h (k + l) =
      surfaceIntersection h k + surfaceIntersection h l := by
  unfold surfaceIntersection
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_add]
  abel

theorem surfaceIntersection_finset_sum_right {g : Nat}
    {I : Type*} [DecidableEq I] (h : SurfaceHomology g)
    (S : Finset I) (f : I -> SurfaceHomology g) :
    surfaceIntersection h (∑ i ∈ S, f i) =
      ∑ i ∈ S, surfaceIntersection h (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [surfaceIntersection]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        surfaceIntersection_add_right, ih]

theorem surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero
    {g : Nat} {I : Type*} [DecidableEq I]
    (lambda : SurfaceSpinStructure g) (S : Finset I)
    (f : I -> SurfaceHomology g)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
      surfaceIntersection (f i) (f j) = 0) :
    surfaceQuadraticParity lambda (∑ i ∈ S, f i) =
      ∑ i ∈ S, surfaceQuadraticParity lambda (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [surfaceQuadraticParity]
  | @insert i S hi ih =>
      have hpairS : ∀ j ∈ S, ∀ k ∈ S, j ≠ k ->
          surfaceIntersection (f j) (f k) = 0 := by
        intro j hj k hk hjk
        exact hpair j (by simp [hj]) k (by simp [hk]) hjk
      have hinter : surfaceIntersection (f i) (∑ j ∈ S, f j) = 0 := by
        rw [surfaceIntersection_finset_sum_right]
        apply Finset.sum_eq_zero
        intro j hj
        exact hpair i (by simp) j (by simp [hj]) (by
          intro hij
          subst j
          exact hi hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        surfaceQuadraticParity_add, hinter, add_zero, ih hpairS]

theorem surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero
    {g : Nat} {I : Type*} [DecidableEq I]
    (lambda : SurfaceSpinStructure g) (S : Finset I)
    (f : I -> SurfaceHomology g)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
      surfaceIntersection (f i) (f j) = 0) :
    (surfaceParitySign
      (surfaceQuadraticParity lambda (∑ i ∈ S, f i)) : Complex) =
      ∏ i ∈ S,
        (surfaceParitySign (surfaceQuadraticParity lambda (f i)) : Complex) := by
  rw [surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero
    lambda S f hpair, surfaceParitySign_finset_sum]
  push_cast
  rfl

theorem surfaceSubgraphHomology_biUnion
    {g : Nat} {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (S : Finset (Sym2 V)) (piece : I -> Finset (Sym2 V))
    (hcover : S = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece) :
    surfaceSubgraphHomology edgeClass S =
      ∑ i, surfaceSubgraphHomology edgeClass (piece i) := by
  classical
  unfold surfaceSubgraphHomology
  rw [hcover, Finset.sum_biUnion hdisj]




def SurfaceDisjointCycleIsotropic {g : Nat}
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) : Prop :=
  forall {u v : V} (p : G.Walk u u) (q : G.Walk v v),
    p.IsCycle -> q.IsCycle ->
    Disjoint p.toSubgraph.verts q.toSubgraph.verts ->
    surfaceIntersection
      (surfaceSubgraphHomology edgeClass p.edges.toFinset)
      (surfaceSubgraphHomology edgeClass q.edges.toFinset) = 0

noncomputable def surfaceBaseCycleCoefficient {g : Nat} {V : Type u}
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (S : Finset (Sym2 V)) : Complex :=
  (surfaceParitySign
    (surfaceBaseQuadraticParity (surfaceSubgraphHomology edgeClass S)) : Real)



theorem kwGraphFormalRoot_coeff_surfaceQuadratic
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (kwGraphFormalRoot G phase) =
      (surfaceParitySign
        (surfaceBaseQuadraticParity
          (surfaceSubgraphHomology edgeClass S)) : Complex) := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hcoeff⟩ :=
    kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog
      G phase (surfaceBaseCycleCoefficient edgeClass) hlog hdeg S hS
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  rw [hcoeff]
  let homology : I -> SurfaceHomology g := fun i =>
    surfaceSubgraphHomology edgeClass (cycle i).edges.toFinset
  have hpair : ∀ i ∈ (Finset.univ : Finset I),
      ∀ j ∈ (Finset.univ : Finset I), i ≠ j ->
        surfaceIntersection (homology i) (homology j) = 0 := by
    intro i hi j hj hij
    exact hisotropic (cycle i) (cycle j) (hcycle i) (hcycle j)
      (hvertDisjoint hi hj hij)
  have hsign :=
    surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero
      (0 : SurfaceSpinStructure g) Finset.univ homology hpair
  have hhomology : surfaceSubgraphHomology edgeClass S = ∑ i, homology i := by
    exact surfaceSubgraphHomology_biUnion edgeClass S
      (fun i => (cycle i).edges.toFinset) hcover hedgeDisjoint
  unfold surfaceBaseCycleCoefficient homology at *
  simpa only [surfaceQuadraticParity_zero, hhomology] using hsign.symm



theorem kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex)
    (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
    (S : Finset (Sym2 V)) (hS : S ∉ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
      (kwGraphFormalRoot G phase) = 0 := by
  classical
  unfold kwGraphFormalRoot
  rw [PowerSeries.coeff_subst (kwGraphFormalLog_hasSubst G phase)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro f hf
  by_contra hprod
  apply hS
  let support : Nat -> Finset (Sym2 V) := fun i => (f i).support
  have hpiece : ∀ i ∈ Finset.range n,
      support i ∈ evenSubgraphs G := by
    intro i hi
    have hcoeffNe : MvPowerSeries.coeff (f i)
        (kwGraphFormalLog G phase) ≠ 0 := by
      intro hzero
      apply hprod
      exact Finset.prod_eq_zero hi hzero
    have hcomponent :=
      ons_finsuppAntidiag_finsetExponent_component
        (Finset.range n) S f hf hi
    change kwGraphFormalLogCoeff G phase (f i) ≠ 0 at hcoeffNe
    rw [hcomponent] at hcoeffNe
    obtain ⟨root, q, hq, hqedges⟩ := hlog.2 (support i) hcoeffNe
    rw [← hqedges]
    exact ons_cycle_edges_evenSubgraph G q hq
  have hpair : ((Finset.range n : Finset Nat) : Set Nat).PairwiseDisjoint
      support := by
    intro i hi j hj hij
    exact ons_finsuppAntidiag_finsetExponent_support_disjoint
      (Finset.range n) S f hf hi hj hij
  have hunion := ons_evenSubgraphs_biUnion_of_pairwiseDisjoint
    G (Finset.range n) support hpair hpiece
  rw [← ons_finsuppAntidiag_finsetExponent_support_cover
    (Finset.range n) S f hf] at hunion
  exact hunion


noncomputable def surfaceBaseFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) :
    MvPowerSeries (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPowerSeries.monomial (ons_finsetExponent F)
      (surfaceBaseCycleCoefficient edgeClass F)


noncomputable def surfaceBaseEvenMvPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) :
    MvPolynomial (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPolynomial.monomial (ons_finsetExponent F)
      (surfaceBaseCycleCoefficient edgeClass F)

theorem surfaceBaseFormalEvenPolynomial_eq_coe
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) :
    surfaceBaseFormalEvenPolynomial G edgeClass =
      (surfaceBaseEvenMvPolynomial G edgeClass :
        MvPowerSeries (Sym2 V) Complex) := by
  classical
  unfold surfaceBaseFormalEvenPolynomial surfaceBaseEvenMvPolynomial
  ext m
  rw [map_sum, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
  simp [eq_comm]

theorem surfaceBaseFormalEvenPolynomial_coeff_finsetExponent
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (S : Finset (Sym2 V)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (surfaceBaseFormalEvenPolynomial G edgeClass) =
      if S ∈ evenSubgraphs G then
        surfaceBaseCycleCoefficient edgeClass S else 0 := by
  classical
  unfold surfaceBaseFormalEvenPolynomial
  rw [map_sum]
  by_cases hS : S ∈ evenSubgraphs G
  · rw [Finset.sum_eq_single S]
    · simp [hS]
    · intro T hT hTS
      rw [MvPowerSeries.coeff_monomial, if_neg]
      intro heq
      exact hTS (ons_finsetExponent_injective heq.symm)
    · exact fun hnot => (hnot hS).elim
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro T hT
    rw [MvPowerSeries.coeff_monomial, if_neg]
    intro heq
    apply hS
    rw [ons_finsetExponent_injective heq]
    exact hT

theorem surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (m : Sym2 V →₀ Nat) (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
        (surfaceBaseFormalEvenPolynomial G edgeClass) = 0 := by
  classical
  unfold surfaceBaseFormalEvenPolynomial
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [MvPowerSeries.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [heq, ons_finsetExponent_apply]
  split <;> omega



theorem kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
    kwGraphFormalRoot G phase =
      surfaceBaseFormalEvenPolynomial G edgeClass := by
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    by_cases heven : m.support ∈ evenSubgraphs G
    · rw [kwGraphFormalRoot_coeff_surfaceQuadratic
        G phase edgeClass hlog hisotropic hdeg m.support heven,
        surfaceBaseFormalEvenPolynomial_coeff_finsetExponent,
        if_pos heven]
      rfl
    · rw [kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted
        G phase _ hlog m.support heven,
        surfaceBaseFormalEvenPolynomial_coeff_finsetExponent,
        if_neg heven]
  · rw [hnonsquare m hm,
      surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
        G edgeClass m hm]

theorem surfaceBaseEvenMvPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) :
    MvPolynomial.eval weight (surfaceBaseEvenMvPolynomial G edgeClass) =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight := by
  classical
  unfold surfaceBaseEvenMvPolynomial surfaceQuadraticEvenPolynomial
    surfaceBaseCycleCoefficient evenSubgraphs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod,
    surfaceQuadraticParity_zero]

theorem surfaceBaseFormalEvenPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) :
    ons_mvSeriesEval (surfaceBaseFormalEvenPolynomial G edgeClass) weight =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight := by
  rw [surfaceBaseFormalEvenPolynomial_eq_coe, ons_mvSeriesEval_coe,
    surfaceBaseEvenMvPolynomial_eval]



noncomputable def surfaceBaseScalePolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) : Polynomial Complex :=
  ∑ F ∈ evenSubgraphs G,
    Polynomial.monomial F.card
      (surfaceBaseCycleCoefficient edgeClass F * ∏ edge ∈ F, weight edge)

theorem surfaceBaseScalePolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) (t : Complex) :
    (surfaceBaseScalePolynomial G edgeClass weight).eval t =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) (fun edge => t * weight edge) := by
  classical
  unfold surfaceBaseScalePolynomial surfaceQuadraticEvenPolynomial
    surfaceBaseCycleCoefficient evenSubgraphs
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, surfaceQuadraticParity_zero]
  simp
  ring





theorem surface_kacWard_base_det_square_of_cycle_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight ^ 2 := by
  let originalDartDecEq : DecidableEq G.Dart := inferInstance
  let standardDartDecEq : DecidableEq G.Dart :=
    fun a b => SimpleGraph.instDecidableEqDart a b
  letI : DecidableEq G.Dart := standardDartDecEq
  let M := kwGraphTransition G weight phase
  let P := kwDetScalePolynomial M
  let Q := (surfaceBaseScalePolynomial G edgeClass weight) ^ 2
  let card : Real := Fintype.card G.Dart
  let q : Real := (2 * (1 + card))⁻¹
  let B : Real := ∑ dart : G.Dart, ∑ next : G.Dart, norm (M dart next)
  let delta : Real := q / (1 + B)
  have hcard0 : 0 <= card := by positivity
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hcardq : card * q < 1 := by
    dsimp only [q]
    rw [mul_inv_lt_iff₀ (by positivity : 0 < 2 * (1 + card))]
    nlinarith
  have hraw (dart next : G.Dart) : norm (M dart next) <= B := by
    dsimp only [B]
    exact (Finset.single_le_sum
      (fun d _ => Finset.sum_nonneg fun e _ => norm_nonneg (M d e))
      (Finset.mem_univ dart)).trans' <|
        Finset.single_le_sum
          (fun e _ => norm_nonneg (M dart e)) (Finset.mem_univ next)
  have hformal := kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial
    G phase edgeClass hlog hisotropic hdeg hnonsquare
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    have hrnorm : norm (r : Complex) = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    let scaled : Sym2 V -> Complex := fun edge => (r : Complex) * weight edge
    have hentry : ∀ dart next,
        norm (kwGraphTransition G scaled phase dart next) <= q := by
      intro dart next
      rw [show scaled = fun edge => (r : Complex) * weight edge from rfl,
        kwGraphTransition_smulWeight, norm_mul, hrnorm]
      have hlt : r * B < q := by
        have hden : 0 < 1 + B := by positivity
        have h := hr.2
        dsimp only [delta] at h
        rw [lt_div_iff₀ hden] at h
        nlinarith
      exact (mul_le_mul_of_nonneg_left
        (hraw dart next) hr.1.le).trans hlt.le
    have hspec : ∀ alpha ∈
        (kwGraphTransition G scaled phase).charpoly.roots,
        norm alpha < 1 :=
      ons_spectral_lt_one_of_entry
        (kwGraphTransition G scaled phase) q hq.le hentry hcardq
    have hroot :
        ons_detWalkRoot (kwGraphTransition G scaled phase) =
          surfaceQuadraticEvenPolynomial G edgeClass
            (0 : SurfaceSpinStructure g) scaled := by
      rw [← kw_mvSeriesEval_GraphFormalRoot
          G phase scaled q hq.le hentry hcardq,
        hformal, surfaceBaseFormalEvenPolynomial_eval]
    have hsmall :
        (1 - kwGraphTransition G scaled phase).det =
          surfaceQuadraticEvenPolynomial G edgeClass
            (0 : SurfaceSpinStructure g) scaled ^ 2 := by
      calc
        (1 - kwGraphTransition G scaled phase).det =
            ons_detWalkRoot (kwGraphTransition G scaled phase) ^ 2 :=
          (ons_detWalkRoot_sq
            (kwGraphTransition G scaled phase) hspec).symm
        _ = _ := by rw [hroot]
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
      surfaceBaseScalePolynomial_eval]
    have hmatrix : (r : Complex) • M =
        kwGraphTransition G scaled phase := by
      ext dart next
      change (r : Complex) * M dart next = _
      dsimp only [M, scaled]
      rw [kwGraphTransition_smulWeight]
    rw [hmatrix]
    exact hsmall
  have hinfinite : Set.Infinite {z : Complex | P.eval z = Q.eval z} := by
    have hI : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real => (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hI.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  have hone' : kwDetOneSubWith standardDartDecEq M =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight ^ 2 := by
    simpa [kwDetOneSubWith, kwDetScalePolynomial_eval,
      surfaceBaseScalePolynomial_eval, M] using hone
  change kwDetOneSubWith originalDartDecEq M =
    surfaceQuadraticEvenPolynomial G edgeClass
      (0 : SurfaceSpinStructure g) weight ^ 2
  exact (kwDetOneSubWith_eq originalDartDecEq standardDartDecEq M).trans hone'


theorem surface_twisted_kacWard_det_square_of_cycle_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V -> Complex) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda weight).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  apply surface_twisted_kacWard_det_square_of_base G phase edgeClass
  intro w
  exact surface_kacWard_base_det_square_of_cycle_phase
    G phase edgeClass hlog hisotropic hdeg hnonsquare w




theorem surface_twisted_kacWard_det_eq_sectorSquare_of_cycle_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V -> Real) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda
        (fun edge => (weight edge : Complex))).det =
      (surfaceTwistedSectorSquare
        (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
  apply surface_twisted_kacWard_det_eq_sectorSquare_of_base G phase edgeClass
  intro w
  exact surface_kacWard_base_det_square_of_cycle_phase
    G phase edgeClass hlog hisotropic hdeg hnonsquare w

end StatMech.FrontierA
