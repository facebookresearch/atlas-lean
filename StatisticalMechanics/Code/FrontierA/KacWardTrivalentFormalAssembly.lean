/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardFormalMultiaffine
import Code.FrontierA.KacWardTrivalentCoefficients
import Code.Onsager.DecorationFormalCoefficient













open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

universe u



noncomputable def kwGraphFormalEvenPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    MvPowerSeries (Sym2 V) ℂ :=
  ∑ F ∈ evenSubgraphs G,
    MvPowerSeries.monomial (ons_finsetExponent F) 1


noncomputable def kwGraphEvenMvPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    MvPolynomial (Sym2 V) ℂ :=
  ∑ F ∈ evenSubgraphs G,
    MvPolynomial.monomial (ons_finsetExponent F) 1

theorem kwGraphFormalEvenPolynomial_eq_coe
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    kwGraphFormalEvenPolynomial G =
      (kwGraphEvenMvPolynomial G : MvPowerSeries (Sym2 V) ℂ) := by
  classical
  unfold kwGraphFormalEvenPolynomial kwGraphEvenMvPolynomial
  ext m
  rw [map_sum, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
  simp [eq_comm]

theorem kwGraphFormalEvenPolynomial_eval
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) :
    ons_mvSeriesEval (kwGraphFormalEvenPolynomial G) weight =
      kwEvenPolynomial G weight := by
  classical
  rw [kwGraphFormalEvenPolynomial_eq_coe,
    ons_mvSeriesEval_coe]
  unfold kwGraphEvenMvPolynomial kwEvenPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod]
  simp




def KWGraphUnitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : Prop :=
  (∀ {root : V} (p : G.Walk root root), p.IsCycle →
      kwGraphFormalLogCoeff G phase
        (ons_finsetExponent p.edges.toFinset) = 1) ∧
  (∀ (S : Finset (Sym2 V)),
      kwGraphFormalLogCoeff G phase (ons_finsetExponent S) ≠ 0 →
        ∃ (root : V) (p : G.Walk root root),
          p.IsCycle ∧ p.edges.toFinset = S)



noncomputable def kwCycleComponentSeries
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i)) :
    MvPowerSeries (Sym2 V) ℂ :=
  ∑ i : I, MvPowerSeries.monomial
    (ons_finsetExponent (cycle i).edges.toFinset) 1

theorem kwCycleComponentSeries_coeff
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i))
    (m : Sym2 V →₀ ℕ) :
    MvPowerSeries.coeff m (kwCycleComponentSeries base cycle) =
      ∑ i : I,
        if ons_finsetExponent (cycle i).edges.toFinset = m then 1 else 0 := by
  classical
  unfold kwCycleComponentSeries
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPowerSeries.coeff_monomial]
  by_cases heq : ons_finsetExponent (cycle i).edges.toFinset = m
  · rw [if_pos heq.symm, if_pos heq]
  · rw [if_neg (Ne.symm heq), if_neg heq]

theorem kwCycleComponentSeries_coeff_piece
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i))
    (hcycle : ∀ i, (cycle i).IsCycle)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (cycle i).edges.toFinset)) (j : I) :
    MvPowerSeries.coeff
        (ons_finsetExponent (cycle j).edges.toFinset)
        (kwCycleComponentSeries base cycle) = 1 := by
  classical
  rw [kwCycleComponentSeries_coeff]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro i hij
    rw [if_neg]
    intro heq
    apply hij
    apply ons_cycle_decomposition_edgeSet_injective base cycle hcycle hdisj
    exact ons_finsetExponent_injective heq

theorem kwCycleComponentSeries_hasSubst
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i))
    (hcycle : ∀ i, (cycle i).IsCycle) :
    PowerSeries.HasSubst (kwCycleComponentSeries base cycle) := by
  classical
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
    kwCycleComponentSeries_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  intro heq
  apply (ons_cycle_edges_toFinset_nonempty (cycle i) (hcycle i)).ne_empty
  apply ons_finsetExponent_injective
  simpa [ons_finsetExponent] using heq



theorem kwGraphFormalLog_coeff_eq_cycleComponent_of_antidiag
    {V I : Type u} {K : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hunit : KWGraphUnitCycleLog G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G)
    (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i))
    (hcycle : ∀ i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (cycle i).edges.toFinset))
    (T : Finset K) (g : K →₀ Sym2 V →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : K} (hi : i ∈ T) :
    kwGraphFormalLogCoeff G phase (g i) =
      MvPowerSeries.coeff (g i)
        (kwCycleComponentSeries base cycle) := by
  classical
  have hcomponent :=
    ons_finsuppAntidiag_finsetExponent_component T S g hg hi
  by_cases hexists : ∃ j : I,
      (g i).support = (cycle j).edges.toFinset
  · obtain ⟨j, hj⟩ := hexists
    have hgi : g i =
        ons_finsetExponent (cycle j).edges.toFinset := by
      calc
        g i = ons_finsetExponent (g i).support := hcomponent
        _ = ons_finsetExponent (cycle j).edges.toFinset := congrArg _ hj
    rw [hgi, hunit.1 (cycle j) (hcycle j)]
    exact (kwCycleComponentSeries_coeff_piece
      base cycle hcycle hdisj j).symm
  · have hleft : kwGraphFormalLogCoeff G phase (g i) = 0 := by
      by_contra hne
      have hcoeffEq : kwGraphFormalLogCoeff G phase
          (ons_finsetExponent (g i).support) ≠ 0 := by
        rw [← hcomponent]
        exact hne
      obtain ⟨root, q, hq, hqedges⟩ := hunit.2 (g i).support hcoeffEq
      have hqsub : q.edges.toFinset ⊆ S := by
        rw [hqedges]
        exact ons_finsuppAntidiag_finsetExponent_support_subset
          T S g hg hi
      obtain ⟨j, hjedges⟩ := ons_cycle_edges_eq_decomposition_piece
        G hdeg S hS base cycle hcycle hcover q hq hqsub
      exact hexists ⟨j, hqedges.symm.trans hjedges⟩
    have hright : MvPowerSeries.coeff (g i)
        (kwCycleComponentSeries base cycle) = 0 := by
      rw [kwCycleComponentSeries_coeff]
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



theorem kwMvPowerSeries_coeff_pow_eq_of_antidiag
    {E : Type*} [DecidableEq E]
    (left right : MvPowerSeries E ℂ) (m : E →₀ ℕ) (n : ℕ)
    (hcoeff : ∀ (g : ℕ →₀ E →₀ ℕ),
      g ∈ (Finset.range n).finsuppAntidiag m →
      ∀ i ∈ Finset.range n,
        MvPowerSeries.coeff (g i) left =
          MvPowerSeries.coeff (g i) right) :
    MvPowerSeries.coeff m (left ^ n) =
      MvPowerSeries.coeff m (right ^ n) := by
  classical
  rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoeff g hg i hi



theorem kwCycleComponentSeries_pow_coeff
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (S : Finset (Sym2 V)) (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i))
    (hcycle : ∀ i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (cycle i).edges.toFinset)) (n : ℕ) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        ((kwCycleComponentSeries base cycle) ^ n) =
      if n = Fintype.card I then (n.factorial : ℂ) else 0 := by
  classical
  let exponent : I → Sym2 V →₀ ℕ :=
    fun i ↦ ons_finsetExponent (cycle i).edges.toFinset
  have hnonempty : ∀ i, ((cycle i).edges.toFinset).Nonempty :=
    fun i ↦ ons_cycle_edges_toFinset_nonempty (cycle i) (hcycle i)
  have hexponent (f : Fin n → I) :
      (∑ k, exponent (f k)) = ons_finsetExponent S ↔
        Function.Bijective f := by
    exact ons_sum_finsetExponent_eq_iff_bijective S
      (fun i ↦ (cycle i).edges.toFinset) hcover hdisj hnonempty n f
  have hprod (f : Fin n → I) :
      (∏ k, MvPowerSeries.monomial (exponent (f k)) (1 : ℂ)) =
        MvPowerSeries.monomial (∑ k, exponent (f k)) 1 := by
    simpa using MvPowerSeries.prod_monomial
      (fun k ↦ exponent (f k)) (fun _ ↦ (1 : ℂ)) Finset.univ
  have hsumForm :
      MvPowerSeries.coeff (ons_finsetExponent S)
          ((kwCycleComponentSeries base cycle) ^ n) =
        ∑ f : Fin n → I, if Function.Bijective f then 1 else 0 := by
    unfold kwCycleComponentSeries
    change MvPowerSeries.coeff (ons_finsetExponent S)
      ((∑ i, MvPowerSeries.monomial (exponent i) 1) ^ n) = _
    rw [Fintype.sum_pow, map_sum]
    apply Finset.sum_congr rfl
    intro f hf
    rw [hprod, MvPowerSeries.coeff_monomial]
    rw [if_congr (by simpa only [eq_comm] using hexponent f) rfl rfl]
  rw [hsumForm]
  by_cases hn : n = Fintype.card I
  · rw [if_pos hn, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hcardEq : Fintype.card (Fin n) = Fintype.card I := by
      simpa using hn
    let e : Fin n ≃ I := Fintype.equivOfCardEq hcardEq
    have hcardBij :
        Fintype.card {f : Fin n → I // Function.Bijective f} =
          n.factorial := by
      calc
        Fintype.card {f : Fin n → I // Function.Bijective f} =
            Fintype.card (Fin n ≃ I) :=
          Fintype.card_congr Equiv.bijectiveEquiv
        _ = (Fintype.card (Fin n)).factorial := Fintype.card_equiv e
        _ = n.factorial := by simp
    have hcardFilter :
        #{f : Fin n → I | Function.Bijective f} = n.factorial := by
      rw [← Fintype.card_subtype]
      exact hcardBij
    rw [Finset.sum_const, nsmul_eq_mul, hcardFilter]
    simp
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro f hf
    rw [if_neg]
    intro hbij
    apply hn
    have hcard := Fintype.card_congr (Equiv.ofBijective f hbij)
    simpa using hcard

theorem kwCycleComponentExp_coeff
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (S : Finset (Sym2 V)) (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i))
    (hcycle : ∀ i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (cycle i).edges.toFinset)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst (kwCycleComponentSeries base cycle)
          (PowerSeries.exp ℂ)) = 1 := by
  classical
  rw [PowerSeries.coeff_subst
    (kwCycleComponentSeries_hasSubst base cycle hcycle)]
  rw [finsum_eq_single _ (Fintype.card I)]
  · rw [kwCycleComponentSeries_pow_coeff
      S base cycle hcycle hcover hdisj, if_pos rfl]
    simp only [PowerSeries.coeff_exp, smul_eq_mul]
    rw [one_div, map_inv₀, map_natCast]
    have hfac : ((Fintype.card I).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (Fintype.card I)
    field_simp
  · intro n hn
    rw [kwCycleComponentSeries_pow_coeff
      S base cycle hcycle hcover hdisj, if_neg hn, smul_zero]



theorem kwGraphFormalRoot_coeff_evenSubgraph_of_unitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hunit : KWGraphUnitCycleLog G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
      (kwGraphFormalRoot G phase) = 1 := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hweight⟩ :=
    kw_trivalent_even_cycle_weight_decomposition G hdeg S hS
      (fun _ ↦ (1 : ℂ))
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  have heq : MvPowerSeries.coeff (ons_finsetExponent S)
      (kwGraphFormalRoot G phase) =
      MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst (kwCycleComponentSeries base cycle)
          (PowerSeries.exp ℂ)) := by
    unfold kwGraphFormalRoot
    rw [PowerSeries.coeff_subst (kwGraphFormalLog_hasSubst G phase),
      PowerSeries.coeff_subst
        (kwCycleComponentSeries_hasSubst base cycle hcycle)]
    apply finsum_congr
    intro n
    congr 1
    apply kwMvPowerSeries_coeff_pow_eq_of_antidiag
    intro g hg i hi
    change kwGraphFormalLogCoeff G phase (g i) = _
    exact kwGraphFormalLog_coeff_eq_cycleComponent_of_antidiag
      (G := G) (phase := phase) (hunit := hunit) (hdeg := hdeg)
      (S := S) (hS := hS) (base := base) (cycle := cycle)
      (hcycle := hcycle) (hcover := hcover) (hdisj := hedgeDisjoint)
      (T := Finset.range n) (g := g) hg hi
  rw [heq]
  exact kwCycleComponentExp_coeff S base cycle hcycle hcover hedgeDisjoint


theorem kwGraphLoopExponent_apply_eq_zero_of_not_mem_edgeFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (edge : Sym2 V) (hedge : edge ∉ G.edgeFinset) :
    kwGraphLoopExponent G loop edge = 0 := by
  classical
  unfold kwGraphLoopExponent
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finsupp.single_apply]
  split
  · rename_i heq
    exfalso
    apply hedge
    rw [← heq, SimpleGraph.mem_edgeFinset]
    exact (loop k).edge_mem
  · rfl

theorem kwGraphFormalLogCoeff_eq_zero_of_offGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (m : Sym2 V →₀ ℕ) (edge : Sym2 V)
    (hedge : edge ∉ G.edgeFinset) (hmedge : m edge ≠ 0) :
    kwGraphFormalLogCoeff G phase m = 0 := by
  classical
  unfold kwGraphFormalLogCoeff
  have houter :
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        (∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop else 0) / ((r : ℂ) + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hinner :
        (∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro loop hloop
      rw [if_neg]
      intro hexponent
      apply hmedge
      rw [← hexponent]
      exact kwGraphLoopExponent_apply_eq_zero_of_not_mem_edgeFinset
        G loop edge hedge
    rw [hinner, zero_div]
  rw [houter]
  ring

theorem kwGraphFormalRoot_coeff_eq_zero_of_offGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (m : Sym2 V →₀ ℕ) (edge : Sym2 V)
    (hedge : edge ∉ G.edgeFinset) (hmedge : m edge ≠ 0) :
    MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0 := by
  classical
  unfold kwGraphFormalRoot
  rw [PowerSeries.coeff_subst (kwGraphFormalLog_hasSubst G phase)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro g hg
  have hsum := congrArg (fun x : Sym2 V →₀ ℕ ↦ x edge)
    (Finset.mem_finsuppAntidiag.mp hg).1
  simp only [Finsupp.finsetSum_apply] at hsum
  have hexists : ∃ i ∈ Finset.range n, g i edge ≠ 0 := by
    by_contra hnone
    have hall : ∀ i ∈ Finset.range n, g i edge = 0 := by
      intro i hi
      exact not_ne_iff.mp (fun hne ↦ hnone ⟨i, hi, hne⟩)
    have hzero : ∑ i ∈ Finset.range n, g i edge = 0 :=
      Finset.sum_eq_zero hall
    rw [hzero] at hsum
    exact hmedge hsum.symm
  obtain ⟨i, hi, hgi⟩ := hexists
  apply Finset.prod_eq_zero hi
  change kwGraphFormalLogCoeff G phase (g i) = 0
  exact kwGraphFormalLogCoeff_eq_zero_of_offGraph
    G phase (g i) edge hedge hgi



theorem kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hunit : KWGraphUnitCycleLog G phase)
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
  intro g hg
  by_contra hprod
  apply hS
  let support : ℕ → Finset (Sym2 V) := fun i ↦ (g i).support
  have hpiece : ∀ i ∈ Finset.range n,
      support i ∈ evenSubgraphs G := by
    intro i hi
    have hcoeffNe : MvPowerSeries.coeff (g i)
        (kwGraphFormalLog G phase) ≠ 0 := by
      intro hzero
      apply hprod
      exact Finset.prod_eq_zero hi hzero
    have hcomponent :=
      ons_finsuppAntidiag_finsetExponent_component
        (Finset.range n) S g hg hi
    change kwGraphFormalLogCoeff G phase (g i) ≠ 0 at hcoeffNe
    rw [hcomponent] at hcoeffNe
    obtain ⟨root, q, hq, hqedges⟩ := hunit.2 (support i) hcoeffNe
    rw [← hqedges]
    exact ons_cycle_edges_evenSubgraph G q hq
  have hpair : ((Finset.range n : Finset ℕ) : Set ℕ).PairwiseDisjoint
      support := by
    intro i hi j hj hij
    exact ons_finsuppAntidiag_finsetExponent_support_disjoint
      (Finset.range n) S g hg hi hj hij
  have hunion := ons_evenSubgraphs_biUnion_of_pairwiseDisjoint
    G (Finset.range n) support hpair hpiece
  rw [← ons_finsuppAntidiag_finsetExponent_support_cover
    (Finset.range n) S g hg] at hunion
  exact hunion

theorem kwGraphFormalEvenPolynomial_coeff_finsetExponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (kwGraphFormalEvenPolynomial G) =
      if S ∈ evenSubgraphs G then 1 else 0 := by
  classical
  unfold kwGraphFormalEvenPolynomial
  rw [map_sum]
  by_cases hS : S ∈ evenSubgraphs G
  · rw [Finset.sum_eq_single S]
    · simp [hS]
    · intro T hT hTS
      rw [MvPowerSeries.coeff_monomial, if_neg]
      intro heq
      exact hTS (ons_finsetExponent_injective heq.symm)
    · exact fun hnot ↦ (hnot hS).elim
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro T hT
    rw [MvPowerSeries.coeff_monomial, if_neg]
    intro heq
    apply hS
    rw [ons_finsetExponent_injective heq]
    exact hT

theorem kwGraphFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Sym2 V →₀ ℕ) (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m (kwGraphFormalEvenPolynomial G) = 0 := by
  classical
  unfold kwGraphFormalEvenPolynomial
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [MvPowerSeries.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [heq, ons_finsetExponent_apply]
  split <;> omega



theorem kwGraphFormalRoot_eq_evenPolynomial_of_unitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hunit : KWGraphUnitCycleLog G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hnonsquare : ∀ m : Sym2 V →₀ ℕ,
      ¬ ons_IsSquarefreeExponent m →
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
    kwGraphFormalRoot G phase = kwGraphFormalEvenPolynomial G := by
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    by_cases heven : m.support ∈ evenSubgraphs G
    · rw [kwGraphFormalRoot_coeff_evenSubgraph_of_unitCycleLog
        G phase hunit hdeg m.support heven,
        kwGraphFormalEvenPolynomial_coeff_finsetExponent, if_pos heven]
    · rw [kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even
        G phase hunit m.support heven,
        kwGraphFormalEvenPolynomial_coeff_finsetExponent, if_neg heven]
  · rw [hnonsquare m hm,
      kwGraphFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree G m hm]




theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_unitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hunit : KWGraphUnitCycleLog G embedding.turnPhase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G := by
  apply kwGraphFormalRoot_eq_evenPolynomial_of_unitCycleLog
    G embedding.turnPhase hunit hdeg
  intro m hm
  simp only [ons_IsSquarefreeExponent] at hm
  push Not at hm
  obtain ⟨edge, hedge⟩ := hm
  have hrepeated : 2 ≤ m edge := by omega
  by_cases hedgeG : edge ∈ G.edgeFinset
  · exact kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated_edge
      G embedding edge hedgeG m hrepeated
  · exact kwGraphFormalRoot_coeff_eq_zero_of_offGraph
      G embedding.turnPhase m edge hedgeG (by omega)

theorem kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_unitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hunit : KWGraphUnitCycleLog G embedding.turnPhase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (weight : Sym2 V → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_detWalkRoot
        (kwGraphTransition G weight embedding.turnPhase) =
      kwEvenPolynomial G weight := by
  rw [← kw_mvSeriesEval_GraphFormalRoot
      G embedding.turnPhase weight q hq hentry hcard,
    kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_unitCycleLog
      G embedding hunit hdeg,
    kwGraphFormalEvenPolynomial_eval]



theorem kacWard_straightLine_trivalent_of_unitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hunit : KWGraphUnitCycleLog G embedding.turnPhase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (weight : Sym2 V → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  let M := kwGraphTransition G weight embedding.turnPhase
  have hspec : ∀ alpha ∈ M.charpoly.roots, ‖alpha‖ < 1 :=
    ons_spectral_lt_one_of_entry M q hq hentry hcard
  calc
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
        ons_detWalkRoot M ^ 2 := (ons_detWalkRoot_sq M hspec).symm
    _ = (kwEvenPolynomial G weight) ^ 2 := by
      rw [kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_unitCycleLog
        G embedding hunit hdeg weight q hq hentry hcard]

end StatMech.FrontierA
