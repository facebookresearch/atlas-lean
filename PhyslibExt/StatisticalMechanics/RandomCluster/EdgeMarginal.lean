/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.DensityBounds
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC

/-!
# Edge marginals, monotone couplings, and boundary-condition comparisons

If `μ ≤ ν` are coupled monotonically, then `ν(A) - μ(A) ≤ ∑_e (ν(e open) - μ(e open))` for
increasing events `A`; in particular equal edge marginals force equal laws on increasing events.

## i. Overview

For a monotone coupling `P` of `μ` and `ν` (`P` supported on pairs `ω ≤ ω'`), the indicator of an
increasing event changes by at most the number of edges that change. Integrating against `P` gives
the edge-marginal bound. The second half compares random-cluster measures with different boundary
graphs `C ≤ C'`: the weights differ by a factor of at most `q^N` when the cluster counts differ by
at most `N`, which bounds `φ^C(A) ≤ q^N φ^{C'}(A)`.

## ii. Key results

- `eventMass_diff_le_edgeMarg_sum` : the edge-marginal bound for monotone couplings.
- `eventMass_eq_of_edgeMarg_eq` : equal edge marginals give equal laws on increasing events.
- `bcEventMass_le_qpow` : boundary-condition comparison with a `q^N` factor.
- `numClustersBC_bot_le` : removing a boundary graph `C'` raises the cluster count by at most
  `|E(C')|`.

## iii. Table of contents

- A. Monotone couplings and edge marginals
- B. Boundary-condition comparisons

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §4.3 (uniqueness via edge densities).
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Monotone couplings and edge marginals -/

/-- The probability `μ(ω(e) = 1)` that the coordinate `e` is open under the mass function `μ`. -/
noncomputable def edgeMargProb (μ : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∑ ω : ConfigSpace E, (if ω e then (1 : ℝ) else 0) * μ ω

/-- The mass `μ(A)` of an event under the mass function `μ`. -/
noncomputable def eventMassProb (μ : ConfigSpace E → ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω * μ ω

/-- `P` is a monotone coupling of the mass functions `μ` and `ν`: a nonnegative mass function on
pairs
with marginals `μ` and `ν`, supported on pairs `(ω, ω')` with `ω ≤ ω'`.
-/
structure IsMonotoneCouplingFun (P : ConfigSpace E × ConfigSpace E → ℝ)
    (μ ν : ConfigSpace E → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ P z
  supportLE : ∀ z, ¬ z.1 ≤ z.2 → P z = 0
  fst_marginal : ∀ ω, ∑ ω' : ConfigSpace E, P (ω, ω') = μ ω
  snd_marginal : ∀ ω', ∑ ω : ConfigSpace E, P (ω, ω') = ν ω'

private lemma bool_eq_of_le_ne {b c : Bool} (hle : b ≤ c) (hne : b ≠ c) :
    b = false ∧ c = true := by
  revert hle hne; cases b <;> cases c <;> decide

private lemma boolR_mono {b c : Bool} (h : b ≤ c) :
    (if b then (1 : ℝ) else 0) ≤ (if c then (1 : ℝ) else 0) := by
  cases b <;> cases c <;> simp_all (config := { decide := true })

private lemma boolR_diff_nonneg {b c : Bool} (h : b ≤ c) :
    (0 : ℝ) ≤ (if c then (1 : ℝ) else 0) - (if b then (1 : ℝ) else 0) := by
  have := boolR_mono h; linarith

omit [DecidableEq E] in
lemma indicator_diff_le_edgeSum {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {ω ω' : ConfigSpace E} (h : ω ≤ ω') :
    A.indicator (fun _ => (1 : ℝ)) ω' - A.indicator (fun _ => (1 : ℝ)) ω
      ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) := by
  have hsumnn : (0 : ℝ)
      ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) :=
    Finset.sum_nonneg (fun e _ => boolR_diff_nonneg (h e))
  by_cases hmem : ω ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hA h hmem)]; simpa using hsumnn
  · rw [Set.indicator_of_notMem hmem, sub_zero]
    by_cases hmem' : ω' ∈ A
    · rw [Set.indicator_of_mem hmem']
      have hne : ω ≠ ω' := fun heq => hmem (heq ▸ hmem')
      obtain ⟨e, he⟩ : ∃ e, ω e ≠ ω' e := by
        by_contra hcon
        exact hne (funext fun e => not_not.mp (fun h => hcon ⟨e, h⟩))
      have hbc : ω e = false ∧ ω' e = true := bool_eq_of_le_ne (h e) he
      calc (1 : ℝ)
          = (if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0) := by
            rw [hbc.1, hbc.2]; norm_num
        _ ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) :=
            Finset.single_le_sum
              (f := fun e => (if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0))
              (fun i _ => boolR_diff_nonneg (h i)) (Finset.mem_univ e)
    · rw [Set.indicator_of_notMem hmem']; exact hsumnn

lemma eventMass_eq_coupling_snd {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (A : Set (ConfigSpace E)) :
    eventMassProb ν A
      = ∑ z : ConfigSpace E × ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) z.2 * P z := by
  unfold eventMassProb
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω' _ => by rw [← hP.snd_marginal ω', Finset.mul_sum]

lemma eventMass_eq_coupling_fst {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (A : Set (ConfigSpace E)) :
    eventMassProb μ A
      = ∑ z : ConfigSpace E × ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) z.1 * P z := by
  unfold eventMassProb
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ω _ => by rw [← hP.fst_marginal ω, Finset.mul_sum]

lemma edgeMarg_eq_coupling_snd {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν) (e : E) :
    edgeMargProb ν e
      = ∑ z : ConfigSpace E × ConfigSpace E, (if z.2 e then (1 : ℝ) else 0) * P z := by
  unfold edgeMargProb
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω' _ => by rw [← hP.snd_marginal ω', Finset.mul_sum]

lemma edgeMarg_eq_coupling_fst {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν) (e : E) :
    edgeMargProb μ e
      = ∑ z : ConfigSpace E × ConfigSpace E, (if z.1 e then (1 : ℝ) else 0) * P z := by
  unfold edgeMargProb
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ω _ => by rw [← hP.fst_marginal ω, Finset.mul_sum]

lemma eventMass_diff_le_edgeMarg_sum {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb ν A - eventMassProb μ A
      ≤ ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) := by
  rw [eventMass_eq_coupling_snd hP, eventMass_eq_coupling_fst hP, ← Finset.sum_sub_distrib]
  have hRHS : ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e)
      = ∑ z : ConfigSpace E × ConfigSpace E,
          (∑ e : E, ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0))) * P z := by
    rw [Finset.sum_congr rfl (fun e _ => by
        rw [edgeMarg_eq_coupling_snd hP e, edgeMarg_eq_coupling_fst hP e,
          ← Finset.sum_sub_distrib])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hRHS]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : z.1 ≤ z.2
  · have hcore := indicator_diff_le_edgeSum hA hz
    have hPnn := hP.nonneg z
    calc A.indicator (fun _ => (1 : ℝ)) z.2 * P z - A.indicator (fun _ => (1 : ℝ)) z.1 * P z
        = (A.indicator (fun _ => (1 : ℝ)) z.2 - A.indicator (fun _ => (1 : ℝ)) z.1) * P z := by
          ring
      _ ≤ (∑ e : E, ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0))) * P z :=
          mul_le_mul_of_nonneg_right hcore hPnn
  · rw [hP.supportLE z hz]; simp

lemma coupling_eventMass_le {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb μ A ≤ eventMassProb ν A := by
  rw [eventMass_eq_coupling_snd hP, eventMass_eq_coupling_fst hP]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : z.1 ≤ z.2
  · exact mul_le_mul_of_nonneg_right (hA.indicator_monotone hz) (hP.nonneg z)
  · rw [hP.supportLE z hz]; simp

/-- Two monotonically coupled measures with the same edge marginals give the same mass to every
increasing event.
-/
lemma eventMass_eq_of_edgeMarg_eq {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (hmarg : ∀ e : E, edgeMargProb μ e = edgeMargProb ν e)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb μ A = eventMassProb ν A := by
  refine le_antisymm (coupling_eventMass_le hP hA) ?_
  have hsum : ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) = 0 :=
    Finset.sum_eq_zero fun e _ => by rw [hmarg e]; ring
  have h := eventMass_diff_le_edgeMarg_sum hP hA
  rw [hsum] at h; linarith

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Boundary-condition comparisons -/

lemma edgeMargProb_fkProb (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (fkProb G p q) e = edgeMarginalOpen G p q e := by
  unfold edgeMargProb edgeMarginalOpen
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω e <;> simp [h]

/-- The mass `φ^C_{G,p,q}(A)` of an event under the random-cluster measure with boundary graph `C`.
-/
noncomputable def bcEventMass (C : SimpleGraph V) [DecidableRel C.Adj] (p q : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma numClustersBC_antitone (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G C' ω ≤ numClustersBC G C ω := by
  unfold numClustersBC
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le (sup_le_sup_left hCC' (openSub G ω))

omit [DecidableEq V] in
lemma bcWeight_antitone (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (ω : ConfigSpace (Sym2 V)) :
    bcWeight G C' p q ω ≤ bcWeight G C p q ω := by
  unfold bcWeight
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hq (numClustersBC_antitone G C C' hCC' ω))
    (edgeProduct_pos G hp hp1 ω).le

omit [DecidableEq V] in
lemma bcWeight_qpow_le (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (N : ℕ) (ω : ConfigSpace (Sym2 V))
    (hb : numClustersBC G C ω ≤ numClustersBC G C' ω + N) :
    bcWeight G C p q ω ≤ q ^ N * bcWeight G C' p q ω := by
  unfold bcWeight
  have hpow : q ^ numClustersBC G C ω ≤ q ^ (numClustersBC G C' ω + N) :=
    pow_le_pow_right₀ hq hb
  rw [pow_add] at hpow
  have hep := (edgeProduct_pos G hp hp1 ω).le
  calc edgeProduct G p ω * q ^ numClustersBC G C ω
      ≤ edgeProduct G p ω * (q ^ numClustersBC G C' ω * q ^ N) :=
        mul_le_mul_of_nonneg_left hpow hep
    _ = q ^ N * (edgeProduct G p ω * q ^ numClustersBC G C' ω) := by ring

lemma bcZ_qpow_le (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (N : ℕ)
    (hb : ∀ ω, numClustersBC G C ω ≤ numClustersBC G C' ω + N) :
    bcZ G C p q ≤ q ^ N * bcZ G C' p q := by
  unfold bcZ
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun ω _ => bcWeight_qpow_le G C C' hp hp1 hq N ω (hb ω)

omit [DecidableEq V] [DecidableRel G.Adj] in
private lemma div_le_qpow_div {Nw Nf Zc Zc' qN : ℝ} (hNum : Nw ≤ Nf)
    (hNumnn : 0 ≤ Nf) (hZc : 0 < Zc) (hZc' : 0 < Zc')
    (hZbound : Zc ≤ qN * Zc') : Nw / Zc' ≤ qN * (Nf / Zc) := by
  have hrhs : qN * (Nf / Zc) = (qN * Nf) / Zc := by ring
  rw [hrhs, div_le_div_iff₀ hZc' hZc]
  calc Nw * Zc ≤ Nf * Zc := mul_le_mul_of_nonneg_right hNum hZc.le
    _ ≤ Nf * (qN * Zc') := mul_le_mul_of_nonneg_left hZbound hNumnn
    _ = qN * Nf * Zc' := by ring

/-- If the cluster counts with boundary graphs `C ≤ C'` differ by at most `N`, then
`φ^C(A) ≤ q^N φ^{C'}(A)` for nonnegative event indicators.
-/
lemma bcEventMass_le_qpow (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (N : ℕ) (hb : ∀ ω, numClustersBC G C ω ≤ numClustersBC G C' ω + N)
    {A : Set (ConfigSpace (Sym2 V))} (hA0 : ∀ ω, 0 ≤ A.indicator (fun _ => (1 : ℝ)) ω) :
    bcEventMass G C' p q A ≤ q ^ N * bcEventMass G C p q A := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ : 0 < bcZ G C p q := bcZ_pos G C hp hp1 hq0
  have hZ' : 0 < bcZ G C' p q := bcZ_pos G C' hp hp1 hq0
  set Nw := ∑ ω : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) ω * bcWeight G C' p q ω
    with hNw
  set Nf := ∑ ω : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) ω * bcWeight G C p q ω
    with hNf
  have hNum : Nw ≤ Nf := Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (bcWeight_antitone G C C' hCC' hp hp1 hq ω) (hA0 ω)
  have hNumnn : 0 ≤ Nf := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hA0 ω) (bcWeight_nonneg G C hp hp1 hq0 ω)
  have hZbound : bcZ G C p q ≤ q ^ N * bcZ G C' p q := bcZ_qpow_le G C C' hp hp1 hq N hb
  have hEM' : bcEventMass G C' p q A = Nw / bcZ G C' p q := by
    unfold bcEventMass bcProb
    rw [hNw, Finset.sum_div]
    exact Finset.sum_congr rfl fun ω _ => by rw [mul_div_assoc]
  have hEM : bcEventMass G C p q A = Nf / bcZ G C p q := by
    unfold bcEventMass bcProb
    rw [hNf, Finset.sum_div]
    exact Finset.sum_congr rfl fun ω _ => by rw [mul_div_assoc]
  rw [hEM', hEM]
  exact div_le_qpow_div hNum hNumnn hZ hZ' hZbound

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma card_connectedComponent_le_sup_fromEdgeSet (S : Finset (Sym2 V)) :
    ∀ A : SimpleGraph V,
      Nat.card A.ConnectedComponent
        ≤ Nat.card (A ⊔ fromEdgeSet (↑S)).ConnectedComponent + S.card := by
  classical
  induction S using Finset.induction with
  | empty => intro A; simp
  | insert e S he ih =>
    intro A
    have key : A ⊔ fromEdgeSet (↑(insert e S))
        = (A ⊔ fromEdgeSet (↑S)) ⊔ fromEdgeSet {e} := by
      rw [Finset.coe_insert, Set.insert_eq, fromEdgeSet_union, sup_comm (fromEdgeSet {e}),
        ← sup_assoc]
    obtain ⟨x, y, hxy⟩ : ∃ x y : V, fromEdgeSet ({e} : Set (Sym2 V)) = edge x y := by
      induction e using Sym2.ind with | _ x y => exact ⟨x, y, by rw [edge]⟩
    rw [key, hxy]
    have h1 := ih A
    have h2 := card_connectedComponent_le_sup_edge (A ⊔ fromEdgeSet (↑S)) x y
    rw [Finset.card_insert_of_notMem he]
    omega

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma numClustersBC_bot_le (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (⊥ : SimpleGraph V) ω ≤ numClustersBC G C' ω + C'.edgeFinset.card := by
  unfold numClustersBC
  rw [sup_bot_eq]
  have h := card_connectedComponent_le_sup_fromEdgeSet (V := V) C'.edgeFinset (openSub G ω)
  rwa [coe_edgeFinset, fromEdgeSet_edgeSet] at h

end FK

end StatMech
