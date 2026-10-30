/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveBoundaryEquiv
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxDomainMarkov

/-!
# Domain Markov property for edge subgraphs

Conditioned on the states of all edges outside a subgraph `K ≤ H`, the random-cluster measure on `H`
with boundary wiring `B` restricted to `K` is the random-cluster measure on `K` whose boundary
wiring is induced by the open exterior edges.

## i. Overview

Freeze a configuration `ψ` outside `K`. The open exterior edges together with `B` form the graph
`edgeSubsetFrozenExteriorGraph`; joining every pair of vertices it connects gives the induced wiring
`edgeSubsetInducedWiring`. Configurations of the fibre over `ψ` correspond to configurations of `K`,
the cluster count of a fibre configuration equals the cluster count on `K` with the induced wiring,
and the Bernoulli product splits into a fixed exterior factor times the product over `K`. The
exterior factor cancels in the conditional probability, which yields the domain Markov property of
the random-cluster model. The key results are proved unconditionally (only `0 < p < 1`, and `0 < q`
for the event form).

## ii. Key results

- `numClustersBC_edgeSubsetFibre_eq_induced` : cluster counts on a fibre equal cluster counts on `K`
  with the induced wiring.
- `edgeSubsetFibre_condBcProb_eq_activeBCProb` : the conditional law on a fibre is the
  random-cluster law on `K` with the induced wiring.
- `edgeSubsetFibreCondEventMass_eq_bcEventMass` : the same statement for events of `K`.

## iii. Table of contents

- A. Frozen exterior and induced wiring
- B. Fibre configurations
- C. Cluster counts on a fibre
- D. Weights and partition functions
- E. Conditional laws

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open Finset SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A. Frozen exterior and induced wiring -/

/-- The graph of edges of `H` outside `K` that are open in `ψ`, together with the boundary wiring
`B`. -/
noncomputable def edgeSubsetFrozenExteriorGraph
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := (H.Adj x y ∧ ¬K.Adj x y ∧ psi s(x, y) = true) ∨ B.Adj x y
  symm := by
    constructor
    rintro x y (hxy | hxy)
    · exact Or.inl ⟨hxy.1.symm, fun hyx => hxy.2.1 hyx.symm,
        by simpa [Sym2.eq_swap] using hxy.2.2⟩
    · exact Or.inr hxy.symm
  loopless := ⟨by
    rintro x (hxx | hxx)
    · exact (H.ne_of_adj hxx.1) rfl
    · exact (B.ne_of_adj hxx) rfl⟩

/-- Adjacency in the frozen exterior graph is decidable (classically). -/
noncomputable instance edgeSubsetFrozenExteriorGraphDecidableAdj
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) :
    DecidableRel (edgeSubsetFrozenExteriorGraph K H B psi).Adj :=
  Classical.decRel _

/-- The induced boundary wiring: distinct vertices are adjacent when the frozen exterior graph
connects them. -/
noncomputable def edgeSubsetInducedWiring
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧
    (edgeSubsetFrozenExteriorGraph K H B psi).Reachable x y
  symm := by
    constructor
    rintro x y ⟨hne, hxy⟩
    exact ⟨hne.symm, hxy.symm⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

/-- Adjacency in the induced wiring is decidable (classically). -/
noncomputable instance edgeSubsetInducedWiringDecidableAdj
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) :
    DecidableRel (edgeSubsetInducedWiring K H B psi).Adj :=
  Classical.decRel _

/-! ## B. Fibre configurations -/

/-- The configuration equal to `η` on the edges of `K` and to `ψ` elsewhere. -/
noncomputable def edgeSubsetFibreConfig (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    ConfigSpace (Sym2 V) := fun e =>
  if h : e ∈ K.edgeSet then eta ⟨e, h⟩ else psi e

lemma edgeSubsetFibreConfig_agreesOff (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    AgreesOff K.edgeFinset psi (edgeSubsetFibreConfig K psi eta) := by
  intro e he
  have hnot : e ∉ K.edgeSet := by
    intro hmem
    exact he (SimpleGraph.mem_edgeFinset.mpr hmem)
  simp [edgeSubsetFibreConfig, hnot]

@[simp] theorem edgeSubsetFibreConfig_restrictActive (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    restrictActive K (edgeSubsetFibreConfig K psi eta) = eta := by
  funext e
  simp [restrictActive, edgeSubsetFibreConfig, e.2]

lemma edgeSubsetFibreConfig_restrictActive_eq (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi rho : ConfigSpace (Sym2 V))
    (hrho : AgreesOff K.edgeFinset psi rho) :
    edgeSubsetFibreConfig K psi (restrictActive K rho) = rho := by
  funext e
  by_cases he : e ∈ K.edgeSet
  · simp [edgeSubsetFibreConfig, restrictActive, he]
  · rw [edgeSubsetFibreConfig, dite_eq_right he]
    exact (hrho e (by
      simpa [SimpleGraph.mem_edgeFinset] using he)).symm

/-- Configurations of `K` are in bijection with the configurations that agree with `ψ` off `K`. -/
noncomputable def edgeSubsetFibreEquiv (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) :
    ConfigSpace K.edgeSet ≃
      {rho : ConfigSpace (Sym2 V) // rho ∈ condFibre K.edgeFinset psi} where
  toFun eta := ⟨edgeSubsetFibreConfig K psi eta, by
    rw [mem_condFibre]
    exact edgeSubsetFibreConfig_agreesOff K psi eta⟩
  invFun rho := restrictActive K rho.1
  left_inv eta := edgeSubsetFibreConfig_restrictActive K psi eta
  right_inv rho := by
    apply Subtype.ext
    exact edgeSubsetFibreConfig_restrictActive_eq K psi rho.1
      (mem_condFibre.mp rho.2)

/-! ## C. Cluster counts on a fibre -/

lemma openSub_edgeSubsetFibre_sup_frozen
    (K H B : SimpleGraph V) [DecidableRel K.Adj] (hKH : K ≤ H)
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    openSub H (edgeSubsetFibreConfig K psi eta) ⊔ B =
      openSub K (extendActive K eta) ⊔
        edgeSubsetFrozenExteriorGraph K H B psi := by
  ext x y
  simp only [openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hH, hopen⟩ | hB)
    · by_cases hK : K.Adj x y
      · left
        refine ⟨hK, ?_⟩
        have he : s(x, y) ∈ K.edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hK
        rw [extendActive_apply K eta ⟨s(x, y), he⟩]
        simpa [edgeSubsetFibreConfig, he] using hopen
      · right
        exact Or.inl ⟨hH, hK, by
          simpa [edgeSubsetFibreConfig,
            show s(x, y) ∉ K.edgeSet by
              rwa [SimpleGraph.mem_edgeSet]] using hopen⟩
    · exact Or.inr (Or.inr hB)
  · rintro (⟨hK, hopen⟩ | (hExt | hB))
    · left
      refine ⟨hKH hK, ?_⟩
      have he : s(x, y) ∈ K.edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hK
      rw [edgeSubsetFibreConfig, dite_eq_left he]
      rw [extendActive_apply K eta ⟨s(x, y), he⟩] at hopen
      exact hopen
    · left
      refine ⟨hExt.1, ?_⟩
      have he : s(x, y) ∉ K.edgeSet := hExt.2.1
      simpa [edgeSubsetFibreConfig, he] using hExt.2.2
    · exact Or.inr hB

/-- If every edge of `A` joins vertices connected in `L`, then reachability in `A` implies
reachability in `L`. -/
private lemma reachable_of_adj_reachable
    {W : Type*} {A L : SimpleGraph W}
    (hstep : ∀ {x y}, A.Adj x y → L.Reachable x y)
    {x y : W} (hxy : A.Reachable x y) : L.Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact .refl _
  | cons huv w ih => exact (hstep huv).trans ih

lemma sup_edgeSubsetFrozen_reachable_iff_induced
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V))
    (A : SimpleGraph V) (x y : V) :
    (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).Reachable x y ↔
      (A ⊔ edgeSubsetInducedWiring K H B psi).Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    rcases huv with hA | hE
    · exact Or.inl hA
    · exact Or.inr ⟨hE.ne, hE.reachable⟩
  · intro hxy
    apply reachable_of_adj_reachable (A :=
      A ⊔ edgeSubsetInducedWiring K H B psi) ?_ hxy
    intro u v huv
    rcases huv with hA | hC
    · exact (show (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).Adj u v
        from Or.inl hA).reachable
    · exact hC.2.mono le_sup_right

/-- Adding the frozen exterior graph or the induced wiring to `A` gives the same connected
components. -/
noncomputable def edgeSubsetExteriorComponentEquiv
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V))
    (A : SimpleGraph V) :
    (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).ConnectedComponent ≃
      (A ⊔ edgeSubsetInducedWiring K H B psi).ConnectedComponent := by
  let L := A ⊔ edgeSubsetFrozenExteriorGraph K H B psi
  let R := A ⊔ edgeSubsetInducedWiring K H B psi
  apply Equiv.ofBijective (fun C : L.ConnectedComponent =>
    R.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hR : R.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hL : L.Reachable C.out D.out :=
      (sup_edgeSubsetFrozen_reachable_iff_induced
        K H B psi A C.out D.out).mpr hR
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hL
  · intro D
    let C := L.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hL : L.Reachable C.out D.out := ConnectedComponent.exact C.out_eq
    exact (sup_edgeSubsetFrozen_reachable_iff_induced
      K H B psi A C.out D.out).mp hL

/-- The number of clusters of a fibre configuration on `H` with wiring `B` equals the number of
clusters of its `K`-part with the induced wiring. -/
lemma numClustersBC_edgeSubsetFibre_eq_induced
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    (eta : ConfigSpace K.edgeSet) :
    numClustersBC H B (edgeSubsetFibreConfig K psi eta) =
      numClustersBC K (edgeSubsetInducedWiring K H B psi)
        (extendActive K eta) := by
  unfold numClustersBC
  rw [openSub_edgeSubsetFibre_sup_frozen K H B hKH psi eta]
  exact Nat.card_congr (edgeSubsetExteriorComponentEquiv K H B psi
    (openSub K (extendActive K eta)))

/-! ## D. Weights and partition functions -/

/-- The Bernoulli weight of the frozen edges of `H` outside `K`. -/
noncomputable def edgeSubsetExteriorEdgeFactor
    (K H : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (psi : ConfigSpace (Sym2 V)) (p : Real) : Real :=
  ∏ e ∈ H.edgeFinset \ K.edgeFinset, if psi e then p else 1 - p

lemma edgeProduct_edgeSubsetFibre
    (K H : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] (hKH : K ≤ H)
    (psi : ConfigSpace (Sym2 V)) (p : Real)
    (eta : ConfigSpace K.edgeSet) :
    edgeProduct H p (edgeSubsetFibreConfig K psi eta) =
      edgeSubsetExteriorEdgeFactor K H psi p *
        edgeProduct K p (extendActive K eta) := by
  classical
  let O := H.edgeFinset \ K.edgeFinset
  have hfactor : edgeSubsetExteriorEdgeFactor K H psi p =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    unfold edgeSubsetExteriorEdgeFactor
    apply Finset.prod_congr
    · ext e
      simp [O]
    · intro e he
      rfl
  have hsub : K.edgeFinset ⊆ H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact hKH he
  have hedges : H.edgeFinset = K.edgeFinset ∪ O :=
    (Finset.union_sdiff_of_subset hsub).symm
  have hdisj : Disjoint K.edgeFinset O := Finset.disjoint_sdiff
  have hinner :
      (∏ e ∈ K.edgeFinset,
        if edgeSubsetFibreConfig K psi eta e then p else 1 - p) =
      ∏ e ∈ K.edgeFinset,
        if extendActive K eta e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heSet : e ∈ K.edgeSet := by
      rwa [← SimpleGraph.mem_edgeFinset]
    have hfibre : edgeSubsetFibreConfig K psi eta e = eta ⟨e, heSet⟩ := by
      simp [edgeSubsetFibreConfig, heSet]
    have hactive := extendActive_apply K eta ⟨e, heSet⟩
    rw [hfibre, hactive]
  have houter :
      (∏ e ∈ O,
        if edgeSubsetFibreConfig K psi eta e then p else 1 - p) =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heNot : e ∉ K.edgeSet := by
      have : e ∉ K.edgeFinset := (Finset.mem_sdiff.mp he).2
      simpa [SimpleGraph.mem_edgeFinset] using this
    simp [edgeSubsetFibreConfig, heNot]
  unfold edgeProduct
  rw [hedges, Finset.prod_union hdisj, hinner, houter, hfactor]
  exact mul_comm _ _

lemma bcWeight_edgeSubsetFibre_eq_induced
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V)) (p q : Real)
    (eta : ConfigSpace K.edgeSet) :
    bcWeight H B p q (edgeSubsetFibreConfig K psi eta) =
      edgeSubsetExteriorEdgeFactor K H psi p *
        activeBCWeight K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q eta := by
  rw [bcWeight, edgeProduct_edgeSubsetFibre K H hKH psi p eta,
    numClustersBC_edgeSubsetFibre_eq_induced K H B hKH psi eta]
  rw [activeBCWeight_const_eq_bcWeight]
  unfold bcWeight
  ring

set_option maxHeartbeats 800000 in
-- The fibre sum unfolds large `Finset` sums over configurations.

lemma edgeSubset_inducedBcZ_eq
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V)) (p q : Real) :
    inducedBcZ H B p q K.edgeFinset psi =
      edgeSubsetExteriorEdgeFactor K H psi p *
        activeBCZ K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q := by
  unfold inducedBcZ activeBCZ
  let S := condFibre K.edgeFinset psi
  let weight := fun rho : ConfigSpace (Sym2 V) => bcWeight H B p q rho
  calc
    (∑ rho ∈ S, weight rho) = ∑ rho : {rho // rho ∈ S}, weight rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) weight
    _ = ∑ eta, weight ((edgeSubsetFibreEquiv K psi) eta) :=
      (Equiv.sum_comp (edgeSubsetFibreEquiv K psi)
        (fun rho => weight rho.1)).symm
    _ = ∑ eta, edgeSubsetExteriorEdgeFactor K H psi p *
        activeBCWeight K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q eta := by
      apply Finset.sum_congr rfl
      intro eta _
      exact bcWeight_edgeSubsetFibre_eq_induced
        K H B hKH psi p q eta
    _ = edgeSubsetExteriorEdgeFactor K H psi p *
        ∑ eta, activeBCWeight K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q eta := by rw [Finset.mul_sum]

/-! ## E. Conditional laws -/

/-- Domain Markov property: the conditional random-cluster law on the fibre over `ψ` is the
random-cluster law on `K` with the induced wiring. -/
theorem edgeSubsetFibre_condBcProb_eq_activeBCProb
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1)
    (eta : ConfigSpace K.edgeSet) :
    condBcProb H B p q K.edgeFinset psi
        (edgeSubsetFibreConfig K psi eta) =
      activeBCProb K (edgeSubsetInducedWiring K H B psi)
        (fun _ => p) q eta := by
  unfold condBcProb activeBCProb
  rw [ite_eq_left (edgeSubsetFibreConfig_agreesOff K psi eta)]
  rw [bcWeight_edgeSubsetFibre_eq_induced K H B hKH psi p q eta,
    edgeSubset_inducedBcZ_eq K H B hKH psi p q]
  exact mul_div_mul_left _ _ (by
    unfold edgeSubsetExteriorEdgeFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    split
    · exact hp.ne'
    · exact (sub_pos.mpr hp1).ne')

/-- The conditional probability, given the exterior configuration `ψ`, of an event `A` of `K`. -/
noncomputable def edgeSubsetFibreCondEventMass
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 V)) (p q : Real)
    (A : Set (ConfigSpace K.edgeSet)) : Real :=
  ∑ eta, A.indicator (fun _ => (1 : Real)) eta *
    condBcProb H B p q K.edgeFinset psi
      (edgeSubsetFibreConfig K psi eta)

lemma edgeSubsetFibreCondEventMass_eq_activeBCProbOf
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace K.edgeSet)) :
    edgeSubsetFibreCondEventMass K H B psi p q A =
      activeBCProbOf K (edgeSubsetInducedWiring K H B psi)
        (fun _ => p) q A := by
  classical
  unfold edgeSubsetFibreCondEventMass activeBCProbOf activeBCMean
  apply Finset.sum_congr rfl
  intro eta _
  rw [edgeSubsetFibre_condBcProb_eq_activeBCProb
    K H B hKH psi hp hp1 eta]

/-- Domain Markov property for events: the conditional probability of an event of `K` given the
exterior equals its probability under the random-cluster measure on `K` with the induced wiring. -/
theorem edgeSubsetFibreCondEventMass_eq_bcEventMass
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace K.edgeSet)) :
    edgeSubsetFibreCondEventMass K H B psi p q A =
      bcEventMass K (edgeSubsetInducedWiring K H B psi) p q
        (restrictActive K ⁻¹' A) := by
  classical
  rw [edgeSubsetFibreCondEventMass_eq_activeBCProbOf
      K H B hKH psi hp hp1 A,
    activeBCProbOf_eq_bcProb_preimage
      K (edgeSubsetInducedWiring K H B psi) hp hp1 hq]
  rfl

set_option maxHeartbeats 800000 in
-- The fibre sum unfolds large `Finset` sums over configurations.

lemma edgeSubsetFibreCondEventMass_eq_ambientSum
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 V)) (p q : Real)
    (A : Set (ConfigSpace K.edgeSet)) :
    edgeSubsetFibreCondEventMass K H B psi p q A =
      ∑ rho, (restrictActive K ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        condBcProb H B p q K.edgeFinset psi rho := by
  classical
  let S := condFibre K.edgeFinset psi
  let term := fun rho : ConfigSpace (Sym2 V) =>
    (restrictActive K ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
      condBcProb H B p q K.edgeFinset psi rho
  have hrestrict : (∑ rho, term rho) = ∑ rho ∈ S, term rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho _ hrho
    have hnot : ¬AgreesOff K.edgeFinset psi rho := by
      rw [mem_condFibre] at hrho
      exact hrho
    unfold term condBcProb
    rw [ite_eq_right hnot, mul_zero]
  symm
  calc
    (∑ rho, term rho) = ∑ rho ∈ S, term rho := hrestrict
    _ = ∑ rho : {rho // rho ∈ S}, term rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) term
    _ = ∑ eta, term ((edgeSubsetFibreEquiv K psi) eta) :=
      (Equiv.sum_comp (edgeSubsetFibreEquiv K psi)
        (fun rho => term rho.1)).symm
    _ = edgeSubsetFibreCondEventMass K H B psi p q A := by
      unfold edgeSubsetFibreCondEventMass term
      apply Finset.sum_congr rfl
      intro eta _
      change
        (restrictActive K ⁻¹' A).indicator (fun _ => (1 : Real))
            (edgeSubsetFibreConfig K psi eta) *
          condBcProb H B p q K.edgeFinset psi
            (edgeSubsetFibreConfig K psi eta) =
        A.indicator (fun _ => (1 : Real)) eta *
          condBcProb H B p q K.edgeFinset psi
            (edgeSubsetFibreConfig K psi eta)
      by_cases heta : eta ∈ A
      · rw [Set.indicator_of_mem heta,
          Set.indicator_of_mem (show
            edgeSubsetFibreConfig K psi eta ∈ restrictActive K ⁻¹' A by
              simpa using heta)]
      · rw [Set.indicator_of_notMem heta,
          Set.indicator_of_notMem (show
            edgeSubsetFibreConfig K psi eta ∉ restrictActive K ⁻¹' A by
              simpa using heta)]

end

end StatMech.FK
