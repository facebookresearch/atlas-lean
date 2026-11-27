/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ReachBoxCrossing

/-!
# Cluster-measurable observables and reach domination

Observables that depend only on the cluster of the frontier, and the resulting frontier-connection
property and covariance lower bound.

## i. Overview

`IncidentCluster endU endV X B e'` says that `e'` meets the open cluster of `B`. A
`ClusterMeasurable` observable depends only on the edges of this cluster; connection indicators are
cluster measurable (`clusterMeasurable_indicatorConn`). For such observables, `PrefixCoversCluster`
implies `FrontierConn` (`frontierConn_of_clusterMeasurable`).
`os_cov_lower_bound_from_clusterMeasurable` is conditional on `PrefixCoversCluster` and the
connection bounds. Part of the revealment bounds for the OSSS covariance lower bound: the revealment
of an edge is bounded by the probability that it is connected to the frontier of the exploration.

## ii. Key results

- `frontierConn_of_clusterMeasurable`: `PrefixCoversCluster` ⇒ `FrontierConn` for cluster-measurable
  `f`.
- `os_cov_lower_bound_from_clusterMeasurable`: covariance lower bound, conditional on
  `PrefixCoversCluster` and connection bounds.

## iii. Table of contents

- A. Incident clusters
- B. Cluster-measurable observables
- C. Frontier connection and covariance bounds

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace OSSS

namespace ReachDomination

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.AdaptDisintegration
open OSSS.GrandCoupling OSSS.Coding
open StatMech.OSSS.RevealmentBoundAssembly
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.ReachBoxCrossing
open StatMech.Lattice

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]

/-! ## A. Incident clusters -/

/-- The edge `e'` has an endpoint connected to `B` by open edges of `X`. -/
def IncidentCluster (endU endV : E → V) (X : ConfigSpace E) (B : Set V) (e' : E) : Prop :=
  ConnOpenSet endU endV X (endU e') B ∨ ConnOpenSet endU endV X (endV e') B

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma reachOpen_stable_to_B {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {x b : V} (hb : b ∈ B) (h : ReachOpen endU endV X x b) :
    ReachOpen endU endV w x b := by
  induction h with
  | refl x => exact ReachOpen.refl x
  | @step a c z e hopen hpair hrest ih =>
      have hcB : ConnOpenSet endU endV X c B := ⟨z, hb, hrest⟩
      have hincid : IncidentCluster endU endV X B e := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · exact Or.inr (by rw [hV]; exact hcB)
        · exact Or.inl (by rw [hU]; exact hcB)
      have hwopen : w e = true := by rw [hagree e hincid]; exact hopen
      exact ReachOpen.step e hwopen hpair (ih hb)

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma connOpenSet_stable_of_agree {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {x : V} (h : ConnOpenSet endU endV X x B) :
    ConnOpenSet endU endV w x B := by
  obtain ⟨b, hbB, hreach⟩ := h
  exact ⟨b, hbB, reachOpen_stable_to_B hagree hbB hreach⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma reachOpen_stable_from_B {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {b y : V} (hb : ConnOpenSet endU endV X b B) (h : ReachOpen endU endV w b y) :
    ConnOpenSet endU endV X y B := by
  induction h with
  | refl x => exact hb
  | @step a c z e hopen hpair hrest ih =>
      have hincid : IncidentCluster endU endV X B e := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · exact Or.inl (by rw [hU]; exact hb)
        · exact Or.inr (by rw [hV]; exact hb)
      have hXopen : X e = true := by rw [← hagree e hincid]; exact hopen
      have hcB : ConnOpenSet endU endV X c B := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · have hbU : ConnOpenSet endU endV X (endU e) B := by rw [hU]; exact hb
          have := connOpenSet_prop hXopen hbU
          rwa [hV] at this
        · have hbV : ConnOpenSet endU endV X (endV e) B := by rw [hV]; exact hb
          have := connOpenSet_prop' hXopen hbV
          rwa [hU] at this
      exact ih hcB

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma connOpenSet_iff_of_agree {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {x : V} :
    ConnOpenSet endU endV w x B ↔ ConnOpenSet endU endV X x B := by
  constructor
  · rintro ⟨b, hbB, hreach⟩
    exact reachOpen_stable_from_B hagree (connOpenSet_of_mem hbB) (reachOpen_symm hreach)
  · exact connOpenSet_stable_of_agree hagree

/-! ## B. Cluster-measurable observables -/

/-- The observable `f` takes the same value on configurations that agree on all edges incident to
  the cluster of `B`. -/
def ClusterMeasurable (f : ConfigSpace E → ℝ) (endU endV : E → V) (B : Set V) : Prop :=
  ∀ X w : ConfigSpace E,
    (∀ e', IncidentCluster endU endV X B e' → w e' = X e') → f w = f X

open Classical in
/-- The indicator that some site of `C` is connected to `B` by open edges. -/
noncomputable def indicatorConn (endU endV : E → V) (B C : Set V) (X : ConfigSpace E) : ℝ :=
  if ∃ x ∈ C, ConnOpenSet endU endV X x B then (1 : ℝ) else 0

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] in
lemma clusterMeasurable_indicatorConn (endU endV : E → V) (B C : Set V) :
    ClusterMeasurable (indicatorConn endU endV B C) endU endV B := by
  intro X w hagree
  unfold indicatorConn
  by_cases hX : ∃ x ∈ C, ConnOpenSet endU endV X x B
  · obtain ⟨x, hxC, hconn⟩ := hX
    have hw : ∃ x ∈ C, ConnOpenSet endU endV w x B :=
      ⟨x, hxC, connOpenSet_stable_of_agree hagree hconn⟩
    rw [ite_eq_left hw, ite_eq_left ⟨x, hxC, hconn⟩]
  · have hw : ¬ ∃ x ∈ C, ConnOpenSet endU endV w x B := by
      rintro ⟨x, hxC, hconn⟩
      exact hX ⟨x, hxC, (connOpenSet_iff_of_agree hagree).mp hconn⟩
    rw [ite_eq_right hw, ite_eq_right hX]

/-! ## C. Frontier connection and covariance bounds -/

/-- Every edge incident to the cluster of `B` comes before `e` in the order `σ`, in every
  configuration where `e` is not incident. -/
def PrefixCoversCluster {n : ℕ} (σ : Fin n ≃ E) (endU endV : E → V) (B : Set V)
    (e : E) : Prop :=
  ∀ X : ConfigSpace E, ∀ e' : E, e' ≠ e →
    IncidentCluster endU endV X B e' → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)

omit [Fintype E] in
omit [DecidableEq V] in
lemma detAtC_of_not_incident {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (endU endV : E → V) (B : Set V) (e : E) (X : ConfigSpace E)
    (hfmeas : ClusterMeasurable f endU endV B)
    (hcover : PrefixCoversCluster σ endU endV B e)
    (hnotincid : ¬ IncidentCluster endU endV X B e) :
    detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) := by
  intro w hw
  refine hfmeas X w (fun e' hincid => ?_)
  by_cases he' : e' = e
  · exact absurd (he' ▸ hincid) hnotincid
  · exact hw e' (hcover X e' he' hincid)

omit [Fintype E] in
omit [DecidableEq V] in
lemma frontierConn_of_clusterMeasurable {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (endU endV : E → V) (B : Set V) (e : E)
    (hfmeas : ClusterMeasurable f endU endV B)
    (hcover : PrefixCoversCluster σ endU endV B e) :
    FrontierConn σ f endU endV B e := by
  intro X hnotdet
  by_contra hcon
  exact hnotdet (detAtC_of_not_incident σ endU endV B e X hfmeas hcover hcon)

section Lattice

variable {d : ℕ}

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
lemma reachProb_le_connBox_of_clusterMeasurable {μ : ConfigSpace E → ℝ}
    (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (e : E)
    (hfmeas : ClusterMeasurable f endU endV (vertexBoundary d k))
    (hcover : PrefixCoversCluster σ endU endV (vertexBoundary d k) e)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) :=
  reachProb_le_connBox hμ0 σ f hinj hcoh hadj k e
    (frontierConn_of_clusterMeasurable σ endU endV (vertexBoundary d k) e hfmeas hcover)

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
lemma os_cov_lower_bound_from_clusterMeasurable {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (D : ℝ) (hDpos : 0 < D)
    [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    (hfmeas : ClusterMeasurable f endU endV (vertexBoundary d k))
    (hcover : ∀ e, PrefixCoversCluster σ endU endV (vertexBoundary d k) e)
    (hbox : ∀ e,
      Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) ≤ D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) :=
  os_cov_lower_bound_from_box_crossing hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem
    hinj hcoh hadj k D hDpos
    (fun e => frontierConn_of_clusterMeasurable σ endU endV (vertexBoundary d k) e
      hfmeas (hcover e))
    hbox

end Lattice

omit [DecidableEq V] [Fintype E] in
lemma prefixCoversCluster_of_prefix_cofinite {n : ℕ} (σ : Fin n ≃ E) (endU endV : E → V)
    (B : Set V) (e : E)
    (hcofin : ∀ e' : E, e' ≠ e → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)) :
    PrefixCoversCluster σ endU endV B e :=
  fun _ e' he' _ => hcofin e' he'

omit [Fintype E] in
lemma prefix_cofinite_of_last {n : ℕ} (hn : 1 ≤ n) (σ : Fin n ≃ E)
    {e : E} (he : (σ.symm e : ℕ) = n - 1) :
    ∀ e' : E, e' ≠ e → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ) := by
  intro e' he'
  rw [mem_prefixSet_iff]
  refine ⟨σ.symm e', ?_, by simp⟩
  have hne : (σ.symm e' : Fin n) ≠ σ.symm e := fun h => he' (by
    have := congrArg σ h; simpa using this)
  have hval : (σ.symm e' : ℕ) ≠ (σ.symm e : ℕ) := fun h => hne (Fin.ext h)
  have hlt : (σ.symm e' : ℕ) < n := (σ.symm e').2
  rw [he]; omega

omit [DecidableEq V] [Fintype E] in
lemma frontierConn_indicatorConn_last {n : ℕ} (hn : 1 ≤ n) (σ : Fin n ≃ E)
    (endU endV : E → V) (B C : Set V) {e : E} (he : (σ.symm e : ℕ) = n - 1) :
    FrontierConn σ (indicatorConn endU endV B C) endU endV B e :=
  frontierConn_of_clusterMeasurable σ endU endV B e
    (clusterMeasurable_indicatorConn endU endV B C)
    (prefixCoversCluster_of_prefix_cofinite σ endU endV B e
      (prefix_cofinite_of_last hn σ he))

end ReachDomination

end OSSS

end StatMech
