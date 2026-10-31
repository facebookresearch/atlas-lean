/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PrefixCoversCluster
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentCovLowerBound

/-!
# Per-scale revealment and the frontier-connection hypothesis

Bounds on revealment by connection probabilities to the frontier at each scale, the family
frontier-connection hypothesis, and explicit refutations of the first-edge frontier connection.

## i. Overview

`FrontierConn σ f endU endV B e` (from `ReachBoxCrossing`) says that whenever `f` is undetermined
before `e` is revealed, an endpoint of `e` is connected to `B`. For the first edge of the order it
is refutable (`psr_frontierConn_first_refutable`), and `psr_frontierConn_first_false_concrete` is a
Lean-checked refutation on a 4-vertex example. `psr_perScale_of_familyFrontierConn` derives
per-scale revealment bounds from `psr_FamilyFrontierConn`, so it is conditional on that hypothesis;
`FrontierFamilyRevealment.frf_familyFrontierConn_false` refutes the hypothesis in the relevant
cases. Part of the revealment bounds for the OSSS covariance lower bound: the revealment of an edge
is bounded by the probability that it is connected to the frontier of the exploration.

## ii. Key results

- `psr_revealAdapt_le_connBox_frontier`: revealment ≤ connection to the box boundary, given
  `FrontierConn`.
- `psr_frontierConn_first_false_concrete`: refutation of the first-edge frontier connection.

## iii. Table of contents

- A. First-edge frontier connection
- B. Revealment bounds
- C. Family frontier connection
- D. Concrete witness

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace OSSS

namespace PerScaleRevealmentClose

open OSSS.Coding
open OSSS.AdaptMConditional
open StatMech.OSSS
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.ReachBoxCrossing
open StatMech.OSSS.ReachDomination
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.PrefixCoversClose
open StatMech.OSSS.FKRevealmentClose
open StatMech.OSSS.MonotonicFK
open StatMech.Lattice

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]

/-! ## A. First-edge frontier connection -/

omit [DecidableEq V] [Fintype E] in
lemma psr_frontierConn_first_iff {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (endU endV : E → V) (B : Set V) {e₀ : E} (he₀ : (σ.symm e₀ : ℕ) = 0) :
    FrontierConn σ f endU endV B e₀ ↔
      ∀ X : ConfigSpace E, (∃ w, f w ≠ f X) →
        ConnOpenSet endU endV X (endU e₀) B ∨ ConnOpenSet endU endV X (endV e₀) B := by
  unfold FrontierConn
  rw [he₀]
  have hpref : prefixSet (σ : Fin n → E) 0 = ∅ := prefixSet_zero _
  constructor
  · intro h X ⟨w, hw⟩
    refine h X (fun hdet => hw ?_)
    exact hdet w (by rw [hpref]; intro a ha; simp at ha)
  · intro h X hnotdet
    refine h X ?_
    by_contra hcon
    rw [not_exists] at hcon
    push Not at hcon
    exact hnotdet (fun w _ => hcon w)

omit [DecidableEq V] [Fintype E] in
lemma psr_frontierConn_first_refutable {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (endU endV : E → V) (B : Set V) {e₀ : E} (he₀ : (σ.symm e₀ : ℕ) = 0)
    (X : ConfigSpace E) (hnc : ∃ w, f w ≠ f X)
    (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) B)
    (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) B) :
    ¬ FrontierConn σ f endU endV B e₀ := by
  rw [psr_frontierConn_first_iff σ f endU endV B he₀]
  intro h
  rcases h X hnc with hU | hV
  · exact hnotU hU
  · exact hnotV hV

omit [DecidableEq V] [Fintype E] in
lemma psr_frontierConn_first_refutable_witness {n : ℕ} (σ : Fin n ≃ E)
    (endU endV : E → V) (B C : Set V) {e₀ : E} (he₀ : (σ.symm e₀ : ℕ) = 0)
    (X w : ConfigSpace E)
    (hX0 : ¬ ∃ x ∈ C, ConnOpenSet endU endV X x B)
    (hw1 : ∃ x ∈ C, ConnOpenSet endU endV w x B)
    (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) B)
    (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) B) :
    ¬ FrontierConn σ (indicatorConn endU endV B C) endU endV B e₀ := by
  refine psr_frontierConn_first_refutable σ _ endU endV B he₀ X ?_ hnotU hnotV
  refine ⟨w, ?_⟩
  unfold indicatorConn
  rw [ite_eq_left hw1, ite_eq_right hX0]
  norm_num

section Lattice

variable {d : ℕ}

/-! ## B. Revealment bounds -/

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
open Classical in
lemma psr_revealAdapt_le_connBox_of_pos {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {nE : ℕ} (σ : Fin nE ≃ E)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ)
    (hσ : ∀ e' : E, (TopIncident endU endV (vertexBoundary d k) e' ↔
        (σ.symm e' : ℕ) <
          (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card))
    (e : E)
    (he : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1
        ≤ (σ.symm e : ℕ))
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) := by
  have hfront : FrontierConn σ
      (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n))
      endU endV (vertexBoundary d k) e :=
    frontierConn_of_clusterMeasurable σ endU endV (vertexBoundary d k) e
      (clusterMeasurable_indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n))
      (prefixCoversCluster_clusterOrder σ endU endV (vertexBoundary d k) hσ e he)
  exact revealAdapt_le_connBox hpos hμ1 σ
    (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n))
    hinj hcoh hadj k e hfront

open Classical in
lemma psr_revealAdapt_le_connBox_frontier {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ) (nE : ℕ) (hnE : Fintype.card E = nE)
    (hne : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).Nonempty) :
    ∃ (σ : Fin nE ≃ E) (e : E),
      TopIncident endU endV (vertexBoundary d k) e ∧
      revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e
        ≤ Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                      then (1 : ℝ) else 0)
          + Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                      then (1 : ℝ) else 0) := by
  classical
  obtain ⟨σ, hσ⟩ := clusterOrder_exists (TopIncident endU endV (vertexBoundary d k)) nE hnE
  have hm1 : 1 ≤ (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card :=
    Finset.Nonempty.card_pos hne
  have hmn : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card ≤ nE := by
    rw [← hnE, ← Finset.card_univ]; exact Finset.card_filter_le _ _
  set e : E := σ ⟨(Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1,
      by omega⟩ with hedef
  have hsymm : (σ.symm e : ℕ) =
      (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1 := by
    rw [hedef, Equiv.symm_apply_apply]
  have htop : TopIncident endU endV (vertexBoundary d k) e := by rw [hσ e, hsymm]; omega
  refine ⟨σ, e, htop, ?_⟩
  exact psr_revealAdapt_le_connBox_of_pos hpos hμ1 σ hinj hcoh hadj k n hσ e (by rw [hsymm])

end Lattice

/-! ## C. Family frontier connection -/

/-- The frontier-connection property for every order `σf k` of a family, with frontier `B k`. -/
def psr_FamilyFrontierConn {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ) (endU endV : E → V) (B : κ → Set V) : Prop :=
  ∀ (k : κ) (e : E), FrontierConn (σf k) f endU endV (B k) e

section LatticeResidue

variable {d : ℕ}

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
lemma psr_perScale_of_familyFrontierConn {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (kscale : κ → ℕ)
    [∀ k e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d (kscale k)))]
    [∀ k e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d (kscale k)))]
    [∀ k e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d (kscale k)))]
    [∀ k e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d (kscale k)))]
    (hfront : psr_FamilyFrontierConn σf f endU endV (fun k => vertexBoundary d (kscale k))) :
    ∀ (k : κ) (e : E),
      revealAdapt μ (σf k) f e
        ≤ Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d (kscale k))
                      then (1 : ℝ) else 0)
          + Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d (kscale k))
                      then (1 : ℝ) else 0) :=
  fun k e =>
    revealAdapt_le_connBox hpos hμ1 (σf k) f hinj hcoh hadj (kscale k) e (hfront k e)

end LatticeResidue

section FKResidue

variable {W : Type*} [Fintype W] [DecidableEq W]

end FKResidue

omit [DecidableEq V] [Fintype E] in
lemma psr_familyFrontierConn_univ {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ) (endU endV : E → V) :
    psr_FamilyFrontierConn σf f endU endV (fun _ => (Set.univ : Set V)) :=
  fun k e => frontierConn_univ (σf k) f endU endV e

omit [DecidableEq E] [DecidableEq V] [Fintype E] in
lemma psr_reachOpen_allClosed {endU endV : E → V} {x y : V}
    (h : ReachOpen endU endV (fun _ => false) x y) : x = y := by
  induction h with
  | refl x => rfl
  | step e hopen _ _ _ => simp at hopen

/-! ## D. Concrete witness -/

/-- First endpoints of the three edges of the 4-vertex witness graph. -/
def psr_witnessEndU : Fin 3 → Fin 4 := ![1, 0, 2]

/-- Second endpoints of the three edges of the 4-vertex witness graph. -/
def psr_witnessEndV : Fin 3 → Fin 4 := ![2, 1, 3]

/-- Refutation of the first-edge frontier connection. -/
theorem psr_frontierConn_first_false_concrete (σ : Fin 3 ≃ Fin 3) (he₀ : (σ.symm 0 : ℕ) = 0) :
    ¬ FrontierConn σ
        (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4)))
        psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) (0 : Fin 3) := by
  refine psr_frontierConn_first_refutable_witness σ psr_witnessEndU psr_witnessEndV
    ({0} : Set (Fin 4)) ({3} : Set (Fin 4)) he₀
    (fun _ => false) (fun _ => true) ?_ ?_ ?_ ?_
  · rintro ⟨x, hxC, b, hbB, hreach⟩
    simp only [Set.mem_singleton_iff] at hxC hbB
    have := psr_reachOpen_allClosed hreach; omega
  · refine ⟨3, Set.mem_singleton 3, 0, Set.mem_singleton 0, ?_⟩
    refine ReachOpen.step 2 rfl (Or.inr ⟨rfl, rfl⟩) ?_
    refine ReachOpen.step 0 rfl (Or.inr ⟨rfl, rfl⟩) ?_
    refine ReachOpen.step 1 rfl (Or.inr ⟨rfl, rfl⟩) ?_
    exact ReachOpen.refl 0
  · rintro ⟨b, hbB, hreach⟩
    simp only [Set.mem_singleton_iff] at hbB
    have := psr_reachOpen_allClosed hreach
    simp only [psr_witnessEndU, Matrix.cons_val_zero] at this; omega
  · rintro ⟨b, hbB, hreach⟩
    simp only [Set.mem_singleton_iff] at hbB
    have := psr_reachOpen_allClosed hreach
    simp only [psr_witnessEndV, Matrix.cons_val_zero] at this; omega

end PerScaleRevealmentClose

end OSSS

end StatMech
