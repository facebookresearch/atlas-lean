/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredPressureDeriv

/-!
# Centered free energies

The finite-volume free energies in the tilt variable, centered to vanish at `t = 0`, are convex,
`1`-Lipschitz, and differentiable with derivative the average edge density.

## i. Overview

`cfe_centered G q t` is the tilt free energy minus its value at `0`, and `cfe_wiredCentered` the
same for wired boundary conditions. For `q = 2` the derivative is the average edge density in
`[0, 1]`, so the centered energy is monotone, `t - cfe_centered` is monotone, and
`|cfe_centered t| ≤ |t|`. These are the inputs of the centered convexity argument run in
`UniquenessGeneralQ`.

## ii. Key results

- `cfe_centered_convexOn`, `cfe_centered_hasDerivAt` : convexity and derivative.
- `cfe_centered_abs_le` : `|cfe_centered G 2 t| ≤ |t|`.

## iii. Table of contents

- A. Centered free energies
- B. Wired centered free energies
- C. Convergence along boxes
- D. Uniqueness

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorems 4.58 and 4.63.
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Centered free energies -/

/-- The tilt free energy of `G` centered at `t = 0`: `F_G(t) - F_G(0)` with
`F_G(t) = |E|^{-1} log Z_G(logistic(t), q) + log(1 + e^t)`.
-/
noncomputable def cfe_centered (q : ℝ) (t : ℝ) : ℝ :=
  ivp2_tiltFreeEnergy G q t - ivp2_tiltFreeEnergy G q 0

@[simp] lemma cfe_centered_zero (q : ℝ) : cfe_centered G q 0 = 0 := by
  unfold cfe_centered; ring

lemma cfe_centered_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (cfe_centered G q) := by
  have hconv : ConvexOn ℝ univ (ivp2_tiltFreeEnergy G q) :=
    ivp2_tiltFreeEnergy_convexOn G q hq hE
  have heq : cfe_centered G q
      = (fun t => ivp2_tiltFreeEnergy G q t + (- ivp2_tiltFreeEnergy G q 0)) := by
    funext t; unfold cfe_centered; ring
  rw [heq]
  exact hconv.add_const _

lemma cfe_centered_hasDerivAt (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (cfe_centered G 2) (fpd_avgDensity G t) t := by
  have hbase : HasDerivAt (ivp2_tiltFreeEnergy G 2) (fpd_avgDensity G t) t := by
    have h := fpd_tiltFreeEnergy_deriv_eq_avgDensity G hE t
    rwa [show (1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2
        (fun ω => (openCount G ω : ℝ)) = fpd_avgDensity G t from rfl] at h
  exact hbase.sub_const (ivp2_tiltFreeEnergy G 2 0)

lemma cfe_avgDensity_mem_Icc (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    0 ≤ fpd_avgDensity G t ∧ fpd_avgDensity G t ≤ 1 := by
  have hp0 : (0 : ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  set p := fsc_logistic t with hp
  have hEr : (0 : ℝ) < (G.edgeFinset.card : ℝ) := by exact_mod_cast hE
  have hsum1 : ∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω = 1 :=
    fkProb_sum_eq_one G hp0 hp1 (by norm_num)
  have hnn : 0 ≤ fkExpect G p 2 (fun ω => (openCount G ω : ℝ)) := by
    unfold fkExpect
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (fkProb_nonneg G hp0 hp1 (by norm_num) ω) (by positivity)
  have hle : fkExpect G p 2 (fun ω => (openCount G ω : ℝ)) ≤ (G.edgeFinset.card : ℝ) := by
    unfold fkExpect
    calc ∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω * (openCount G ω : ℝ)
        ≤ ∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω * (G.edgeFinset.card : ℝ) := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_left _ (fkProb_nonneg G hp0 hp1 (by norm_num) ω)
          have : openCount G ω ≤ G.edgeFinset.card := by
            unfold openCount; exact Finset.card_filter_le _ _
          exact_mod_cast this
      _ = (∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω) * (G.edgeFinset.card : ℝ) := by
          rw [← Finset.sum_mul]
      _ = (G.edgeFinset.card : ℝ) := by rw [hsum1, one_mul]
  refine ⟨?_, ?_⟩
  · unfold fpd_avgDensity; positivity
  · unfold fpd_avgDensity
    rw [div_mul_eq_mul_div, one_mul, div_le_one hEr]
    exact hle

lemma cfe_centered_monotone (hE : 0 < G.edgeFinset.card) :
    Monotone (cfe_centered G 2) :=
  monotone_of_hasDerivAt_nonneg (fun x => cfe_centered_hasDerivAt G hE x)
    (fun x => (cfe_avgDensity_mem_Icc G hE x).1)

lemma cfe_id_sub_centered_monotone (hE : 0 < G.edgeFinset.card) :
    Monotone (fun t => t - cfe_centered G 2 t) := by
  refine monotone_of_hasDerivAt_nonneg
    (f' := fun x => 1 - fpd_avgDensity G x) (fun x => ?_) (fun x => ?_)
  · exact (hasDerivAt_id x).sub (cfe_centered_hasDerivAt G hE x)
  · have := (cfe_avgDensity_mem_Icc G hE x).2
    change (0 : ℝ) ≤ 1 - fpd_avgDensity G x
    linarith

lemma cfe_centered_abs_le (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    |cfe_centered G 2 t| ≤ |t| := by
  have hmono := cfe_centered_monotone G hE
  have hmono2 := cfe_id_sub_centered_monotone G hE
  have h0 : cfe_centered G 2 0 = 0 := cfe_centered_zero G 2
  rcases le_or_gt 0 t with ht | ht
  · have hge : 0 ≤ cfe_centered G 2 t := by
      have := hmono ht; rw [h0] at this; exact this
    have hle : cfe_centered G 2 t ≤ t := by
      have := hmono2 ht; simp only at this; rw [h0] at this; linarith
    rw [abs_of_nonneg hge, abs_of_nonneg ht]; exact hle
  · have hle : cfe_centered G 2 t ≤ 0 := by
      have := hmono ht.le; rw [h0] at this; exact this
    have hge : t ≤ cfe_centered G 2 t := by
      have := hmono2 ht.le; simp only at this; rw [h0] at this; linarith
    rw [abs_of_nonpos hle, abs_of_nonpos ht.le]; linarith

section Wired

variable (bdry : V → Prop) [DecidablePred bdry]

/-! ## B. Wired centered free energies -/

/-- The wired tilt free energy of `G` with boundary `bdry`, centered at `t = 0`. -/
noncomputable def cfe_wiredCentered (q : ℝ) (t : ℝ) : ℝ :=
  wpd_wiredTiltFreeEnergy G bdry q t - wpd_wiredTiltFreeEnergy G bdry q 0

@[simp] lemma cfe_wiredCentered_zero (q : ℝ) : cfe_wiredCentered G bdry q 0 = 0 := by
  unfold cfe_wiredCentered; ring

lemma cfe_wiredCentered_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (cfe_wiredCentered G bdry q) := by
  have hconv : ConvexOn ℝ univ (wpd_wiredTiltFreeEnergy G bdry q) :=
    wpd_wiredTiltFreeEnergy_convexOn G bdry q hq hE
  have heq : cfe_wiredCentered G bdry q
      = (fun t => wpd_wiredTiltFreeEnergy G bdry q t + (- wpd_wiredTiltFreeEnergy G bdry q 0)) := by
    funext t; unfold cfe_wiredCentered; ring
  rw [heq]; exact hconv.add_const _

lemma cfe_wiredCentered_hasDerivAt (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (cfe_wiredCentered G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t := by
  have hbase : HasDerivAt (wpd_wiredTiltFreeEnergy G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t
      := by
    have h := wpd_wiredTiltFreeEnergy_hasDerivAt G bdry 2 (by norm_num) hE t
    rwa [show (1 / (G.edgeFinset.card : ℝ))
        * wpd_wiredFkExpect G bdry (fsc_logistic t) 2 (fun ω => (openCount G ω : ℝ))
        = wpd_avgWiredDensity G bdry 2 t from rfl] at h
  exact hbase.sub_const (wpd_wiredTiltFreeEnergy G bdry 2 0)

end Wired

variable {d : ℕ}

/-! ## C. Convergence along boxes -/

/-- The centered free energies of the boxes `Λ_n` converge pointwise to `G`, and `G(0) = 0`. -/
def cfe_CenteredConvergence (d : ℕ) (G : ℝ → ℝ) : Prop :=
  (∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) ∧ G 0 = 0

/-! ## D. Uniqueness -/

lemma cfe_centeredConvergence_satisfiable :
    ∃ (gn : ℕ → ℝ → ℝ) (G : ℝ → ℝ),
      (∀ t, Tendsto (fun n => gn n t) atTop (𝓝 (G t))) ∧ G 0 = 0 ∧ ConvexOn ℝ univ G := by
  refine ⟨fun _ _ => 0, fun _ => 0, fun t => tendsto_const_nhds, rfl, ?_⟩
  exact convexOn_const 0 convex_univ

end FK

end StatMech
