/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.TildePc
public import PhyslibExt.CondensedMatter.IsingModel.GKS

/-!
# The Duminil-Copin–Tassion point for the Ising model

The quantity `φ_β(S) = tanh β ∑_{(x,y) ∈ ∂S} ⟨σ_0σ_x⟩_S` and the auxiliary critical point `β̃_c`,
for percolation and for the Ising model on `ℤ^d`.

## i. Overview

For a finite set `S ∋ 0`, `⟨·⟩_S` is the free-boundary Ising measure on the subgraph of `ℤ^d`
induced by `S` at zero field. The Ising version of the Duminil-Copin–Tassion quantity is `φ_β(S) =
tanh β ∑_{(x,y) ∈ ∂S} ⟨σ_0σ_x⟩_S`, and `β̃_c = sup {β ≥ 0 | ∃ S ∋ 0, φ_β(S) < 1}`. The percolation
analogue uses the edge parameter `1 - e^{-β}`.

## ii. Key results

- `freeCorr` : free-boundary two-point function in `S`
- `phiIsing` : the quantity `φ_β(S)`
- `tildeBetaCIsing` : the auxiliary critical point `β̃_c`

## iii. Table of contents

- A. The percolation version
- B. Free-boundary correlations in a finite set
- C. The Ising version of `φ` and `β̃_c`

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal
open Finset

namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}

/-! ## A. The percolation version -/

/-- The bond parameter `1 - exp(-β)` as an element of `ℝ≥0`. -/
noncomputable def bondParam (β : ℝ) : ℝ≥0 := Real.toNNReal (1 - Real.exp (-β))

lemma bondParam_le_one (β : ℝ) : bondParam β ≤ 1 := by
  unfold bondParam
  rw [Real.toNNReal_le_one]
  have h1 : (0 : ℝ) < Real.exp (-β) := Real.exp_pos _
  linarith

/-- The percolation quantity `φ_p(S)` at `p = 1 - exp(-β)`. -/
noncomputable def phiBeta (d : ℕ) (β : ℝ) (S : Finset (Site d)) : ℝ :=
  Percolation.phi d (bondParam β) (bondParam_le_one β) S

lemma phiBeta_nonneg (d : ℕ) (β : ℝ) (S : Finset (Site d)) :
    0 ≤ phiBeta d β S :=
  Percolation.phi_nonneg d (bondParam β) (bondParam_le_one β) S

/-- Inverse temperatures `β ≥ 0` with a finite `S ∋ 0` such that `φ_{1-e^{-β}}(S) < 1`. -/
def tildeBetaCPercoSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d β S < 1}

@[simp]
lemma mem_tildeBetaCPercoSet {d : ℕ} {β : ℝ} :
    β ∈ tildeBetaCPercoSet d ↔
      0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d β S < 1 :=
  Iff.rfl

/-- The percolation auxiliary critical point on the `β` scale, the supremum of `tildeBetaCPercoSet`.
-/
noncomputable def tildeBetaCPerco (d : ℕ) : ℝ :=
  sSup (tildeBetaCPercoSet d)

/-! ## B. Free-boundary correlations in a finite set -/

/-- The subgraph of `ℤ^d` induced by a finite set `S`, on the vertex type `S`. -/
noncomputable def graphS (d : ℕ) (S : Finset (Site d)) : SimpleGraph {v // v ∈ S} :=
  (hypercubicLattice d).comap (fun v : {v // v ∈ S} => (v : Site d))

/-- Decidability of adjacency in `graphS`. -/
noncomputable instance instDecidableAdjGraphS (d : ℕ) (S : Finset (Site d)) :
    DecidableRel (graphS d S).Adj := by
  classical
  intro a b
  unfold graphS
  simp only [SimpleGraph.comap_adj]
  infer_instance

/-- The free-boundary zero-field two-point function `⟨σ_aσ_b⟩_S` in the induced graph on `S` (equal
to `1` when `a = b`). -/
noncomputable def freeCorr (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : ℝ :=
  if a = b then 1 else
    isingExpectation (graphS d S) β 0 (spinProd {a, b})

@[simp]
lemma freeCorr_self (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a : {v // v ∈ S}) : freeCorr d β S a a = 1 := by
  simp [freeCorr]

lemma abs_freeCorr_le_one (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : |freeCorr d β S a b| ≤ 1 := by
  classical
  by_cases hab : a = b
  · simp [freeCorr, hab]
  rw [freeCorr, ite_eq_right hab]
  unfold isingExpectation
  have hbound : ∀ s : ConfigSpace {v // v ∈ S}, |spinProd ({a, b} : Finset _) s| ≤ 1 := by
    intro s
    unfold spinProd
    rw [Finset.abs_prod]
    apply Finset.prod_le_one₀
    · intro x _; positivity
    · intro x _; exact abs_spin_le_one s x
  calc |∑ s : ConfigSpace {v // v ∈ S},
            isingProb (graphS d S) β 0 s * spinProd ({a, b} : Finset _) s|
      ≤ ∑ s : ConfigSpace {v // v ∈ S},
            |isingProb (graphS d S) β 0 s * spinProd ({a, b} : Finset _) s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : ConfigSpace {v // v ∈ S}, isingProb (graphS d S) β 0 s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul, abs_of_nonneg (isingProb_nonneg (graphS d S) β 0 s)]
        exact mul_le_mul_of_nonneg_left (hbound s) (isingProb_nonneg (graphS d S) β 0 s)
    _ = ∑ s : ConfigSpace {v // v ∈ S}, isingProb (graphS d S) β 0 s := by simp
    _ = 1 := isingProb_sum_eq_one (graphS d S) β 0

lemma freeCorr_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : 0 ≤ freeCorr d β S a b := by
  by_cases hab : a = b
  · simp [freeCorr, hab]
  rw [freeCorr, ite_eq_right hab]
  exact gks_first (graphS d S) β 0 hβ le_rfl {a, b}

/-- The function `x ↦ ⟨σ_0σ_x⟩_S`, extended by `0` outside `S` (and identically `0` if `0 ∉ S`). -/
noncomputable def corrOriginInner (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (x : Site d) : ℝ := by
  classical
  exact
    if h0 : origin d ∈ S then
      if hx : x ∈ S then
        freeCorr d β S ⟨origin d, h0⟩ ⟨x, hx⟩
      else 0
    else 0

lemma corrOriginInner_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d))
    (x : Site d) : 0 ≤ corrOriginInner d β S x := by
  classical
  unfold corrOriginInner
  split
  · split
    · exact freeCorr_nonneg d hβ S _ _
    · exact le_refl 0
  · exact le_refl 0

/-! ## C. The Ising version of `φ` and `β̃_c` -/

/-- The Duminil-Copin–Tassion quantity `φ_β(S) = tanh β ∑_{(x,y) ∈ ∂S} ⟨σ_0σ_x⟩_S`. -/
noncomputable def phiIsing (d : ℕ) (β : ℝ) (S : Finset (Site d)) : ℝ :=
  Real.tanh β * ∑ e ∈ Percolation.boundaryEdges d S, corrOriginInner d β S e.1

lemma phiIsing_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d)) :
    0 ≤ phiIsing d β S := by
  unfold phiIsing
  refine mul_nonneg ?_ (Finset.sum_nonneg ?_)
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos _).le
  · intro e _
    exact corrOriginInner_nonneg d hβ S e.1

/-- Inverse temperatures `β ≥ 0` with a finite `S ∋ 0` such that `φ_β(S) < 1`. -/
def tildeBetaCIsingSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiIsing d β S < 1}

@[simp]
lemma mem_tildeBetaCIsingSet {d : ℕ} {β : ℝ} :
    β ∈ tildeBetaCIsingSet d ↔
      0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiIsing d β S < 1 :=
  Iff.rfl

/-- The auxiliary critical point `β̃_c(d) = sup {β ≥ 0 | ∃ S ∋ 0, φ_β(S) < 1}`. -/
noncomputable def tildeBetaCIsing (d : ℕ) : ℝ :=
  sSup (tildeBetaCIsingSet d)

end Sharpness

end StatMech
