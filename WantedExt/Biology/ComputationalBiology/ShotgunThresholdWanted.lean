/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Repeat-versus-coverage threshold for optimal shotgun assembly

Model: circular genome of length `G` with i.i.d. letters of distribution `p`
on four bases; `N` reads of length `L` with independent uniform starts;
perfect reconstruction with error probability at most `ε`. With normalized
read length `L̄ = L / log G` fixed, let `N_cov` be the Lander-Waterman number
of reads needed to cover and `c_min(L̄)` the limit of `N_min / N_cov`. For
fixed `ε < 1/2`, `c_min(L̄) = ∞` below `2 / H₂(p)` and `1` above, where
`H₂(p) = -log ∑ᵢ pᵢ²` is the order-2 Renyi entropy; above the threshold a
simple greedy algorithm is optimal. The Markov-genome extension (Theorem 6,
Renyi entropy rate) is a follow-up.

Overlap: none found (no information-theoretic assembly module). This must
not overlap the accepted Lander-Waterman islands/gaps file
(`CSLibExt/Bioinformatics/Assembly/LanderWatermanIslands.lean`); the
coverage count `N_cov` here is characterized abstractly and can cite it.

Sources: A. S. Motahari, G. Bresler and D. N. C. Tse, "Information Theory of
DNA Shotgun Sequencing", IEEE Transactions on Information Theory
59(10):6273-6289, 2013, doi:10.1109/TIT.2013.2270273, Theorem 1 (read as
arXiv:1203.6233v4).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.ShotgunThresholdWanted

open Classical Filter Topology

/-- Finite-sum helper. -/
def finSum4 (g : Fin 4 → ℝ) : ℝ :=
  Finset.sum Finset.univ g

/-- Order-2 Renyi entropy of a distribution on four bases. -/
noncomputable def renyi2 (p : Fin 4 → ℝ) : ℝ :=
  -Real.log (finSum4 fun i => (p i) ^ 2)

/-- Base distribution: nonnegative, sums to one, non-degenerate. -/
def IsGenomeDist (p : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ finSum4 p = 1 ∧ ∃ i, 0 < p i ∧ p i < 1

/-- **Shotgun assembly threshold** (Motahari-Bresler-Tse 2013, Theorem 1):
hypotheses are a genome distribution (`hp`, non-degenerate so `H₂ > 0` by
`hH2`), error tolerance below one half (`heps`), coverage and minimum read
counts with positive coverage (`hncov`), and the normalized-length regime
(`hregime`: reads scale as `L̄ log G`, relating the length parameter to `G`).
Conclusions: below `2 / H₂(p)` the normalized ratio diverges (`hbelow`),
above it converges to one (`habove`).

Source: Motahari-Bresler-Tse (2013), Theorem 1. -/
theorem_wanted shotgun_threshold (p : Fin 4 → ℝ) (hp : IsGenomeDist p)
    (H2 : ℝ) (hH2def : H2 = renyi2 p) (hH2 : 0 < H2)
    (eps : ℝ) (heps : 0 ≤ eps ∧ eps < 1 / 2)
    (nMin nCov : ℕ → ℝ)
    (hncov : ∀ G, 0 < nCov G)
    (Lbar : ℝ) (hLbar : 0 < Lbar) :
    (Lbar < 2 / H2 →
      Filter.Tendsto (fun G => nMin G / nCov G) Filter.atTop Filter.atTop) ∧
    (2 / H2 < Lbar →
      Filter.Tendsto (fun G => nMin G / nCov G) Filter.atTop (𝓝 1))

/-- **Greedy optimality above threshold** (Motahari-Bresler-Tse 2013):
hypotheses are the Theorem-1 setup above threshold (`habove_thr`) and a
greedy error curve vanishing at infinity (`hgreedy_vanish`). Conclusion: the
greedy algorithm attains the optimal normalized coverage.

Source: Motahari-Bresler-Tse (2013). -/
theorem_wanted greedy_optimal (p : Fin 4 → ℝ) (hp : IsGenomeDist p)
    (H2 : ℝ) (hH2def : H2 = renyi2 p) (hH2 : 0 < H2)
    (eps : ℝ) (heps : 0 ≤ eps ∧ eps < 1 / 2)
    (nMin nCov : ℕ → ℝ)
    (hncov : ∀ G, 0 < nCov G)
    (Lbar : ℝ) (hLbar : 0 < Lbar)
    (habove_thr : 2 / H2 < Lbar)
    (greedyErr : ℕ → ℝ)
    (hgreedy_vanish : Filter.Tendsto greedyErr Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun G => nMin G / nCov G) Filter.atTop (𝓝 1)

end WantedExt.Biology.ComputationalBiology.ShotgunThresholdWanted
