/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kingman's theorem for the ancestral lineage count

Trace `k` gene copies back one generation in a neutral Wright–Fisher population of `M` gene
copies (`M = 2N` for `N` diploid individuals): each copy picks its parent uniformly and
independently among the `M` copies of the previous generation, and the number of ancestral
lineages one generation back is the number `j` of distinct parents. Exactly
`Nat.stirlingSecond k j * M.descFactorial j` of the `M ^ k` parent assignments have `j` distinct
parents, so the one-generation transition probability is
`stirlingSecond k j * M^{(j)} / M ^ k` (`wfLineageProb`), and the lineage count is a Markov chain
on `{0, …, n}` with transition matrix `wfLineageMatrix n M`.

Kingman's theorem, restricted to the block-counting (lineage-count) process, says that with
time measured in units of `M` generations this chain converges to the pure-death process in
which `k` lineages become `k - 1` at rate `k.choose 2` (`blockCountingGenerator n`): after
`⌊t M⌋` generations the transition matrix converges entrywise to `exp (t • G)`. The one-entry
special case `j = k` (no coalescence) is proved in
`MathlibExt.Biology.PopulationGenetics.Coalescent.tendsto_noCoalProb_pow_floor`.

Tavaré (1984) computed the transition probabilities of the pure-death process: for
`1 ≤ j ≤ i`, `P(i → j in time t)` is `∑_{k=j}^{i} e^{-k(k-1)t/2} (2k-1) (-1)^{k-j}
j^{(k-1)} i_{(k)} / (j! (k-j)! i^{(k)})`, where `a^{(m)}` is the rising factorial
`Nat.ascFactorial a m` and `a_{(m)}` the falling factorial `Nat.descFactorial a m`
(`tavareProb`).

Sources: J. F. C. Kingman, "The coalescent", Stochastic Process. Appl. 13 (1982) 235–248;
J. F. C. Kingman, "On the genealogy of large populations", J. Appl. Probab. 19A (1982) 27–43;
S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population
genetics models", Theor. Popul. Biol. 26 (1984) 119–164; R. Durrett, *Probability
Models for DNA Sequence Evolution*, 2nd ed. (2008), ch. 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCountingWanted

open Filter Topology

/-- One-generation transition probability of the ancestral lineage count in a neutral
Wright–Fisher population of `M` gene copies: `k` lineages pick their parents uniformly and
independently among `M` copies, and `j` distinct parents occur with probability
`stirlingSecond k j * M.descFactorial j / M ^ k`. -/
noncomputable def wfLineageProb (M k j : ℕ) : ℝ :=
  (Nat.stirlingSecond k j : ℝ) * (M.descFactorial j : ℝ) / (M : ℝ) ^ k

/-- The one-generation transition matrix of the ancestral lineage count of a sample of at most
`n` gene copies in a Wright–Fisher population of `M` copies; row `k`, column `j` is
`wfLineageProb M k j`. -/
noncomputable def wfLineageMatrix (n M : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j => wfLineageProb M k j

/-- The rate matrix of Kingman's block-counting (pure-death) process on `{0, …, n}`: `k`
lineages become `k - 1` at rate `k.choose 2`, time in units of `M = 2N` generations. -/
noncomputable def blockCountingGenerator (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j =>
    if (j : ℕ) + 1 = k then ((k : ℕ).choose 2 : ℝ)
    else if j = k then -((k : ℕ).choose 2 : ℝ) else 0

/-- Tavaré's closed form for the probability that `i` lineages of Kingman's coalescent have
`j` ancestors `t` time units (`2N` generations each) earlier, for `1 ≤ j ≤ i`. -/
noncomputable def tavareProb (i j : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc j i,
    Real.exp (-((k : ℝ) * (k - 1) * t / 2)) * (2 * k - 1) * (-1) ^ (k - j) *
      (j.ascFactorial (k - 1) : ℝ) * (i.descFactorial k : ℝ) /
      ((j.factorial : ℝ) * ((k - j).factorial : ℝ) * (i.ascFactorial k : ℝ))

/-- **Kingman's theorem for the lineage count.** For `t ≥ 0`, the `⌊t M⌋`-generation transition
matrix of the Wright–Fisher ancestral lineage count converges, as the population size `M`
tends to infinity, to the transition matrix `exp (t • G)` of the pure-death process with rates
`k.choose 2`.

Source: Kingman (1982); Durrett (2008), ch. 1. -/
theorem_wanted tendsto_wfLineageMatrix_pow_floor (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => wfLineageMatrix n M ^ ⌊t * M⌋₊) atTop
      (𝓝 (NormedSpace.exp (t • blockCountingGenerator n)))

/-- **Tavaré's formula.** The transition probabilities of Kingman's block-counting process
from `i` to `j` lineages in time `t`, for `1 ≤ j ≤ i ≤ n`, are given by `tavareProb`.

Source: Tavaré (1984). -/
theorem_wanted exp_blockCountingGenerator_apply (n : ℕ) (t : ℝ) (i j : Fin (n + 1))
    (hj : 1 ≤ (j : ℕ)) (hji : j ≤ i) :
    NormedSpace.exp (t • blockCountingGenerator n) i j = tavareProb i j t

end MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCountingWanted
