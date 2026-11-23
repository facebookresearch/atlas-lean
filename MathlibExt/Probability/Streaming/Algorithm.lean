/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Randomized one-pass streaming algorithms with bounded memory

A randomized streaming algorithm over an alphabet `α` with `s` bits of memory reads a stream
`a₁, …, a_m` once, keeping only a state in `Fin (2 ^ s)`, and outputs a real number at the end.
Its randomness is a seed `r` drawn uniformly from a finite nonempty set `R` and visible at every
step. This is the model of N. Alon, Y. Matias and M. Szegedy, "The space complexity of
approximating the frequency moments", J. Comput. System Sci. 58 (1999) 137–147, Section 1, with
one difference: the seed is not charged to the memory. This is the standard public-randomness
(random-oracle) streaming model. Every algorithm of the source's model, whose random bits are
stored in memory or drawn during the pass, is an algorithm of this model with the same memory,
so a space lower bound proved here is at least as strong as the source's.

The free seed does not weaken the source's lower bounds (`space_lower_bound_maxFreq`,
`space_lower_bound_freqMoment`), because their proofs turn the seed into the public coin of a
communication protocol, and the communication bounds hold against arbitrary public randomness:

- Proposition 3.1: Alice and Bob share the seed `r` as a public coin. Alice runs the algorithm
  on the elements of `x` and sends the `s`-bit memory content, and Bob finishes the run on `y`.
  This is a one-way public-coin protocol for disjointness of cost `s + O(1)`, and the
  public-coin bound `randComplexity_disjFn_ge` applies.
- Theorem 3.2: Proposition 3.3 is proved distributionally ("it suffices to exhibit a
  distribution on the inputs and prove that any deterministic communication protocol … errs
  with probability `Ω(1)`"). Amplify the algorithm by independent copies (seed space `R^k`,
  memory `k s` bits, still an algorithm of this model), average the error over the input
  distribution, and fix one seed. The result is a deterministic state-passing protocol with
  small distributional error, so the size of the seed space never enters.

## Main definitions

- `StreamingAlgorithm α R s`: initial state, transition and output, each depending on the seed.
- `StreamingAlgorithm.output`: the output after reading a stream.
- `StreamingAlgorithm.failProb`: the fraction of seeds whose output violates a correctness
  predicate, for a nonempty seed space (for an empty one every failure probability would be
  `0`).
- `maxFreq`, `freqMoment`: `F*_∞` and `F_k` of a stream over `Fin n`, with `mᵢ = l.count i`.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.Streaming

/-- **Randomized streaming algorithm with `s` bits of memory.** A one-pass algorithm over the
alphabet `α` whose state is one of `2 ^ s` memory contents, given by an initial state, a
transition reading one stream element, and a real output, all depending on a random seed in `R`
(N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), Section 1). The seed is not
counted in the memory (the public-randomness model). The source's algorithms are special cases,
and the source's lower-bound proofs use the seed only as a public coin, as explained in the module
documentation. -/
structure StreamingAlgorithm (α R : Type*) (s : ℕ) where
  /-- The initial memory content for each seed. -/
  init : R → Fin (2 ^ s)
  /-- The new memory content after reading one element. -/
  step : R → Fin (2 ^ s) → α → Fin (2 ^ s)
  /-- The output computed from the final memory content. -/
  out : R → Fin (2 ^ s) → ℝ

namespace StreamingAlgorithm

variable {α R : Type*} {s : ℕ}

/-- **Output of a streaming algorithm.** The output of `A` with seed `r` after reading the stream
`l` from left to right. -/
def output (A : StreamingAlgorithm α R s) (r : R) (l : List α) : ℝ :=
  A.out r (l.foldl (A.step r) (A.init r))

open Classical in
/-- **Failure probability of a streaming algorithm.** For a correctness predicate `ok l y`
("output `y` is acceptable on the stream `l`"), the fraction of seeds `r ∈ R` for which the output
of `A` on `l` is not acceptable, the seed being uniform on the finite nonempty set `R`. For an
empty `R`, which is excluded, the fraction would be `0 / 0 = 0` for every predicate. -/
noncomputable def failProb [Fintype R] [Nonempty R] (A : StreamingAlgorithm α R s)
    (ok : List α → ℝ → Prop) (l : List α) : ℝ :=
  ((univ.filter fun r => ¬ ok l (A.output r l)).card : ℝ) / Fintype.card R

end StreamingAlgorithm

/-- **Largest multiplicity of a stream.** `F*_∞ = maxᵢ mᵢ`, where `mᵢ = l.count i`, for a stream
over `Fin n` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), Section 1).
It is `0` for the empty stream. -/
def maxFreq {n : ℕ} (l : List (Fin n)) : ℕ := univ.sup fun i => l.count i

/-- **Frequency moment of a stream.** `F_k = ∑ᵢ mᵢ ^ k` for a stream over `Fin n` (N. Alon,
Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), Section 1). This agrees with the
source for `k ≥ 1`. For `k = 0`, Lean's convention `0 ^ 0 = 1` makes it `n`, whereas the source's
`F₀` is the number of distinct elements of the stream. -/
def freqMoment {n : ℕ} (k : ℕ) (l : List (Fin n)) : ℕ := ∑ i, l.count i ^ k

end MathlibExt.Probability.Streaming
