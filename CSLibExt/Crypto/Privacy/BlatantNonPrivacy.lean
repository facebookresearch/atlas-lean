/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.InformationTheory.Hamming
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Distortion and blatant non-privacy

The lower bounds on the noise needed for privacy take a database of one sensitive bit per
person, `d : Fin n → Bool`, and subset-sum queries: a query is a set of rows `q ⊆ [n]`, and its
exact answer `a_q(d) = ∑_{i ∈ q} d_i` is the number of selected rows whose bit is `1` (Dwork and
Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Section 8.1; Dinur and
Nissim, *PODS* 2003, Definition 1).

* `subsetSumQuery`: the exact answer `a_q(d)`.
* `HasDistortion`: answers to the subset-sum queries on `d` have distortion at most `E` when every
  answer is within `E` of the exact one.
* `BlatantlyNonPrivate`: from a mechanism's random output, an adversary reconstructs the database
  in all but `o(n)` entries, except with negligible probability (Dwork and Roth, Definition 8.1;
  Dinur and Nissim, Definition 3).

A mechanism is randomized: its answers may depend on its random choices (Dwork and Roth,
Section 8.1), so `BlatantlyNonPrivate` takes the law of its output on each database, and the
adversary sees the whole output. A mechanism whose answers also depend on the history of queries
enters through a chosen output, such as its answers to a fixed set of queries asked at once, as
in the non-adaptive attacks of Dinur and Nissim (Remark 1). `HasDistortion` is a property of one
table of answers, and a mechanism whose answers are always within `E` of the exact ones gives
such a table with probability one. Definition 8.1 does not say with what probability the
adversary must succeed; `BlatantlyNonPrivate` asks for success with probability `1 - neg(n)` for
every `ε > 0`, as Dinur and Nissim's Definition 3 does, without their bound on the adversary's
running time, which Definition 8.1 does not impose. Negligibility is Mathlib's
`Asymptotics.SuperpolynomialDecay`, which for these nonnegative probabilities agrees with
`Cslib.Crypto.Framework.NegligibleAdv` by
`Cslib.Crypto.Framework.negligibleAdv_iff_superpolynomialDecay`. The adversary is a map from
outputs to candidates, with no coin tosses of its own.
-/

@[expose] public section

open Asymptotics Filter MeasureTheory

namespace Cslib.Crypto.Privacy

variable {n : ℕ}

/-- **Subset-sum query.** For a database of `n` bits `d : Fin n → Bool`, with `true` read as `1`,
and a set of rows `q ⊆ [n]`, the subset-sum query has the exact answer `a_q(d) = ∑_{i ∈ q} d_i`,
the number of rows in `q` whose bit is `1` (Dinur and Nissim, *PODS* 2003, Definition 1; Dwork and
Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Section 8.1, where `q` is given
by its characteristic vector `S` and the answer is `A(S) = ∑ᵢ dᵢ Sᵢ`). -/
def subsetSumQuery (d : Fin n → Bool) (q : Finset (Fin n)) : ℕ :=
  ∑ i ∈ q, (d i).toNat

/-- **Distortion.** Answers `r : Finset (Fin n) → ℝ` to the subset-sum queries on a database
`d : Fin n → Bool` have distortion at most `E` if every answer is within `E` of the exact answer:
`|r q - a_q(d)| ≤ E` for every `q ⊆ [n]` (Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy*, 2014, Section 8.1, the distortion `E(S, r(S)) = |A(S) - r(S)|` bounded by
`E` as in Theorem 8.1; Dinur and Nissim, *PODS* 2003, Definition 2, "within `E`
perturbation"). -/
def HasDistortion (d : Fin n → Bool) (r : Finset (Fin n) → ℝ) (E : ℝ) : Prop :=
  ∀ q, |r q - subsetSumQuery d q| ≤ E

/-- **Blatant non-privacy.** A mechanism releases, for every `n` and every database
`d : Fin n → Bool`, a random output with law `M n d`, such as its answers to all subset-sum
queries. It is blatantly non-private if an adversary can construct from the output a candidate
that agrees with the database in all but `o(n)` entries, except with negligible probability:
there are maps `A n` from outputs to candidates `c : Fin n → Bool` such that, for every choice of
databases `d n : Fin n → Bool` and every `ε > 0`, the probability that the candidate `A n ω`
built from the output `ω` on `d n` differs from `d n` in more than `ε n` entries decays faster
than every power of `n` (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*,
2014, Definition 8.1, `‖c - d‖₀ ∈ o(n)`; Dinur and Nissim, *PODS* 2003, Definition 3, success
with probability `1 - neg(n)` for every `ε > 0`, there for adversaries of bounded running time).
The adversary may depend on the mechanism but not on the database, and need not know on which
entries it is correct. The probability of an event that is not measurable is its outer
measure. -/
def BlatantlyNonPrivate {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (M : ∀ n, (Fin n → Bool) → ProbabilityMeasure (Ω n)) : Prop :=
  ∃ A : ∀ n, Ω n → Fin n → Bool, ∀ (d : ∀ n, Fin n → Bool) (ε : ℝ), 0 < ε →
    SuperpolynomialDecay atTop (fun n : ℕ ↦ (n : ℝ))
      fun n ↦ (M n (d n) {ω | ε * n < hammingDist (A n ω) (d n)} : ℝ)

end Cslib.Crypto.Privacy
