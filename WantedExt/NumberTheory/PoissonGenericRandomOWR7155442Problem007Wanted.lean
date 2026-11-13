/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Computable and random Poisson generic sequences (Oberwolfach Reports 21/2021)

Oberwolfach workshop Computability Theory (2021), open problems, V. Becher: (1) Is there a
computable Poisson generic real? (2) Are all Martin-Löf random reals Poisson generic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure

@[expose] public section

namespace MathlibExt.NumberTheory.PoissonGenericRandomOWR7155442Problem007Wanted

/-!
Source: V. Becher, open problems session, in Computability Theory, Oberwolfach Reports 18 (2021),
no. 21, pp. 1178-1179, questions (1) and (2), DOI 10.4171/OWR/2021/21. UnsolvedMath record
UM-30004673 (`OWR-7155442-007`), dataset ulamai/UnsolvedMath v1.8.0.

Reals are identified with their binary expansions `x : ℕ → Bool`, as in the source. Poisson
genericity is Rudnick's definition in the precise form of Álvarez-Becher-Mereb, Definition 1 (base
`2`): the occurrences of a word of length `n` are counted at the first `⌊λ 2^n⌋` starting positions.
A sequence is computable when `n ↦ x n` is `Computable`. A Martin-Löf test is a uniformly computably
enumerable sequence of sets of strings `U m` whose generated open sets have fair-coin measure at
most `2⁻ᵐ`; `x` is Martin-Löf random when it avoids some level of every test. Question (3) (a
Kolmogorov-complexity characterization) is open-ended and question (4) (`Π⁰₃`-completeness, answered
by Becher-Jackson-Kwietniak-Mance, arXiv:2305.10529) needs the Borel hierarchy and Wadge reductions;
neither is formalized.
-/

open MeasureTheory Filter Topology

/-- The number of occurrences of the word `w` of length `n` in the binary sequence `x` starting at
one of the first `N` positions: the `i < N` with `x (i + j) = w j` for every `j < n` (occurrences
inside `x 0, …, x (N + n - 2)`, as in Álvarez-Becher-Mereb, Definition 1). -/
def occurrences (x : ℕ → Bool) (N n : ℕ) (w : Fin n → Bool) : ℕ :=
  ((Finset.range N).filter fun i => ∀ j : Fin n, x (i + j) = w j).card

/-- Rudnick's Poisson genericity (Oberwolfach Report 21/2021, p. 1178; Álvarez-Becher-Mereb,
Definition 1, base `2`): for every real `λ > 0` and every `k ≥ 0`, the proportion of the `2^n`
binary words of length `n` that occur exactly `k` times at the first `⌊λ 2^n⌋` starting positions of
`x` tends to `e^{-λ} λ^k / k!` as `n → ∞`. -/
def IsPoissonGeneric (x : ℕ → Bool) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ k : ℕ,
    Tendsto (fun n : ℕ =>
        ((Finset.univ.filter fun w : Fin n → Bool =>
            occurrences x ⌊lam * 2 ^ n⌋₊ n w = k).card : ℝ) / 2 ^ n)
      atTop (𝓝 (Real.exp (-lam) * lam ^ k / k.factorial))

/-- The string `σ` is a prefix of the sequence `x`. -/
def IsPrefix (σ : List Bool) (x : ℕ → Bool) : Prop :=
  ∀ (i : ℕ) (h : i < σ.length), σ[i] = x i

/-- The uniform (fair-coin) product measure on binary sequences. -/
noncomputable def coinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ =>
    ProbabilityTheory.bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

/-- A Martin-Löf test: a uniformly computably enumerable sequence `U 0, U 1, …` of sets of strings
such that the set of sequences with a prefix in `U m` has measure at most `2⁻ᵐ`. -/
def IsMartinLofTest (U : ℕ → Set (List Bool)) : Prop :=
  REPred (fun p : ℕ × List Bool => p.2 ∈ U p.1) ∧
    ∀ m : ℕ, coinMeasure {x | ∃ σ ∈ U m, IsPrefix σ x} ≤ (2⁻¹ : ENNReal) ^ m

/-- `x` is Martin-Löf random: it passes every Martin-Löf test, i.e. for every test `U` some level
`U m` contains no prefix of `x`. -/
def IsMartinLofRandom (x : ℕ → Bool) : Prop :=
  ∀ U : ℕ → Set (List Bool), IsMartinLofTest U → ∃ m, ∀ σ ∈ U m, ¬ IsPrefix σ x

/-- Becher's question (1) (Oberwolfach Report 21/2021, p. 1179): there is a computable Poisson
generic binary sequence. -/
def computablePoissonGenericExists : Prop :=
  ∃ x : ℕ → Bool, Computable x ∧ IsPoissonGeneric x

/-- Becher's question (2) (Oberwolfach Report 21/2021, p. 1179): every Martin-Löf random binary
sequence is Poisson generic. -/
def martinLofRandomIsPoissonGeneric : Prop :=
  ∀ x : ℕ → Bool, IsMartinLofRandom x → IsPoissonGeneric x

/--
Resolved true: Álvarez, Becher and Mereb (Theorem 2) construct computable Poisson generic sequences
(countably many) over every finite alphabet, in particular binary ones. Source: V. Becher, open
problems session, in Computability Theory, Oberwolfach Reports 18 (2021), no. 21, pp. 1178-1179,
questions (1) and (2), DOI 10.4171/OWR/2021/21; resolution: N. Álvarez, V. Becher and M. Mereb,
Poisson generic sequences, Int. Math. Res. Not. IMRN 2023, no. 24, 20970-20987, DOI
10.1093/imrn/rnac234, arXiv:2202.01632, Theorem 2: there are countably many computable Poisson
generic elements of Ω^ℕ; Theorem 3: all Martin-Löf random elements of Ω^ℕ are Poisson generic (Ω an
alphabet of b ≥ 2 symbols, Poisson genericity as in Definition 1), https://arxiv.org/abs/2202.01632.
-/
public theorem_wanted computablePoissonGenericExists_holds : computablePoissonGenericExists

/--
Resolved true: Álvarez, Becher and Mereb (Theorem 3) prove that every Martin-Löf random sequence
over a finite alphabet is Poisson generic, in particular every binary one. Source: V. Becher, open
problems session, in Computability Theory, Oberwolfach Reports 18 (2021), no. 21, pp. 1178-1179,
questions (1) and (2), DOI 10.4171/OWR/2021/21; resolution: N. Álvarez, V. Becher and M. Mereb,
Poisson generic sequences, Int. Math. Res. Not. IMRN 2023, no. 24, 20970-20987, DOI
10.1093/imrn/rnac234, arXiv:2202.01632, Theorem 2: there are countably many computable Poisson
generic elements of Ω^ℕ; Theorem 3: all Martin-Löf random elements of Ω^ℕ are Poisson generic (Ω an
alphabet of b ≥ 2 symbols, Poisson genericity as in Definition 1), https://arxiv.org/abs/2202.01632.
-/
public theorem_wanted martinLofRandomIsPoissonGeneric_holds : martinLofRandomIsPoissonGeneric

end MathlibExt.NumberTheory.PoissonGenericRandomOWR7155442Problem007Wanted
