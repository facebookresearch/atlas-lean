/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rademacher LIL constant
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.NumberTheory.RandomMultiplicativeFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.LiminfLimsup

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators
open MetaMathlibExt.RandomMultiplicativeFunction

namespace MathlibExt.NumberTheory.RademacherLILConstantWanted

/-! Source record `EP-520__2155`. -/

/-- **Partial sums of the Rademacher multiplicative function.** Given signs
$X_p(\omega) \in \{-1, 1\}$ indexed by the primes $p$ and a sample point $\omega$, and given
$N \in \mathbb{N}$, the partial sum $S_N(\omega)$ is the real number $\sum_{m=1}^{N} f_\omega(m)$,
where $f_\omega$ is the Rademacher multiplicative function of the signs $X_p(\omega)$:
$f_\omega(m) = \prod_{p \mid m} X_p(\omega)$ for squarefree $m$ and $f_\omega(m) = 0$ otherwise. -/
noncomputable def partialSum {Ω : Type*} (X : Nat.Primes → Ω → ℤˣ) (ω : Ω)
    (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ((rademacherFunction X ω m : ℤ) : ℝ)

/-- **Rademacher LIL constant conjecture.** The statement that there is a real constant $c > 0$
such that, for every probability space $(\Omega, \mu)$ and every family $(X_p)_p$ of independent,
measurable random signs indexed by the primes, each uniform on $\{-1, 1\}$, for $\mu$-almost
every $\omega$ the limit superior as $N \to \infty$ of $S_N(\omega) / \sqrt{N \log \log N}$
equals $c$. Here $S_N(\omega) = \sum_{m=1}^{N} f_\omega(m)$ is the partial sum of the Rademacher
random multiplicative function $f_\omega$, given by $f_\omega(m) = \prod_{p \mid m} X_p(\omega)$
for squarefree $m$ and $f_\omega(m) = 0$ otherwise.

This is the question asked in Erdős Problem 520. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Nat.Primes → Ω → ℤˣ),
    IsRademacherFamily μ X →
    ∀ᵐ ω ∂μ, Filter.limsup
      (fun N : ℕ => partialSum X ω N /
        Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) Filter.atTop = c

/--
**No iterated-logarithm constant for Rademacher multiplicative functions.** The Rademacher
LIL constant conjecture is false: there is no real constant $c > 0$ such that, for every
probability space $(\Omega, \mu)$ and every family $(X_p)_p$ of independent, measurable random
signs indexed by the primes, each uniform on $\{-1, 1\}$, for $\mu$-almost every $\omega$ the
limit superior as $N \to \infty$ of $S_N(\omega) / \sqrt{N \log \log N}$ equals $c$. Here
$S_N(\omega) = \sum_{m=1}^{N} f_\omega(m)$, where $f_\omega$ is the Rademacher random
multiplicative function: $f_\omega(m) = \prod_{p \mid m} X_p(\omega)$ for squarefree $m$ and
$f_\omega(m) = 0$ otherwise.

Durkan and Pearce-Crump, and independently Verreault, proved that for every $\varepsilon > 0$,
almost surely $|\sum_{n \le x} f_\omega(n)| \ll \sqrt{x} (\log \log x)^{1/4 + \varepsilon}$ as
$x \to \infty$, so the normalized limit superior is almost surely $0$.

Source: B. Durkan, A. Pearce-Crump, A sharp almost sure upper bound for partial sums of
random multiplicative functions, arXiv preprint (2026), arXiv:2607.29429,
https://arxiv.org/abs/2607.29429; W. Verreault, Almost sure upper bound for sums of random
multiplicative functions and critical chaos, arXiv preprint (2026), arXiv:2608.21354,
https://arxiv.org/abs/2608.21354. Moved from
`OpenConjectures/NumberTheory/RademacherLILConstant`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.RademacherLILConstantWanted
