/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted

open MeasureTheory

/-- **Lebesgue measure on the unit interval (Scottish Book Problem 86).** Lebesgue measure on
$\mathbb{R}$ restricted to the unit interval $[0, 1]$, the ambient measure for Problem 86. -/
noncomputable def scottishBook86Measure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/-- **Scottish Book Problem 86 (Banach).** The claim that for every real $M > 0$ and every
sequence $(\varphi_n)_{n \in \mathbb{N}}$ of functions $\mathbb{R} \to \mathbb{R}$ that are
almost everywhere measurable on $[0, 1]$, orthonormal in $L^2[0, 1]$ (that is,
$\int_0^1 \varphi_n \varphi_m \, dt$ is $1$ if $n = m$ and $0$ otherwise) and satisfy
$|\varphi_n(t)| \le M$ for all $n$ and all $t \in [0, 1]$, there is a sequence
$(\psi_n)_{n \in \mathbb{N}}$ of functions $\mathbb{R} \to \mathbb{R}$, almost everywhere
measurable on $[0, 1]$, orthonormal in the same sense and with $|\psi_n(t)| \le M$ for all $n$
and all $t \in [0, 1]$, such that every $\varphi_n$ equals some $\psi_m$ and $(\psi_n)$ is
complete: every $g \in L^2[0, 1]$ with $\int_0^1 \psi_n g \, dt = 0$ for all $n$ vanishes
almost everywhere on $[0, 1]$.

The case of interest in the original problem is when infinitely many functions are necessary
for the completion. -/
def ScottishBookProblem86Claim : Prop :=
  ∀ (M : ℝ) (φ : ℕ → ℝ → ℝ), 0 < M →
    (∀ n, AEStronglyMeasurable (φ n) scottishBook86Measure) →
    (∀ n m, ∫ t, φ n t * φ m t ∂scottishBook86Measure =
      if n = m then 1 else 0) →
    (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |φ n t| ≤ M) →
    ∃ ψ : ℕ → ℝ → ℝ,
      (∀ n, AEStronglyMeasurable (ψ n) scottishBook86Measure) ∧
      (∀ n m, ∫ t, ψ n t * ψ m t ∂scottishBook86Measure =
        if n = m then 1 else 0) ∧
      (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |ψ n t| ≤ M) ∧
      (∀ n, ∃ m, ψ m = φ n) ∧
      ∀ g : ℝ → ℝ, MemLp g 2 scottishBook86Measure →
        (∀ n, ∫ t, ψ n t * g t ∂scottishBook86Measure = 0) →
        g =ᵐ[scottishBook86Measure] 0

/--
**Banach's Scottish Book Problem 86 fails.** The Scottish Book Problem 86 claim is false: there
are a real $M > 0$ and a sequence $(\varphi_n)_{n \in \mathbb{N}}$ of functions
$\mathbb{R} \to \mathbb{R}$, almost everywhere measurable on $[0, 1]$, orthonormal in
$L^2[0, 1]$ and with $|\varphi_n(t)| \le M$ for all $n$ and all $t \in [0, 1]$, such that there
is no sequence $(\psi_n)_{n \in \mathbb{N}}$ of functions $\mathbb{R} \to \mathbb{R}$, almost
everywhere measurable on $[0, 1]$, orthonormal in $L^2[0, 1]$ and with $|\psi_n(t)| \le M$ for
all $n$ and all $t \in [0, 1]$, that has every $\varphi_n$ as one of its terms and is complete:
every $g \in L^2[0, 1]$ with $\int_0^1 \psi_n g \, dt = 0$ for all $n$ vanishes almost
everywhere on $[0, 1]$.

Source:
S. Banach, Problem 86 of the Scottish Book; negative answer via
A. Plichko and A. Razenkov, "On three problems from the Scottish Book
connected with orthogonal systems", Colloq. Math. 70 (1996), 227–234,
Proposition 3, which constructs a bounded orthogonal sequence in a
Banach space densely and non-compactly embedded in a Hilbert space
that admits no extension to a fundamental orthogonal sequence using
elements of the Banach space. Earlier work on the problem includes
S. Kaczmarz (1936) and K. S. Kazarian ("On a problem of S. Banach
from the Scottish Book", Proc. Amer. Math. Soc. 110 (1990), 881–887).
-/
theorem_wanted banach86_refuted : ¬ ScottishBookProblem86Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted
