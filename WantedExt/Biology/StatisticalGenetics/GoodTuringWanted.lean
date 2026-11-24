/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Good–Turing estimate of the missing mass

Draw an independent sample of size `N` from a distribution `p` on finitely many species, and let
`n_r(N)` be the number of species seen exactly `r` times. Good (1953), crediting Turing, showed
that the total population frequency of the species seen `r` times is about `(r + 1) n_{r+1} / N`,
and in particular that the proportion of the population represented by the sample is about
`1 - n₁ / N` (eq. 8). The exact form behind these approximations compares a sample of size `N`
with one of size `N + 1`: the expected missing mass satisfies `E[M₀(N)] = E[n₁(N + 1)] / (N + 1)`,
and, more generally, the expected total probability of the species seen exactly `r` times in a
sample of size `N` is `(r + 1) E[n_{r+1}(N + 1)] / (N + 1)`.

Recorded here: the two exact identities for samples drawn independently from `p`. The rendered
equations of Good (1953) were not available locally (the text read is an OCR copy with garbled
displays); the exact identities are derived from the model, and Good's approximate forms
(eq. 2 and eq. 8) are the readable source statements.

Sources: I. J. Good, "The population frequencies of species and the estimation of population
parameters", Biometrika 40 (1953) 237–264, doi:10.1093/biomet/40.3-4.237, eqs. 2 and 8.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.GoodTuringWanted

open Finset

/-- The probability `∏ⱼ p(ωⱼ)` of the ordered sample `ω` of size `N` drawn independently from the
species distribution `p`. -/
noncomputable def sampleProb {α : Type*} {N : ℕ} (p : α → ℝ) (ω : Fin N → α) : ℝ :=
  ∏ j, p (ω j)

/-- The number of times species `a` occurs in the sample `ω`. -/
def count {α : Type*} [DecidableEq α] {N : ℕ} (ω : Fin N → α) (a : α) : ℕ := #{j | ω j = a}

/-- `n_r`: the number of species seen exactly `r` times in the sample `ω`. -/
def freqOfFreq {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} (ω : Fin N → α) (r : ℕ) : ℕ :=
  #{a | count ω a = r}

/-- The total population frequency `∑_{a : count a = r} p(a)` of the species seen exactly `r`
times in the sample `ω`; for `r = 0` this is the missing mass `M₀`. -/
noncomputable def massSeen {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} (p : α → ℝ)
    (ω : Fin N → α) (r : ℕ) : ℝ :=
  ∑ a with count ω a = r, p a

/-- The expectation `∑_ω p(ω) f(ω)` of a function of a sample of size `N` drawn independently from
`p`. -/
noncomputable def expect {α : Type*} [Fintype α] (N : ℕ) (p : α → ℝ) (f : (Fin N → α) → ℝ) : ℝ :=
  ∑ ω : Fin N → α, sampleProb p ω * f ω

/-- **The Good–Turing identity for the missing mass** (Good 1953, exact form of eq. 8; derived):
let `p` be a probability distribution on a finite set of species (every `p(a) ≥ 0`,
`∑ p(a) = 1`) and `N` a sample size. Then the expected total probability of the species not seen
in a sample of size `N` equals the expected number of species seen exactly once in a sample of
size `N + 1`, divided by `N + 1`: `E[M₀(N)] = E[n₁(N + 1)] / (N + 1)`.

Source: Good (1953), eq. 8. -/
public theorem_wanted expect_missingMass {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : ∑ a, p a = 1) (N : ℕ) :
    expect N p (fun ω => massSeen p ω 0) =
      expect (N + 1) p (fun ω => (freqOfFreq ω 1 : ℝ)) / (N + 1)

/-- **The Good–Turing identity for species seen `r` times** (Good 1953, exact form of eq. 2;
derived): let `p` be a probability distribution on a finite set of species (every `p(a) ≥ 0`,
`∑ p(a) = 1`), `N` a sample size and `r` a natural number. Then the expected total probability of
the species seen exactly `r` times in a sample of size `N` equals
`(r + 1) E[n_{r+1}(N + 1)] / (N + 1)`.

Source: Good (1953), eq. 2. -/
public theorem_wanted expect_massSeen {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : ∑ a, p a = 1) (N r : ℕ) :
    expect N p (fun ω => massSeen p ω r) =
      (r + 1) * expect (N + 1) p (fun ω => (freqOfFreq ω (r + 1) : ℝ)) / (N + 1)

end WantedExt.Biology.StatisticalGenetics.GoodTuringWanted
