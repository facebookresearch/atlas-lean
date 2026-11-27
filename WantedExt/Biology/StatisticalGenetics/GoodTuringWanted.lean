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
that the total population frequency of the species seen `r` times is about `(r + 1) n_{r+1} / N`
(eq. 6), and in particular that the chance that the next individual belongs to a new species is
about `n₁ / N` (eq. 9). These approximations come from Good's exact relation (eq. 15), which
compares a sample of size `N` with one of size `N + 1`:
`E_N(q_r) = (r + 1) E_{N+1}(n_{r+1}) / ((N + 1) E_N(n_r))` for the population frequency `q_r` of
a species seen `r` times. Multiplied by `E_N(n_r)` (eq. 11) it says that the expected total
probability of the species seen exactly `r` times in a sample of size `N` is
`(r + 1) E[n_{r+1}(N + 1)] / (N + 1)`; for `r = 0`, the expected missing mass is
`E[M₀(N)] = E[n₁(N + 1)] / (N + 1)`.

Recorded here: the identity for species seen `r` times, in total-mass form, for samples drawn
independently from `p`. The definitions and the case `r = 0` (`expect_missingMass`) are in
`Domains.Biology.StatisticalGenetics.GoodTuring`, which this module imports. The text read locally
is an OCR copy whose displayed equations are partly garbled; the equation numbers follow Good
(1953), and the total-mass form is derived from eq. 15 and eq. 11.

Sources: I. J. Good, "The population frequencies of species and the estimation of population
parameters", Biometrika 40 (1953) 237–264, doi:10.1093/biomet/40.3-4.237, eqs. 6, 9, 11 and 15.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Domains.Biology.StatisticalGenetics.GoodTuring

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.GoodTuringWanted

open Finset

/-- **The Good–Turing identity for species seen `r` times** (Good 1953, eq. 15 multiplied by
eq. 11, in total-mass form; its approximation is eq. 6): let `p` be a probability distribution
on a finite set of species (every `p(a) ≥ 0`, `∑ p(a) = 1`), `N` a sample size and `r` a natural
number. Then the expected total probability of the species seen exactly `r` times in a sample of
size `N` equals `(r + 1) E[n_{r+1}(N + 1)] / (N + 1)`.

Source: Good (1953), eqs. 15, 11 and 6. -/
public theorem_wanted expect_massSeen {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : ∑ a, p a = 1) (N r : ℕ) :
    expect N p (fun ω => massSeen p ω r) =
      (r + 1) * expect (N + 1) p (fun ω => (freqOfFreq ω (r + 1) : ℝ)) / (N + 1)

end WantedExt.Biology.StatisticalGenetics.GoodTuringWanted
