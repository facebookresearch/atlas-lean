/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Limits of identifiability of population-size histories from the SFS

For a relative population-size function `η`, the expected time to the first coalescence among
`m` lineages is `c_m = ∫_0^∞ exp(-C(m,2) R(s)) ds`, `R(s) = ∫_0^s 1/η`
(`MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS.firstCoalMean`). Bhaskar &
Song (2014) show that the expected site frequency spectrum of a sample of size `n` and
`(c_2, …, c_n)` determine each other, so statements about `(c_m)` are statements about the
expected SFS; that reduction is not formalized.

Proved in `MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS`
(`PiecewiseHistory.sizeFn_eq_of_firstCoalMean_eq`): a piecewise-constant history with `K`
pieces is determined by `c_2, …, c_n` when `n ≥ 2K`. Recorded here:

* the tightness of `n ≥ 2K` for every `K` (Bhaskar & Song 2014, Corollary 7): with only
  `c_2, …, c_{2K-1}`, two different `K`-piece histories can agree. The case `K = 2` is proved
  by an explicit pair (`PiecewiseHistory.exists_ne_firstCoalMean_eq_two`);
* the non-identifiability of general histories (Myers, Fefferman & Patterson 2008): there are
  two population-size functions, bounded above and below by positive constants and different
  on a set of positive measure, with the same `c_m` for every `m ≥ 2`, hence the same expected
  SFS for every sample size.

Sources: A. Bhaskar and Y. S. Song, "Descartes' rule of signs and the identifiability of
population demographic models from genomic variation data", Ann. Statist. 42 (2014)
2469–2493, Corollary 7; S. Myers, C. Fefferman and N. Patterson, "Can one learn history from
the allelic spectrum?", Theor. Popul. Biol. 73 (2008) 342–348.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted

open MeasureTheory Finset
open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS

/-- **Tightness of `n ≥ 2K`** (Bhaskar & Song 2014, Corollary 7): for every `K ≥ 2` there are
two piecewise-constant histories with `K` pieces whose sizes differ at some time `s ≥ 0` but
whose first-coalescence times `c_m` agree for `2 ≤ m ≤ 2K - 1`. (For `K = 1` the range is
empty and the statement is trivial; `K = 2` is
`PiecewiseHistory.exists_ne_firstCoalMean_eq_two`.)

Source: Bhaskar & Song (2014), Corollary 7. -/
theorem_wanted exists_ne_firstCoalMean_eq_of_lt (K : ℕ) (hK : 2 ≤ K) :
    ∃ h h' : PiecewiseHistory K, (∃ s, 0 ≤ s ∧ h.sizeFn s ≠ h'.sizeFn s) ∧
      ∀ m ∈ Icc 2 (2 * K - 1), firstCoalMean h.sizeFn m = firstCoalMean h'.sizeFn m

/-- **Non-identifiability of general histories** (Myers, Fefferman & Patterson 2008): there
are two measurable population-size functions, bounded between positive constants, that differ
on a set of positive Lebesgue measure in `[0, ∞)` and have the same expected first-coalescence
time `c_m` for every `m ≥ 2` (hence the same expected SFS for every sample size).

Source: Myers, Fefferman & Patterson (2008). -/
theorem_wanted exists_ne_ae_firstCoalMean_eq :
    ∃ η₁ η₂ : ℝ → ℝ, Measurable η₁ ∧ Measurable η₂ ∧
      (∃ a b : ℝ, 0 < a ∧ ∀ s, a ≤ η₁ s ∧ η₁ s ≤ b ∧ a ≤ η₂ s ∧ η₂ s ≤ b) ∧
      ¬ (η₁ =ᵐ[volume.restrict (Set.Ici 0)] η₂) ∧
      ∀ m, 2 ≤ m → firstCoalMean η₁ m = firstCoalMean η₂ m

end MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted
