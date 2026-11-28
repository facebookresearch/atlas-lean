/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Competitive exclusion at fixed densities on fewer resources than species

`n` species with densities `xᵢ` interact only through `k` resource or limiting-factor variables
`R ∈ ℝᵏ`, with per-capita growth rates entering linearly: `xᵢ' = xᵢ gᵢ(R)` and
`gᵢ(R) = bᵢ · R - mᵢ`. An interior equilibrium needs every growth rate to vanish at the
equilibrium resource level, `bᵢ · R = mᵢ` for all `i`: `n` linear equations in `k` unknowns.
Armstrong and McGehee (1980, §5) state that coexistence of `n` species at fixed densities on
`k < n` resources is impossible; for linear growth rates, McGehee and Armstrong (1977, proof of
Theorem 4.5) show that an interior equilibrium needs `m` in the range of the matrix `B` with rows
`bᵢ`, a proper subspace, so for every `B` the set of bad `m` is Lebesgue-null.

Recorded here: for every `B` with `k < n`, almost every `m ∈ ℝⁿ` admits no resource level `R`
with all growth rates zero, so no interior equilibrium exists, whatever the resource dynamics.
This specialization of the cited argument is derived. The claim that two consumers can persist
on one biotic resource along a periodic orbit is not formalized: McGehee
and Armstrong (1977, §7) prove persistence in an attractor block and state that the existence of
an attracting periodic orbit is unknown.

Sources: R. A. Armstrong and R. McGehee, "Competitive exclusion", Am. Nat. 115 (1980) 151–170,
doi:10.1086/283553, §5; R. McGehee and R. A. Armstrong, "Some mathematical problems concerning
the ecological principle of competitive exclusion", J. Differential Equations 23 (1977) 30–52,
doi:10.1016/0022-0396(77)90135-8, Theorems 4.1 and 4.5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

namespace WantedExt.Biology.Ecology.LinearCompetitiveExclusionWanted

open MeasureTheory Matrix

/-- The species can all have zero per-capita growth rate `gᵢ(R) = (B R)ᵢ - mᵢ` at some resource
level `R ∈ ℝᵏ`; this is necessary for an interior equilibrium of `xᵢ' = xᵢ gᵢ(R)` with any
resource dynamics. -/
def CanBalance {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (m : Fin n → ℝ) : Prop :=
  ∃ R : Fin k → ℝ, ∀ i, (B *ᵥ R) i - m i = 0

/-- **No coexistence at fixed densities on fewer resources** (Armstrong and McGehee 1980, §5;
McGehee and Armstrong 1977, Theorem 4.5): let `k < n` and let `B` be any real `n × k` matrix
whose rows are the resource coefficients `bᵢ`. Then for Lebesgue-almost every vector of
mortalities `m ∈ ℝⁿ`, there is no resource level `R ∈ ℝᵏ` at which all `n` growth rates
`(B R)ᵢ - mᵢ` vanish; in particular `n` species with these linear growth rates have no interior
equilibrium.

Sources: Armstrong and McGehee (1980), §5; McGehee and Armstrong (1977), Theorem 4.5. -/
public theorem_wanted ae_not_canBalance {n k : ℕ} (hk : k < n) (B : Matrix (Fin n) (Fin k) ℝ) :
    ∀ᵐ m : Fin n → ℝ ∂volume, ¬ CanBalance B m

end WantedExt.Biology.Ecology.LinearCompetitiveExclusionWanted
