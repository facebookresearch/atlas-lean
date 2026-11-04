/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalMultiaffine

/-!

# Onsager's solution of the two-dimensional Ising model

The free energy of the zero-field square-lattice Ising model as the limit of torus pressures, given
by Onsager's double integral.

## i. Overview

For the nearest-neighbor Ising model with unit coupling and no field on the `L × L` torus, the
pressure `p_L(β) = log Z_L(β) / L²` converges as `L → ∞`, for every `β ≥ 0`, to
`log 2 + (1 / 8π²) ∫_{-π}^{π} ∫_{-π}^{π} log (cosh² 2β - sinh 2β (cos k₁ + cos k₂)) dk₁ dk₂`. All
side lengths `L > 2` are included, odd and even.

The proof is combinatorial, following Kac and Ward, Sherman and Burgoyne. The high-temperature
expansion reduces `Z_L` to the even-subgraph sum `X_L(tanh β)`. Splitting `X_L` by homology class
gives four signed sums whose squares are Kac-Ward determinants with periodic or antiperiodic
boundary phases (the spin Kac-Ward identities). These are proved on a trivalent decoration of the
torus through a multivariate formal power series identity, using Sherman's loop cancellations,
Hopf's Umlaufsatz for contractible loops and a turning computation for non-contractible ones. The
determinants are products over momenta by Fourier analysis, and their logarithms per site are
Riemann sums of Onsager's integrand. The critical point `β_c = ½ log (1 + √2)` is reached by
continuity.

This file collects the main statements under stable names. Scope: `β ≥ 0` (ferromagnetic) only; the
statement does not assert analyticity or non-analyticity of the limit; at `β_c` it asserts
convergence and continuity only.

## ii. Key results

- `main_high_temperature_expansion` : the high-temperature expansion on any finite graph
- `main_critical_beta_value` : `sinh 2β_c = 1`
- `main_critical_beta_unique` : `β_c` is the unique positive solution
- `main_pressure_continuous_at_critical` : Onsager's pressure is continuous at `β_c`
- `main_torus_pressure_decomposition` : the torus pressure through the even-subgraph sum
- `main_free_energy` : Onsager's formula

## iii. Table of contents

- A. Finite volume
- B. The critical point
- C. The torus limit
- D. The Kac-Ward identities and Onsager's formula

## iv. References

- L. Onsager, *Crystal statistics. I. A two-dimensional model with an order-disorder transition*,
  Phys. Rev. 65 (1944) 117-149
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217
- P. N. Burgoyne, *Remarks on the combinatorial approach to the Ising problem*, J. Math. Phys. 4
  (1963) 1320-1326
- H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys.
  Rev. 60 (1941) 252-262
- B. M. McCoy and T. T. Wu, *The Two-Dimensional Ising Model*, Harvard University Press (1973)
- R. J. Baxter, *Exactly Solved Models in Statistical Mechanics*, Academic Press (1982)

-/

@[expose] public section

namespace StatMech.Onsager

open StatMech.Ising

section FiniteVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Finite volume -/

/-- **High-temperature expansion** (van der Waerden 1941). On a finite graph,
`Z(β) = 2^|V| (cosh β)^|E| X(tanh β)` with `X` the even-subgraph generating function. -/
theorem main_high_temperature_expansion (beta : ℝ) :
    ons_Z G beta =
      (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card *
        ons_X G (Real.tanh beta) :=
  ons_hte G beta

/-- The finite-volume pressure as `log 2 + (|E|/|V|) log cosh β + log X(tanh β) / |V|`, for `β ≥ 0`.
-/
lemma main_finite_pressure_decomposition
    (beta : ℝ) (hbeta : 0 ≤ beta) (hV : 0 < Fintype.card V) :
    ons_pressureFinite G beta =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) *
          Real.log (Real.cosh beta) +
        Real.log (ons_X G (Real.tanh beta)) / (Fintype.card V : ℝ) :=
  ons_pressureFinite_eq G beta hbeta hV

end FiniteVolume

section CriticalPoint

/-! ## B. The critical point -/

/-- **Kramers-Wannier critical point.** `β_c = ½ log (1 + √2)` satisfies `sinh 2β_c = 1` (H. A.
Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, 1941). -/
theorem main_critical_beta_value :
    Real.sinh (2 * ons_betaC) = 1 :=
  ons_betaC_sinh

/-- `β_c` is the only positive `β` with `sinh 2β = 1`. -/
theorem main_critical_beta_unique (beta : ℝ) (hbeta : 0 < beta) :
    Real.sinh (2 * beta) = 1 ↔ beta = ons_betaC :=
  ons_betaC_unique beta hbeta

/-- Onsager's pressure is continuous at `β_c`. Its non-analyticity there is not proved here. -/
lemma main_pressure_continuous_at_critical :
    ContinuousAt ons_pressure ons_betaC :=
  ons_continuousAt_pressure_betaC

end CriticalPoint

section TorusLimit

/-! ## C. The torus limit -/

/-- On the `L × L` torus, `p_L(β) = log 2 + 2 log cosh β + log X_L(tanh β) / L²` for `β ≥ 0`. -/
lemma main_torus_pressure_decomposition
    (L : ℕ) [Fact (2 < L)] (beta : ℝ) (hbeta : 0 ≤ beta) :
    ons_pressureFinite (onsTorusGraph L) beta =
      Real.log 2 + 2 * Real.log (Real.cosh beta) +
        Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) / ((L : ℝ) ^ 2) :=
  ons_torusPressure_eq L beta hbeta

/-- Onsager's formula follows from the spin Kac-Ward identities at all `β`. -/
lemma main_free_energy_from_spin_kacWard
    (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) :=
  ons_free_energy_of_spinKacWard_all hall beta hbeta

end TorusLimit

section FiniteKacWard

/-! ## D. The Kac-Ward identities and Onsager's formula -/

/-- The spin Kac-Ward identities follow from the edge-weighted root identity on all tori. -/
lemma main_spin_kacWard_from_weighted_root
    (hweighted : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_weightedRootIdentity L)
    (beta : ℝ) :
    ons_spinKacWardIdentities beta :=
  ons_spinKacWardIdentities_of_weightedRoot hweighted beta

/-- The edge-weighted root identity follows from the formal Kac-Ward identity on the decorated
torus. -/
lemma main_weighted_root_from_decorated_formal
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L) :
    ons_weightedRootIdentity L :=
  ons_weightedRootIdentity_of_decoratedFormal L hformal

/-- The spin Kac-Ward identities follow from the formal Kac-Ward identity on all decorated tori. -/
lemma main_spin_kacWard_from_decorated_formal
    (hformal : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L)
    (beta : ℝ) :
    ons_spinKacWardIdentities beta :=
  ons_spinKacWardIdentities_of_decoratedFormal hformal beta

/-- **Onsager's formula** (L. Onsager, *Crystal statistics. I. A two-dimensional model with an
order-disorder transition*, Phys. Rev. 65, 1944). For the zero-field nearest-neighbor Ising model
with unit coupling on the `L × L` torus, the pressure `log Z_L(β) / L²` converges, for every
`β ≥ 0`, to `log 2 + (1 / 8π²) ∫∫_{[-π, π]²} log (cosh² 2β - sinh 2β (cos k₁ + cos k₂))`.

The limit runs over all `L` (the sequence is `0` for `L ≤ 2`, which does not affect it). Negative
`β` (antiferromagnetic coupling) is not covered: the right-hand side is even in `β`, but the
corresponding limit, which on odd tori involves frustrated configurations, is not proved here.
Non-analyticity at `β_c` is not part of the statement. -/
theorem main_free_energy
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop
        (nhds
          (Real.log 2 +
            (1 / (8 * Real.pi ^ 2)) *
              ∫ k₁ in (-Real.pi)..Real.pi,
                ∫ k₂ in (-Real.pi)..Real.pi,
                  Real.log
                    (Real.cosh (2 * beta) ^ 2 -
                      Real.sinh (2 * beta) *
                        (Real.cos k₁ + Real.cos k₂)))) := by
  simpa [ons_pressure, ons_freeEnergyIntegral, ons_gInt] using
    ons_free_energy beta hbeta

end FiniteKacWard

end StatMech.Onsager
