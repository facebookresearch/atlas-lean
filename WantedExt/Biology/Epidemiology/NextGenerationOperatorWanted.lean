/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generation growth for the next-generation operator in a heterogeneous population

Diekmann, Heesterbeek and Metz (1990) describe a heterogeneous population by a measure space
`Ω` of individual states and the next-generation operator on `L¹(Ω)`,

  `(K φ)(ξ) = S(ξ) ∫ k(ξ, η) φ(η) dη`,

a positive operator: an infective distribution `φ` produces `K φ` in the next generation. They
define `R₀ = r(K) = lim_m ‖K^m‖^(1/m) = inf_m ‖K^m‖^(1/m)` (Eq. (2.2)), so that `K^m φ` tends to
zero for every `φ` when `R₀ < 1`, while for `R₀ > 1` some `φ` leads to arbitrarily large later
generations. Under conditions on `K` they describe the long run as `K^m φ ~ c(φ) R₀^m φ_d`, with
`c(φ) > 0` for nonnegative nonzero `φ` (p. 368, Eq. (2.3)), and they remark that an
irreducibility hypothesis is needed for every introduction of infectivity to lead to an epidemic
when `R₀ > 1` (Remark 3). For a separable kernel `k(ξ, η) = a(ξ) b(η)` the operator has range of
dimension at most one and `R₀ = ∫ b S a` (Eqs. (3.1)–(3.3)).

`generationGrowth` is Mathlib's Gelfand radius `gelfandRadius` of the real bounded operator `K`,
the limit of `‖K^m‖^(1/m)`, which is also its infimum over `m ≥ 1` and equals the spectral radius
of the complexification of `K` by Gelfand's formula. The finite-dimensional threshold
`R₀ = ρ(F V⁻¹)` of van den Driessche and Watmough is proved in
`Domains.Biology.Epidemiology.NextGenerationMatrix`.

Recorded here: subcritical decay, supercritical growth and the separable kernel. Not stated here:
the corollary that every nonzero nonnegative introduction grows at exactly the rate `R₀`,
`‖K^m φ‖^(1/m) → R₀`, for a positive, compact, ideal-irreducible `K` with `R₀ > 0` on a σ-finite
space. The source does not state it; its proof needs a strictly positive eigenfunctional of the
adjoint of `K` for `R₀`, from the Perron–Frobenius theory of irreducible positive operators
(Schaefer 1974, §V.5).

Sources: O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, "On the definition and the
computation of the basic reproduction ratio R₀ in models for infectious diseases in
heterogeneous populations", J. Math. Biol. 28 (1990) 365–382, Eqs. (2.1)–(2.3), pp. 367–368,
Remark 3 (p. 369) and Section 3.1; H. H. Schaefer, *Banach Lattices and Positive Operators*,
Springer (1974), §V.5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Domains.Biology.Epidemiology.NextGenerationOperator

@[expose] public section

namespace WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `K` maps nonnegative functions to nonnegative functions. -/
def IsPositive (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : Prop :=
  ∀ φ : Lp ℝ 1 μ, 0 ≤ φ → 0 ≤ K φ

/-- `K` is ideal-irreducible: for no measurable set `E` with `μ E > 0` and `μ Eᶜ > 0` does `K`
map the functions vanishing off `E` to functions vanishing off `E`. -/
def IsIdealIrreducible (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → 0 < μ E → 0 < μ Eᶜ →
    ∃ φ : Lp ℝ 1 μ, (φ : Ω → ℝ) =ᵐ[μ.restrict Eᶜ] 0 ∧
      ¬ ((K φ : Lp ℝ 1 μ) : Ω → ℝ) =ᵐ[μ.restrict Eᶜ] 0

/-- **Subcritical decay** (Diekmann, Heesterbeek and Metz 1990, p. 367): if `R₀ < 1`, then every
infective distribution dies out over generations, `‖K^m φ‖ → 0`. -/
theorem_wanted tendsto_norm_pow_apply_zero (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hK : generationGrowth K < 1) (φ : Lp ℝ 1 μ) :
    Tendsto (fun m : ℕ => ‖(K ^ m) φ‖) atTop (𝓝 0)

/-- **Supercritical growth** (Diekmann, Heesterbeek and Metz 1990, p. 367): for a positive
next-generation operator with `R₀ > 1`, some nonnegative infective distribution `φ` has
unbounded generation sizes `‖K^m φ‖`. -/
theorem_wanted exists_nonneg_unbounded_of_one_lt (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hpos : IsPositive K) (hK : 1 < generationGrowth K) :
    ∃ φ : Lp ℝ 1 μ, 0 ≤ φ ∧ ¬ BddAbove (Set.range fun m : ℕ => ‖(K ^ m) φ‖)

end WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted
