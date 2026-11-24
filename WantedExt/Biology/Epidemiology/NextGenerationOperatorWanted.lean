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
generations; under an irreducibility hypothesis every nonzero nonnegative introduction of
infection grows at rate `R₀` (Remark 3). For a separable kernel `k(ξ, η) = a(ξ) b(η)` the
operator has one-dimensional range and `R₀ = ∫ b S a` (Eqs. (3.1)–(3.3)).

The generation-growth factor `inf_m ‖K^m‖^(1/m)` is the spectral radius of `K` by Gelfand's
formula. The finite-dimensional threshold `R₀ = ρ(F V⁻¹)` of van den Driessche and Watmough is
proved in `Domains.Biology.Epidemiology.NextGenerationMatrix`; the operator statements below
are not proved yet.

Sources: O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, "On the definition and the
computation of the basic reproduction ratio R₀ in models for infectious diseases in
heterogeneous populations", J. Math. Biol. 28 (1990) 365–382, Eqs. (2.1)–(2.2), p. 367,
Remark 3 (p. 369) and Section 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The per-generation growth factor `inf_{m ≥ 1} ‖K^m‖^(1/m)` of a bounded operator, the
basic reproduction ratio `R₀ = r(K)` of Diekmann, Heesterbeek and Metz (1990, Eq. (2.2)). -/
noncomputable def generationGrowth (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : ℝ :=
  ⨅ m : ℕ, ‖K ^ (m + 1)‖ ^ ((1 : ℝ) / (m + 1))

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

/-- **Every introduction grows at rate `R₀` under irreducibility** (Diekmann, Heesterbeek and
Metz 1990, p. 368 and Remark 3). Let `μ` be σ-finite and `K` a positive, compact,
ideal-irreducible operator on `L¹(Ω)` with `R₀ > 0`. Then every nonzero nonnegative infective
distribution `φ` grows at exactly the rate `R₀`: `‖K^m φ‖^(1/m) → R₀`. In particular every
such introduction leads to unbounded generations when `R₀ > 1`.

Source: Diekmann, Heesterbeek and Metz (1990), Remark 3. -/
theorem_wanted tendsto_norm_pow_apply_rpow [SigmaFinite μ] (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hpos : IsPositive K) (hcpt : IsCompactOperator K) (hirr : IsIdealIrreducible K)
    (hK : 0 < generationGrowth K) (φ : Lp ℝ 1 μ) (hφ : 0 ≤ φ) (hφ0 : φ ≠ 0) :
    Tendsto (fun m : ℕ => ‖(K ^ m) φ‖ ^ ((1 : ℝ) / m)) atTop (𝓝 (generationGrowth K))

/-- **`R₀` for a separable kernel** (Diekmann, Heesterbeek and Metz 1990, Section 3.1,
Eqs. (3.1)–(3.3)). Let `a, b, S ≥ 0` be measurable with `b` essentially bounded and `S a`
integrable, and let `K φ = S a ∫ b φ`, the next-generation operator of the kernel
`k(ξ, η) = a(ξ) b(η)`. Then `R₀ = ∫ b S a`.

Source: Diekmann, Heesterbeek and Metz (1990), Eq. (3.3). -/
theorem_wanted generationGrowth_eq_integral_of_separable (a b S : Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hS : Measurable S)
    (ha0 : ∀ ξ, 0 ≤ a ξ) (hb0 : ∀ ξ, 0 ≤ b ξ) (hS0 : ∀ ξ, 0 ≤ S ξ)
    (hbinf : MemLp b ⊤ μ) (hSa : Integrable (fun ξ => S ξ * a ξ) μ)
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hK : ∀ φ : Lp ℝ 1 μ,
      ((K φ : Lp ℝ 1 μ) : Ω → ℝ) =ᵐ[μ] fun ξ => S ξ * a ξ * ∫ η, b η * φ η ∂μ) :
    generationGrowth K = ∫ ξ, b ξ * S ξ * a ξ ∂μ

end WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted
