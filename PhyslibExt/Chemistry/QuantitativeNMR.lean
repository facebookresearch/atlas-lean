/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Classical

/-!
# Quantitative NMR

First-order quantitative NMR: Zeeman splitting, chemical shift, multiplets,
integrals, and the exact AB quartet.

Reuse-verified against Mathlib / ATLAS main: this module imports no next-50
prerequisite module.

## i. Overview

This module formalises the spin-1/2 Zeeman model, the first-order weak-coupling
model (`Δν >> J`), and the full-relaxation integral model of quantitative NMR.
Every identity is a mathematical consequence *inside* its named model; the
models themselves (spin-1/2 Zeeman levels, first-order weak coupling, full
relaxation, Boltzmann populations) are carried as explicit hypotheses.
Second-order effects (when `Δν ~ J`) are outside the first-order model and are
handled only by the elective AB section (§E).

Frequency convention: all frequencies `ν` are in Hz (cycles per second).
Angular frequencies `ω = 2πν` are never used silently; the only bridge between
energy and frequency is the explicit relation `h = 2 * Real.pi * hbar` with
`ν = ΔE / h`. All quantities are plain real numbers; empirical inputs (`γ`,
`B0`, shielding constants `σ`, couplings `J`, relaxation behaviour) are
explicit real parameters, never universal constants.

## ii. Key results

* `zeeman_energy_split`, `zeeman_transition_freq`: Zeeman splitting and the
  transition frequency `ν = γ * B0 / (2 * Real.pi)` (CH43.1).
* `chemicalShift_field_indep`: the chemical shift is field-independent to
  first order inside the shielding model (CH43.2).
* `multiplet_sum`, `multiplet_symm`: `n + 1` binomial lines for `n` equivalent
  spin-1/2 neighbours; `card_combined_le`, `card_combined_eq_iff`: the general
  maximum multiplicity `∏ (nᵢ * sᵢ + 1)` with explicit degeneracies;
  `conv_total`, `binomial_vandermonde`: higher-spin intensities by convolution
  (CH43.3).
* `integral_ratio`: integrals proportional to nucleus count under full
  relaxation; `excessFraction_bound`: the Boltzmann population excess is
  `~ γ * hbar * B0 / (2 * kB * T)` to first order with an explicit bound
  (CH43.4).
* `ab_det_plus`, `ab_det_minus`, `ab_first_order_limit`: the exact AB quartet,
  reducing to first order when `|Δν| >> |J|` (CH43.5, elective).

## iii. Table of contents

* §A. Spin-1/2 Zeeman transition frequency.
* §B. Chemical shift: dimensionless and field-independent to first order.
* §C. First-order multiplets, general multiplicity, convolution.
* §D. Integrals and population excess.
* §E. Elective: exact AB quartet.

## iv. References

* IUPAC Green Book (_Quantities, Units and Symbols in Physical Chemistry_) for
  the chemical-shift definition (ppm, dimensionless ratio).
* MIT OCW 5.61 _Physical Chemistry_ (CHEM-S4) for the quantum two-level /
  Zeeman framing.
-/

@[expose] public section

namespace Chemistry.QuantitativeNMR

/-! ## A. Spin-1/2 Zeeman transition frequency (CH43.1) -/

/-- Zeeman energy of a level with magnetic quantum number `m`: `E = -γ * hbar * B0 * m`.
`hbar` is an explicit real parameter (no Mathlib `hbar` constant is assumed).
Model assumption (spin-1/2 Zeeman model): the two levels are `m = ±1/2`. -/
def zeemanEnergy (γ hbar B0 m : ℝ) : ℝ := -γ * hbar * B0 * m

/-- Energy splitting between `m = -1/2` and `m = +1/2`: `ΔE = γ * hbar * B0`.
`γ > 0` fixes the sign convention (for nuclei with negative `γ` the level
ordering flips; the formula with signed `γ` gives a signed frequency, and the
observed frequency is its absolute value — the positive formula is not claimed
for signed `γ`). -/
lemma zeeman_energy_split (γ hbar B0 : ℝ) (hγ : 0 < γ) (hhbar : 0 < hbar)
    (hB0 : 0 < B0) :
    zeemanEnergy γ hbar B0 (-1 / 2) - zeemanEnergy γ hbar B0 (1 / 2) =
      γ * hbar * B0 := by
  simp only [zeemanEnergy]
  ring

/-- Transition frequency from the splitting: with `h = 2 * Real.pi * hbar` and
`ν = ΔE / h`, one has `ν = γ * B0 / (2 * Real.pi)`. `ΔE` and `ν` are stated as
explicit equations; `ν` is in Hz. -/
lemma zeeman_transition_freq (γ hbar B0 ΔE h ν : ℝ) (hγ : 0 < γ)
    (hhbar : 0 < hbar) (hB0 : 0 < B0) (hΔE : ΔE = γ * hbar * B0)
    (hh : h = 2 * Real.pi * hbar) (hν : ν = ΔE / h) :
    ν = γ * B0 / (2 * Real.pi) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hhbar' : hbar ≠ 0 := ne_of_gt hhbar
  have hden : (2 : ℝ) * Real.pi * hbar ≠ 0 := mul_ne_zero hpi hhbar'
  rw [hν, hΔE, hh, div_eq_div_iff hden hpi]
  ring

/-! ## B. Chemical shift (CH43.2) -/

/-- Chemical shift in ppm: `δ = 1e6 * (ν - νref) / νref`, a dimensionless
ratio of frequencies in Hz. `1e6` is the real literal `1000000`. -/
noncomputable def chemicalShift (ν νref : ℝ) : ℝ :=
  1000000 * (ν - νref) / νref

/-- Field independence to first order inside the shielding model: if
`ν = γ * B0 * (1 - σ) / (2 * Real.pi)` and
`νref = γ * B0 * (1 - σref) / (2 * Real.pi)`, then the shift equals
`1e6 * (σref - σ) / (1 - σref)`, which contains no `γ` and no `B0`.
Field-independence holds to first order inside this shielding model; it is not
a claim about higher-order (e.g. susceptibility) field dependence. -/
lemma chemicalShift_field_indep (γ B0 σ σref ν νref : ℝ)
    (hν : ν = γ * B0 * (1 - σ) / (2 * Real.pi))
    (hνref : νref = γ * B0 * (1 - σref) / (2 * Real.pi))
    (hγB : γ * B0 ≠ 0) (hσ : 1 - σref ≠ 0) :
    chemicalShift ν νref = 1000000 * (σref - σ) / (1 - σref) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hγB
  have hB0 : B0 ≠ 0 := right_ne_zero_of_mul hγB
  have hνref' : γ * B0 * (1 - σref) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero (mul_ne_zero hγB hσ) hpi
  rw [hν, hνref]
  simp only [chemicalShift]
  field_simp
  ring

/-- The shift of a frequency against itself is zero (for `ν ≠ 0`). -/
lemma chemicalShift_self (ν : ℝ) (hν : ν ≠ 0) : chemicalShift ν ν = 0 := by
  simp [chemicalShift, sub_self]

/-- The shift is a pure ratio: scaling both frequencies by the same nonzero
factor leaves it unchanged (for `νref ≠ 0`). -/
lemma chemicalShift_scale (ν νref c : ℝ) (hc : c ≠ 0) (hν : νref ≠ 0) :
    chemicalShift (c * ν) (c * νref) = chemicalShift ν νref := by
  have hcν : c * νref ≠ 0 := mul_ne_zero hc hν
  simp only [chemicalShift]
  rw [div_eq_div_iff hcν hν]
  ring

/-! ## C. First-order multiplets, general multiplicity, convolution (CH43.3) -/

/-- Binomial multiplet weights for `n` equivalent spin-1/2 neighbours: the
`k`-th of the `n + 1` lines has relative intensity `Nat.choose n k`.
Model assumption (first-order weak coupling): `Δν >> J`. -/
def multipletWeights (n : ℕ) : Fin (n + 1) → ℝ :=
  fun k => (Nat.choose n (k : ℕ) : ℝ)

/-- The multiplet weights sum to `2 ^ n`. -/
lemma multiplet_sum (n : ℕ) : ∑ k, multipletWeights n k = 2 ^ n := by
  have h1 : (∑ k, multipletWeights n k)
      = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) := by
    simp only [multipletWeights]
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (Nat.choose n i : ℝ)) _
  rw [h1, ← Nat.cast_sum]
  exact_mod_cast Nat.sum_range_choose n

/-- Symmetry of binomial coefficients: `choose n k = choose n (n - k)`. -/
lemma multiplet_symm_nat (n k : ℕ) (hk : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) := (Nat.choose_symm hk).symm

/-- The multiplet weights are symmetric under reversal of the line order. -/
lemma multiplet_symm (n : ℕ) (k : Fin (n + 1)) :
    multipletWeights n k = multipletWeights n (Fin.rev k) := by
  simp only [multipletWeights]
  have hrev : ((Fin.rev k : Fin (n + 1)) : ℕ) = n - (k : ℕ) := by
    have h := Fin.rev_add_cast k
    omega
  have hk : (k : ℕ) ≤ n := by have h2 := k.2; omega
  rw [hrev]
  exact congrArg Nat.cast (multiplet_symm_nat n _ hk)

/-- The number of lines for `n` equivalent spin-1/2 neighbours is `n + 1`. -/
lemma multiplet_card (n : ℕ) : Fintype.card (Fin (n + 1)) = n + 1 :=
  Fintype.card_fin _

/-- Position of the `k`-th multiplet line: `ν0 + (k - n / 2) * J`, with centre
`ν0` and coupling `J`, both in Hz. -/
noncomputable def linePosition (ν0 J : ℝ) (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  ν0 + (((k.val : ℕ) : ℝ) - (n : ℝ) / 2) * J

/-- The line positions are distinct when `J ≠ 0` (the position function is
injective). First-order positions are not claimed when `Δν ~ J`. -/
lemma linePosition_injective (ν0 J : ℝ) (n : ℕ) (hJ : J ≠ 0) :
    Function.Injective (linePosition ν0 J n) := by
  intro a b hab
  simp only [linePosition] at hab
  have h2 : (((a.val : ℕ) : ℝ) - (n : ℝ) / 2) * J =
      (((b.val : ℕ) : ℝ) - (n : ℝ) / 2) * J := by linarith [hab]
  have h : ((a.val : ℕ) : ℝ) - (n : ℝ) / 2 =
      ((b.val : ℕ) : ℝ) - (n : ℝ) / 2 := mul_right_cancel₀ hJ h2
  have hcast : ((a.val : ℕ) : ℝ) = ((b.val : ℕ) : ℝ) := by linarith [h]
  have hval : a.val = b.val := Nat.cast_inj.mp hcast
  exact Fin.ext hval

/-- Maximum multiplicity over an explicit finite set `s` of groups: spins are
given by `s_ : ι → ℕ` where the spin of group `i` is `s_ i / 2` (so `s_ i` is
twice the spin), and `n i` is the number of equivalent nuclei in group `i`. -/
def maxMultiplicityOn {ι : Type*} (s : Finset ι) (n s_ : ι → ℕ) : ℕ :=
  ∏ i ∈ s, (n i * s_ i + 1)

/-- Maximum multiplicity over all groups of a finite index type. -/
def maxMultiplicity {ι : Type*} [Fintype ι] (n s_ : ι → ℕ) : ℕ :=
  maxMultiplicityOn Finset.univ n s_

/-- For spin-1/2 groups (`s_ i = 1` on `s`), the multiplicity is
`∏ i ∈ s, (n i + 1)`. -/
lemma maxMultiplicityOn_spinHalf {ι : Type*} (s : Finset ι) (n s_ : ι → ℕ)
    (h : ∀ i ∈ s, s_ i = 1) :
    maxMultiplicityOn s n s_ = ∏ i ∈ s, (n i + 1) := by
  simp only [maxMultiplicityOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [h i hi, mul_one]

/-- For spin-1/2 groups (`s_ i = 1` for all `i`), the maximum multiplicity is
`∏ i, (n i + 1)`. -/
lemma maxMultiplicity_spinHalf {ι : Type*} [Fintype ι] (n s_ : ι → ℕ)
    (h : ∀ i, s_ i = 1) : maxMultiplicity n s_ = ∏ i, (n i + 1) := by
  rw [maxMultiplicity, maxMultiplicityOn_spinHalf _ _ _ (fun i _ => h i)]

/-- Multiplicativity over a disjoint union of group sets: the product over
` s ∪ t` splits into a product of products. -/
lemma maxMultiplicityOn_union {ι : Type*} (s t : Finset ι) (n s_ : ι → ℕ)
    (h : Disjoint s t) :
    maxMultiplicityOn (s ∪ t) n s_ =
      maxMultiplicityOn s n s_ * maxMultiplicityOn t n s_ := by
  simp only [maxMultiplicityOn]
  rw [Finset.prod_union h]

/-- The combined shift of one choice of line per group: the sum over groups of
the chosen line positions. -/
def combinedSum {ι : Type*} [Fintype ι] (lines : ι → Finset ℝ)
    (x : Π i, ↥(lines i)) : ℝ :=
  ∑ i, ((x i : ↥(lines i)) : ℝ)

/-- Combined line positions: sums `∑ i, x i` with `x i ∈ lines i`, as a finite
set (coincident sums appear once). -/
noncomputable def combinedLines {ι : Type*} [Fintype ι] (lines : ι → Finset ℝ) :
    Finset ℝ :=
  Finset.univ.image (combinedSum lines)

/-- The number of per-group line choices equals the maximum multiplicity. -/
lemma card_univ_choices_eq_maxMult {ι : Type*} [Fintype ι]
    (lines : ι → Finset ℝ) (n s : ι → ℕ)
    (hcard : ∀ i, (lines i).card = n i * s i + 1) :
    (Finset.univ : Finset (Π i, ↥(lines i))).card = maxMultiplicity n s := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp only [maxMultiplicity, maxMultiplicityOn]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_coe, hcard i]

/-- Resolved-line bound: the number of distinct combined positions is at most
the maximum multiplicity. Coincident shifts/degeneracies reduce the resolved
count; the product is the _maximum_ resolved multiplicity. -/
lemma card_combined_le {ι : Type*} [Fintype ι] (lines : ι → Finset ℝ)
    (n s : ι → ℕ) (hcard : ∀ i, (lines i).card = n i * s i + 1) :
    (combinedLines lines).card ≤ maxMultiplicity n s := by
  have hmax := card_univ_choices_eq_maxMult lines n s hcard
  change (Finset.univ.image (combinedSum lines)).card ≤ _
  calc (Finset.univ.image (combinedSum lines)).card ≤ Finset.univ.card :=
        Finset.card_image_le
    _ = maxMultiplicity n s := hmax

/-- Equality holds iff the sum map is injective on the per-group choices
(`Set.InjOn` over the full choice set). -/
lemma card_combined_eq_iff {ι : Type*} [Fintype ι] (lines : ι → Finset ℝ)
    (n s : ι → ℕ) (hcard : ∀ i, (lines i).card = n i * s i + 1) :
    (combinedLines lines).card = maxMultiplicity n s ↔
      Set.InjOn (combinedSum lines)
        (Finset.univ : Finset (Π i, ↥(lines i))) := by
  have hmax := card_univ_choices_eq_maxMult lines n s hcard
  constructor
  · intro heq x _ y _ hxy
    by_contra hne
    have hsub : Finset.univ.image (combinedSum lines) ⊆
        (Finset.univ.erase x).image (combinedSum lines) := by
      intro z hz
      rw [Finset.mem_image] at hz ⊢
      obtain ⟨w, _, rfl⟩ := hz
      by_cases hwx : w = x
      · subst hwx
        exact ⟨y, Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ y⟩,
          hxy.symm⟩
      · exact ⟨w, Finset.mem_erase.mpr ⟨hwx, Finset.mem_univ w⟩, rfl⟩
    have hle : (Finset.univ.image (combinedSum lines)).card ≤
        (Finset.univ.erase x).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_image_le
    rw [Finset.card_erase_of_mem (Finset.mem_univ x)] at hle
    have hpos : 0 < maxMultiplicity n s := by
      rw [← hmax]
      exact Finset.card_pos.mpr ⟨x, Finset.mem_univ x⟩
    have heq' : (Finset.univ.image (combinedSum lines)).card =
        maxMultiplicity n s := heq
    omega
  · intro hinj
    change (Finset.univ.image (combinedSum lines)).card = _
    rw [Finset.card_image_of_injOn hinj]
    exact hmax

/-- Convolution of finitely supported intensity functions: the intensity at a
combined position `k` is the sum of `f i * g j` over pairs with
`pos i j = k`. On `ℤ` with `pos i j = i + j` restricted to finite supports this
is `(f * g) k = ∑ i, f i * g (k - i)`; the finite-type form below is the
representation that makes total-intensity provable. -/
def convIntensity {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (f : α → ℝ) (g : β → ℝ) (pos : α → β → γ) : γ → ℝ :=
  fun k => ∑ i, ∑ j, if pos i j = k then f i * g j else 0

/-- Total intensity multiplies: the intensity distribution of two independent
groups is the convolution of the per-group distributions. -/
lemma conv_total {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (f : α → ℝ) (g : β → ℝ) (pos : α → β → γ) :
    ∑ k, convIntensity f g pos k = (∑ i, f i) * (∑ j, g j) := by
  have hswap : (∑ k, ∑ i, ∑ j, (if pos i j = k then f i * g j else 0)) =
      ∑ i, ∑ j, ∑ k, (if pos i j = k then f i * g j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hmul : (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, f i * g j :=
    Finset.sum_mul_sum _ _ _ _
  simp only [convIntensity]
  rw [hswap, hmul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Fintype.sum_ite_eq _ _

/-- Vandermonde convolution for binomials over `Finset.antidiagonal`
(`Nat.choose` is zero above the diagonal, as Mathlib defines it). -/
lemma binomial_vandermonde (n m k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k,
        ((Nat.choose n ij.1 : ℝ) * (Nat.choose m ij.2 : ℝ)) =
      ((Nat.choose (n + m) k : ℕ) : ℝ) := by
  simp_rw [← Nat.cast_mul, ← Nat.cast_sum]
  exact (congrArg Nat.cast (Nat.add_choose_eq n m k)).symm

/-! ## D. Integrals and population excess (CH43.4) -/

/-- Integrals are proportional to nucleus count: if `ii = C * Ni` and
`ij = C * Nj` for a common `C ≠ 0` (full-relaxation model hypothesis, `C` a
real parameter) and `Nj ≠ 0`, then `ii / ij = Ni / Nj`. Proportionality holds
_under full relaxation_; relaxation-weighted integrals are not claimed. -/
lemma integral_ratio (C Ni Nj ii ij : ℝ) (hC : C ≠ 0) (hNj : Nj ≠ 0)
    (hi : ii = C * Ni) (hj : ij = C * Nj) : ii / ij = Ni / Nj := by
  have h1 : C * Nj ≠ 0 := mul_ne_zero hC hNj
  rw [hi, hj, div_eq_div_iff h1 hNj]
  ring

/-- Population excess fraction in exponential form, with
`x = γ * hbar * B0 / (kB * T)` (all parameters explicit reals): the Boltzmann
population ratio is a model assumption (MOD), and this is its mathematical
consequence (MC). -/
noncomputable def excessFraction (x : ℝ) : ℝ :=
  (Real.exp x - 1) / (Real.exp x + 1)

/-- The excess fraction always lies strictly inside `(-1, 1)`. -/
lemma excessFraction_abs_lt_one (t : ℝ) : |excessFraction t| < 1 := by
  have h1 : (0 : ℝ) < Real.exp t + 1 := by have h := Real.exp_pos t; linarith
  simp only [excessFraction]
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ h1]; have h := Real.exp_pos t; linarith
  · rw [div_lt_iff₀ h1]; have h := Real.exp_pos t; linarith

/-- Lower sandwich bound: for `x > -1`, `x / (2 + x) ≤ excessFraction x`,
from `Real.exp x ≥ 1 + x` and monotonicity of `(u - 1) / (u + 1)` in `u`. -/
lemma excessFraction_lower (x : ℝ) (hx : -1 < x) :
    x / (2 + x) ≤ excessFraction x := by
  have hle : (1 : ℝ) + x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x; linarith
  have hmono : ((1 + x) - 1) / ((1 + x) + 1) ≤
      (Real.exp x - 1) / (Real.exp x + 1) := by
    have h1 : (0 : ℝ) < (1 + x) + 1 := by linarith
    have h2 : (0 : ℝ) < Real.exp x + 1 := by
      have h := Real.exp_pos x; linarith
    rw [div_le_div_iff₀ h1 h2]
    linear_combination 2 * hle
  have hphi : ((1 + x) - 1) / ((1 + x) + 1) = x / (2 + x) := by
    congr 1 <;> ring
  rw [hphi] at hmono
  simpa [excessFraction] using hmono

/-- Upper sandwich bound: for `x < 1`, `excessFraction x ≤ x / (2 - x)`, from
`Real.exp x ≤ 1 / (1 - x)` (via `Real.exp (-x) ≥ 1 - x`) and monotonicity. -/
lemma excessFraction_upper (x : ℝ) (hx : x < 1) :
    excessFraction x ≤ x / (2 - x) := by
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hle : Real.exp x ≤ 1 / (1 - x) := by
    have h0 : (-x) + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
    rw [Real.exp_neg] at h0
    have h1 : (1 : ℝ) - x ≤ (Real.exp x)⁻¹ := by linarith [h0]
    have h2 : Real.exp x * (1 - x) ≤ 1 := by
      calc Real.exp x * (1 - x) ≤ Real.exp x * (Real.exp x)⁻¹ :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt he)
        _ = 1 := mul_inv_cancel₀ (ne_of_gt he)
    rw [le_div_iff₀ h1x]
    exact h2
  have hpos : (0 : ℝ) < 1 / (1 - x) := one_div_pos.mpr h1x
  have hmono : (Real.exp x - 1) / (Real.exp x + 1) ≤
      (1 / (1 - x) - 1) / (1 / (1 - x) + 1) := by
    have h1 : (0 : ℝ) < Real.exp x + 1 := by linarith
    have h2 : (0 : ℝ) < 1 / (1 - x) + 1 := by linarith
    rw [div_le_div_iff₀ h1 h2]
    linear_combination 2 * hle
  have hphi : (1 / (1 - x) - 1) / (1 / (1 - x) + 1) = x / (2 - x) := by
    have hne : (1 : ℝ) - x ≠ 0 := ne_of_gt h1x
    have hne2 : (2 : ℝ) - x ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 2 - x)
    field_simp
    ring
  rw [hphi] at hmono
  simpa [excessFraction] using hmono

/-- First-order bound on the open interval: for `-1 < x < 1`,
`|excessFraction x - x / 2| ≤ x ^ 2`, from the sandwich bounds. -/
lemma excessFraction_bound_interior (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    |excessFraction x - x / 2| ≤ x ^ 2 := by
  have hlow := excessFraction_lower x hx1
  have hup := excessFraction_upper x hx2
  have h2x : (0 : ℝ) < 2 + x := by linarith
  have h2x' : (0 : ℝ) < 2 - x := by linarith
  have h3a : (0 : ℝ) < 3 + 2 * x := by linarith
  have h3b : (0 : ℝ) < 3 - 2 * x := by linarith
  have n1 : (2 : ℝ) + x ≠ 0 := ne_of_gt h2x
  have n2 : (2 : ℝ) - x ≠ 0 := ne_of_gt h2x'
  have e1 : x / (2 + x) - (x / 2 - x ^ 2) = x ^ 2 * (3 + 2 * x) / (2 * (2 + x)) := by
    field_simp
    ring
  have e2 : (x / 2 + x ^ 2) - x / (2 - x) = x ^ 2 * (3 - 2 * x) / (2 * (2 - x)) := by
    field_simp
    ring
  have g1 : (0 : ℝ) ≤ x ^ 2 * (3 + 2 * x) / (2 * (2 + x)) := by positivity
  have g2 : (0 : ℝ) ≤ x ^ 2 * (3 - 2 * x) / (2 * (2 - x)) := by positivity
  rw [abs_le]
  constructor
  · linarith [hlow, e1, g1]
  · linarith [hup, e2, g2]

/-- First-order bound: for `|x| ≤ 1`, `|excessFraction x - x / 2| ≤ x ^ 2`.
This is a first-order approximation with an explicit bound, not an exact
equality; the population excess is `~ γ * hbar * B0 / (2 * kB * T)` only to
first order (with `x = γ * hbar * B0 / (kB * T)`). -/
lemma excessFraction_bound (x : ℝ) (hx : |x| ≤ 1) :
    |excessFraction x - x / 2| ≤ x ^ 2 := by
  by_cases hlt : |x| < 1
  · have hx12 := abs_lt.mp hlt
    exact excessFraction_bound_interior x hx12.1 hx12.2
  · have habs : |x| = 1 := le_antisymm hx (not_lt.mp hlt)
    have hsq : x ^ 2 = 1 := by rw [← sq_abs, habs]; norm_num
    have hor : x = 1 ∨ x = -1 := sq_eq_one_iff.mp hsq
    obtain rfl | rfl := hor
    · have hlow := excessFraction_lower 1 (by norm_num)
      have hcrude := excessFraction_abs_lt_one 1
      norm_num at hlow ⊢
      rw [abs_lt] at hcrude
      rw [abs_le]
      obtain ⟨hc1, hc2⟩ := hcrude
      constructor <;> linarith [hlow, hc1, hc2]
    · have hup := excessFraction_upper (-1) (by norm_num)
      have hcrude := excessFraction_abs_lt_one (-1)
      norm_num at hup ⊢
      rw [abs_lt] at hcrude
      rw [abs_le]
      obtain ⟨hc1, hc2⟩ := hcrude
      constructor <;> linarith [hup, hc1, hc2]

/-! ## E. Elective: exact AB quartet (CH43.5) -/

/-- AB Hamiltonian (2x2, in the product basis): `H = !![νA, J / 2; J / 2, νB]`
as a `Matrix (Fin 2) (Fin 2) ℝ`. -/
noncomputable def abHamiltonian (νA νB J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![νA, J / 2; J / 2, νB]

/-- Upper AB eigenvalue: `(νA + νB) / 2 + (1 / 2) * √((νA - νB) ^ 2 + J ^ 2)`. -/
noncomputable def abEigenPlus (νA νB J : ℝ) : ℝ :=
  (νA + νB) / 2 + (1 / 2) * Real.sqrt ((νA - νB) ^ 2 + J ^ 2)

/-- Lower AB eigenvalue: `(νA + νB) / 2 - (1 / 2) * √((νA - νB) ^ 2 + J ^ 2)`. -/
noncomputable def abEigenMinus (νA νB J : ℝ) : ℝ :=
  (νA + νB) / 2 - (1 / 2) * Real.sqrt ((νA - νB) ^ 2 + J ^ 2)

/-- The upper stated value satisfies the characteristic equation
`det (H - λ • 1) = 0`. No eigenspace basis is claimed. -/
lemma ab_det_plus (νA νB J : ℝ) :
    Matrix.det (abHamiltonian νA νB J - abEigenPlus νA νB J • 1) = 0 := by
  have hD : (0 : ℝ) ≤ (νA - νB) ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt ((νA - νB) ^ 2 + J ^ 2)) ^ 2 =
      (νA - νB) ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  have hM : abHamiltonian νA νB J - abEigenPlus νA νB J • 1 =
      !![νA - abEigenPlus νA νB J, J / 2; J / 2, νB - abEigenPlus νA νB J] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [abHamiltonian, show (0 : Fin 2) ≠ 1 from by decide,
        show (1 : Fin 2) ≠ 0 from by decide]
  rw [hM, Matrix.det_fin_two_of]
  simp only [abEigenPlus]
  linear_combination (1 / 4 : ℝ) * hsq

/-- The lower stated value satisfies the characteristic equation
`det (H - λ • 1) = 0`. No eigenspace basis is claimed. -/
lemma ab_det_minus (νA νB J : ℝ) :
    Matrix.det (abHamiltonian νA νB J - abEigenMinus νA νB J • 1) = 0 := by
  have hD : (0 : ℝ) ≤ (νA - νB) ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt ((νA - νB) ^ 2 + J ^ 2)) ^ 2 =
      (νA - νB) ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  have hM : abHamiltonian νA νB J - abEigenMinus νA νB J • 1 =
      !![νA - abEigenMinus νA νB J, J / 2; J / 2, νB - abEigenMinus νA νB J] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [abHamiltonian, show (0 : Fin 2) ≠ 1 from by decide,
        show (1 : Fin 2) ≠ 0 from by decide]
  rw [hM, Matrix.det_fin_two_of]
  simp only [abEigenMinus]
  linear_combination (1 / 4 : ℝ) * hsq

/-- Trace matching: the two stated values sum to `νA + νB`. Together with
`ab_eigen_prod` this is the provable form of `(X - λ₁)(X - λ₂)` equaling the
characteristic polynomial for the 2x2 case. -/
lemma ab_eigen_sum (νA νB J : ℝ) :
    abEigenPlus νA νB J + abEigenMinus νA νB J = νA + νB := by
  simp only [abEigenPlus, abEigenMinus]
  ring

/-- Determinant matching: the product of the two stated values equals
`νA * νB - (J / 2) ^ 2`. -/
lemma ab_eigen_prod (νA νB J : ℝ) :
    abEigenPlus νA νB J * abEigenMinus νA νB J =
      νA * νB - (J / 2) ^ 2 := by
  have hD : (0 : ℝ) ≤ (νA - νB) ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt ((νA - νB) ^ 2 + J ^ 2)) ^ 2 =
      (νA - νB) ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  simp only [abEigenPlus, abEigenMinus]
  linear_combination (-1 / 4 : ℝ) * hsq

/-- First-order limit: for `Δν := νA - νB ≠ 0`,
`|√(Δν ^ 2 + J ^ 2) - |Δν|| ≤ J ^ 2 / (2 * |Δν|)`. When `|Δν| >> |J|` the AB
lines approach the first-order positions; the bound quantifies the approach. -/
lemma ab_first_order_limit (Δν J : ℝ) (hΔ : Δν ≠ 0) :
    |(Real.sqrt (Δν ^ 2 + J ^ 2) - |Δν|)| ≤ J ^ 2 / (2 * |Δν|) := by
  have ha : (0 : ℝ) < |Δν| := abs_pos.mpr hΔ
  have hD : (0 : ℝ) ≤ Δν ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt (Δν ^ 2 + J ^ 2)) ^ 2 = Δν ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  have hge : |Δν| ≤ Real.sqrt (Δν ^ 2 + J ^ 2) := by
    have h2 : Real.sqrt (Δν ^ 2) ≤ Real.sqrt (Δν ^ 2 + J ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg J))
    have h1 : |Δν| = Real.sqrt (Δν ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    rw [h1]
    exact h2
  have hpos : (0 : ℝ) < Real.sqrt (Δν ^ 2 + J ^ 2) + |Δν| := by
    have hnn := Real.sqrt_nonneg (Δν ^ 2 + J ^ 2)
    linarith
  have hdiff : Real.sqrt (Δν ^ 2 + J ^ 2) - |Δν| =
      J ^ 2 / (Real.sqrt (Δν ^ 2 + J ^ 2) + |Δν|) := by
    rw [eq_div_iff (ne_of_gt hpos)]
    linear_combination hsq - sq_abs Δν
  have hden : (2 : ℝ) * |Δν| ≤ Real.sqrt (Δν ^ 2 + J ^ 2) + |Δν| := by
    linarith [hge]
  have h2a : (0 : ℝ) < 2 * |Δν| := by linarith [ha]
  have hle : J ^ 2 / (Real.sqrt (Δν ^ 2 + J ^ 2) + |Δν|) ≤ J ^ 2 / (2 * |Δν|) := by
    have h := one_div_le_one_div_of_le h2a hden
    have hsq2 : (0 : ℝ) ≤ J ^ 2 := sq_nonneg J
    calc J ^ 2 / (Real.sqrt (Δν ^ 2 + J ^ 2) + |Δν|)
        = J ^ 2 * (1 / (Real.sqrt (Δν ^ 2 + J ^ 2) + |Δν|)) := by ring
      _ ≤ J ^ 2 * (1 / (2 * |Δν|)) := mul_le_mul_of_nonneg_left h hsq2
      _ = J ^ 2 / (2 * |Δν|) := by ring
  have hnn : (0 : ℝ) ≤ Real.sqrt (Δν ^ 2 + J ^ 2) - |Δν| := by linarith [hge]
  rw [abs_of_nonneg hnn, hdiff]
  exact hle

end Chemistry.QuantitativeNMR
