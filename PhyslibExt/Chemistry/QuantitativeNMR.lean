/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Physlib.Relativity.PauliMatrices.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# Quantitative NMR

Zeeman splitting, chemical shift, first-order multiplets, integrals, population excess, and the
exact energy levels and candidate transitions of the two-spin AB system.

## i. Overview

This module formalizes the spin-1/2 Zeeman model, the first-order weak-coupling model
(`|νA - νB| ≫ |J|`), the full-relaxation integral model of quantitative NMR, and the exact AB
spin system. Every identity is a mathematical consequence inside its named model; the model
assumptions (spin-1/2 Zeeman levels, first-order weak coupling, full relaxation, Boltzmann
populations) are explicit hypotheses or are stated in the docstrings.

Frequency convention: all frequencies `ν` are in Hz (cycles per second). Angular frequencies
`ω = 2πν` are never used silently; the only bridge between energy and frequency is the explicit
relation `h = 2 * Real.pi * hbar` with `ν = ΔE / h`. All quantities are plain real numbers;
empirical inputs (`γ`, `B0`, shielding constants `σ`, couplings `J`) are explicit real
parameters, never universal constants.

The AB section (§E) starts from the full two-spin Hamiltonian
`H = -νA I_zA - νB I_zB + J I_A · I_B` in frequency units, built from Physlib's Pauli matrices on
the product basis `αα, αβ, βα, ββ`. The Zeeman terms carry the sign of §A (`E = -γ hbar B0 m`,
with the resonance frequencies `νA`, `νB` positive for `γ > 0`), so for positive `νA`, `νB` the
state `α` (`m = +1/2`) lies below `β`; the Hamiltonian and its spectrum are defined for all real
`νA`, `νB`, `J`, including signed frequencies measured from a carrier. Its eigenvalues are
exactly the four levels `-(νA + νB) / 2 + J / 4` (`αα`), `(νA + νB) / 2 + J / 4` (`ββ`) and
`-J / 4 ± D / 2`, where `D = √((νA - νB) ^ 2 + J ^ 2)`. The four candidate transitions run
between `αα` or `ββ` and the two mixed states (the `ΔM = ±1` selection rule is assumed, not
derived). Their signed transition offsets are `(νA + νB) / 2 ± (D ± J) / 2`; their line
frequencies, the absolute energy gaps, equal these offsets when `|J| < νA` and `|J| < νB`. When
`νA ≠ νB` each offset lies within `J ^ 2 / (4 |νA - νB|)` of its first-order position.
Transition moments and line intensities are not formalized. A candidate is an observed line only
if its transition moment is nonzero, and for `J ≠ 0` all four are observed only when `νA ≠ νB`:
at `νA = νB = ν0` the two candidates at `ν0 ± J` have zero transition moment.

## ii. Key results

- `zeeman_energy_split`, `zeeman_transition_freq` : Zeeman splitting and the transition
  frequency `ν = γ * B0 / (2 * Real.pi)`.
- `chemicalShift_field_indep` : inside the shielding model the chemical shift contains no `γ`
  and no `B0`.
- `multiplet_sum`, `multiplet_symm` : `n + 1` binomial lines for `n` equivalent spin-1/2
  neighbours.
- `card_combined_le`, `card_combined_eq_iff` : the maximum multiplicity `∏ (nᵢ * sᵢ + 1)` of
  several groups, and when it is attained.
- `conv_total` : total intensity under convolution. The Vandermonde identity for binomial
  weights is Mathlib's `Nat.add_choose_eq`.
- `integral_ratio` : integrals are proportional to nucleus count under full relaxation.
- `excessFraction_eq_of_populations`, `excessFraction_bound` : the signed Boltzmann population
  excess and its first-order value `x / 2` with an explicit `x ^ 2` bound.
- `abHamiltonian_hasEigenvalue_iff` : the four energy levels of the AB system.
- `abOffsets_eq` : the signed transition offsets `(νA + νB) / 2 ± (D ± J) / 2` of the four
  candidate AB transitions.
- `abGaps_eq` : the line frequencies, the absolute energy gaps, equal these offsets when both
  resonance frequencies exceed `|J|`.
- `abOffsets_weakCoupling`, `abGaps_weakCoupling` : the weak-coupling limit, with an explicit
  bound.

## iii. Table of contents

- A. Spin-1/2 Zeeman transition frequency
- B. Chemical shift
- C. First-order multiplets, general multiplicity, convolution
- D. Integrals and population excess
- E. The AB spin system
  - E.1. The two-spin Hamiltonian
  - E.2. Energy levels
  - E.3. The mixed-state block
  - E.4. Candidate transitions and the weak-coupling limit

## iv. References

- M. H. Levitt, *Spin Dynamics: Basics of Nuclear Magnetic Resonance*, 2nd ed., Wiley (2008):
  Zeeman splitting, chemical shift, scalar coupling and spin populations.
- R. K. Harris, E. D. Becker, S. M. Cabral de Menezes, R. Goodfellow and P. Granger, "NMR
  nomenclature. Nuclear spin properties and conventions for chemical shifts (IUPAC
  Recommendations 2001)", *Pure Appl. Chem.* 73 (2001) 1795–1818: the chemical-shift scale.
- J. A. Pople, W. G. Schneider and H. J. Bernstein, *High-resolution Nuclear Magnetic
  Resonance*, McGraw-Hill (1959): first-order multiplets and the analysis of the AB spectrum.

-/

open scoped Kronecker Matrix

@[expose] public section

namespace Chemistry.QuantitativeNMR

/-!

## A. Spin-1/2 Zeeman transition frequency

-/

/-- Zeeman energy of a level with magnetic quantum number `m`: `E = -γ * hbar * B0 * m`.
`hbar` is an explicit real parameter (no Mathlib `hbar` constant is assumed).
Model assumption (spin-1/2 Zeeman model): the two levels are `m = ±1/2`. -/
def zeemanEnergy (γ hbar B0 m : ℝ) : ℝ := -γ * hbar * B0 * m

/-- Energy splitting between `m = -1/2` and `m = +1/2`, for `γ`, `hbar`, `B0 > 0`:
`ΔE = γ * hbar * B0`.
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

/-- Transition frequency from the splitting: for `γ`, `hbar`, `B0 > 0`, with
`ΔE = γ * hbar * B0`, `h = 2 * Real.pi * hbar` and `ν = ΔE / h`, one has
`ν = γ * B0 / (2 * Real.pi)`. `ΔE` and `ν` are stated as explicit equations; `ν` is in Hz. -/
lemma zeeman_transition_freq (γ hbar B0 ΔE h ν : ℝ) (hγ : 0 < γ)
    (hhbar : 0 < hbar) (hB0 : 0 < B0) (hΔE : ΔE = γ * hbar * B0)
    (hh : h = 2 * Real.pi * hbar) (hν : ν = ΔE / h) :
    ν = γ * B0 / (2 * Real.pi) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hhbar' : hbar ≠ 0 := ne_of_gt hhbar
  have hden : (2 : ℝ) * Real.pi * hbar ≠ 0 := mul_ne_zero hpi hhbar'
  rw [hν, hΔE, hh, div_eq_div_iff hden hpi]
  ring

/-!

## B. Chemical shift

-/

/-- Chemical shift in ppm: `δ = 1e6 * (ν - νref) / νref`, a dimensionless
ratio of frequencies in Hz. `1e6` is the real literal `1000000`. The shift is
defined only for a reference frequency `νref ≠ 0`: at `νref = 0` Lean's
convention `x / 0 = 0` gives the meaningless value `0`, and the lemmas below
assume `νref ≠ 0` (or a shielding model with `νref ≠ 0`). -/
noncomputable def chemicalShift (ν νref : ℝ) : ℝ :=
  1000000 * (ν - νref) / νref

/-- Field independence to first order inside the shielding model: if
`ν = γ * B0 * (1 - σ) / (2 * Real.pi)` and
`νref = γ * B0 * (1 - σref) / (2 * Real.pi)` with `γ * B0 ≠ 0` and `1 - σref ≠ 0`, then the
shift equals `1e6 * (σref - σ) / (1 - σref)`, which contains no `γ` and no `B0`.
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

/-!

## C. First-order multiplets, general multiplicity, convolution

-/

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

/-- The multiplet weights are symmetric under reversal of the line order. -/
lemma multiplet_symm (n : ℕ) (k : Fin (n + 1)) :
    multipletWeights n k = multipletWeights n (Fin.rev k) := by
  simp only [multipletWeights]
  have hrev : ((Fin.rev k : Fin (n + 1)) : ℕ) = n - (k : ℕ) := by
    have h := Fin.rev_add_cast k
    omega
  have hk : (k : ℕ) ≤ n := by have h2 := k.2; omega
  rw [hrev]
  exact congrArg Nat.cast (Nat.choose_symm hk).symm

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

open Classical in
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

open Classical in
/-- Combined line positions: sums `∑ i, x i` with `x i ∈ lines i`, as a finite
set (coincident sums appear once). -/
noncomputable def combinedLines {ι : Type*} [Fintype ι] (lines : ι → Finset ℝ) :
    Finset ℝ :=
  Finset.univ.image (combinedSum lines)

open Classical in
/-- If group `i` has exactly `n i * s i + 1` lines, the number of per-group line choices equals
the maximum multiplicity. -/
lemma card_univ_choices_eq_maxMult {ι : Type*} [Fintype ι]
    (lines : ι → Finset ℝ) (n s : ι → ℕ)
    (hcard : ∀ i, (lines i).card = n i * s i + 1) :
    (Finset.univ : Finset (Π i, ↥(lines i))).card = maxMultiplicity n s := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp only [maxMultiplicity, maxMultiplicityOn]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_coe, hcard i]

open Classical in
/-- Resolved-line bound: if group `i` has exactly `n i * s i + 1` lines, the number of distinct
combined positions is at most the maximum multiplicity. This is an upper bound only: coincident
positions reduce the resolved count, and `card_combined_eq_iff` says when it is attained. -/
lemma card_combined_le {ι : Type*} [Fintype ι] (lines : ι → Finset ℝ)
    (n s : ι → ℕ) (hcard : ∀ i, (lines i).card = n i * s i + 1) :
    (combinedLines lines).card ≤ maxMultiplicity n s := by
  have hmax := card_univ_choices_eq_maxMult lines n s hcard
  change (Finset.univ.image (combinedSum lines)).card ≤ _
  calc (Finset.univ.image (combinedSum lines)).card ≤ Finset.univ.card :=
        Finset.card_image_le
    _ = maxMultiplicity n s := hmax

open Classical in
/-- If group `i` has exactly `n i * s i + 1` lines, the number of distinct combined positions
equals the maximum multiplicity iff the sum map is injective on the per-group choices
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

/-- Convolution of intensity functions on finite types: the intensity at a
combined position `k` is the sum of `f i * g j` over the pairs `(i, j)` with
`pos i j = k`. In the first-order model the multiplet of two independent groups
of nuclei is this convolution of the per-group intensity functions, with
`pos i j` the combined line position (a model assumption). -/
def convIntensity {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] (f : α → ℝ) (g : β → ℝ) (pos : α → β → γ) : γ → ℝ :=
  fun k => ∑ i, ∑ j, if pos i j = k then f i * g j else 0

/-- Total intensity multiplies under convolution: the intensities of
`convIntensity f g pos` sum to `(∑ i, f i) * (∑ j, g j)`. -/
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

/-!

## D. Integrals and population excess

-/

/-- Integrals are proportional to nucleus count: if `ii = C * Ni` and
`ij = C * Nj` for a common `C ≠ 0` (full-relaxation model hypothesis, `C` a
real parameter) and `Nj ≠ 0`, then `ii / ij = Ni / Nj`. Proportionality holds
_under full relaxation_; relaxation-weighted integrals are not claimed. -/
lemma integral_ratio (C Ni Nj ii ij : ℝ) (hC : C ≠ 0) (hNj : Nj ≠ 0)
    (hi : ii = C * Ni) (hj : ij = C * Nj) : ii / ij = Ni / Nj := by
  have h1 : C * Nj ≠ 0 := mul_ne_zero hC hNj
  rw [hi, hj, div_eq_div_iff h1 hNj]
  ring

/-- The population excess fraction `(e^x - 1) / (e^x + 1)` of a two-level
system whose populations are in the Boltzmann ratio `Nα / Nβ = e^x`
(`excessFraction_eq_of_populations`). It is signed: the excess
`(Nα - Nβ) / (Nα + Nβ)` of `α` over `β`, negative when `x < 0`. For spin-1/2
nuclei in a field `B0` at temperature `T`, `x = γ * hbar * B0 / (kB * T)`,
with all parameters explicit reals; the Boltzmann ratio is the model
assumption. -/
noncomputable def excessFraction (x : ℝ) : ℝ :=
  (Real.exp x - 1) / (Real.exp x + 1)

/-- Populations in the Boltzmann ratio `Nα = e^x * Nβ` with `Nβ > 0` have excess
fraction `(Nα - Nβ) / (Nα + Nβ) = excessFraction x`. -/
lemma excessFraction_eq_of_populations (x Nα Nβ : ℝ) (hβ : 0 < Nβ)
    (h : Nα = Real.exp x * Nβ) : (Nα - Nβ) / (Nα + Nβ) = excessFraction x := by
  have hβ' : Nβ ≠ 0 := ne_of_gt hβ
  have he : Real.exp x + 1 ≠ 0 := by positivity
  rw [h, excessFraction, div_eq_div_iff (by positivity) he]
  ring

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

/-!

## E. The AB spin system

Two coupled spin-1/2 nuclei `A` and `B` with resonance frequencies `νA`, `νB` and scalar
coupling `J`, all in Hz. States are vectors `Fin 2 × Fin 2 → ℂ`: the first factor is nucleus
`A`, and `0 = α` (`m = +1/2`), `1 = β` (`m = -1/2`), so the product basis is `αα = (0, 0)`,
`αβ = (0, 1)`, `βα = (1, 0)` and `ββ = (1, 1)`.

-/

/-!

### E.1. The two-spin Hamiltonian

-/

/-- The AB Hamiltonian in frequency units (Hz), `H = -νA I_zA - νB I_zB + J I_A · I_B`. The
Zeeman terms have the sign of `zeemanEnergy` (`E = -γ hbar B0 m`), so for positive resonance
frequencies `νA`, `νB` the state `α` (`m = +1/2`) lies below `β`. The spin-1/2 operators are
`I_k = σ_k / 2` (`k = 0, 1, 2` for `x, y, z`), with Physlib's Pauli matrices
`σ_k = PauliMatrix.pauliMatrix (Sum.inr k)`. On the two-spin space `I_kA = I_k ⊗ 1` and
`I_kB = 1 ⊗ I_k` (Kronecker products), so `I_kA I_kB = I_k ⊗ I_k` by the mixed-product rule
`Matrix.mul_kronecker_mul`, and the coupling term is `J ∑ k, I_k ⊗ I_k`. -/
noncomputable def abHamiltonian (νA νB J : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  -(νA : ℂ) • (((1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr 2)) ⊗ₖ
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) -
    (νB : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
      ((1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr 2))) +
    (J : ℂ) • ∑ k : Fin 3, ((1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr k)) ⊗ₖ
      ((1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr k))

/-- The `αα` component of `H v` is `(-(νA + νB) / 2 + J / 4) v(αα)`. -/
lemma abHamiltonian_mulVec_alphaAlpha (νA νB J : ℝ) (v : Fin 2 × Fin 2 → ℂ) :
    (abHamiltonian νA νB J *ᵥ v) (0, 0) = ((-(νA + νB) / 2 + J / 4 : ℝ) : ℂ) * v (0, 0) := by
  simp [abHamiltonian, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, PauliMatrix.pauliMatrix, Matrix.one_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The `αβ` component of `H v` is `(-(νA - νB) / 2 - J / 4) v(αβ) + (J / 2) v(βα)`. -/
lemma abHamiltonian_mulVec_alphaBeta (νA νB J : ℝ) (v : Fin 2 × Fin 2 → ℂ) :
    (abHamiltonian νA νB J *ᵥ v) (0, 1) =
      ((-(νA - νB) / 2 - J / 4 : ℝ) : ℂ) * v (0, 1) + ((J / 2 : ℝ) : ℂ) * v (1, 0) := by
  simp [abHamiltonian, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, PauliMatrix.pauliMatrix, Matrix.one_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The `βα` component of `H v` is `(J / 2) v(αβ) + ((νA - νB) / 2 - J / 4) v(βα)`. -/
lemma abHamiltonian_mulVec_betaAlpha (νA νB J : ℝ) (v : Fin 2 × Fin 2 → ℂ) :
    (abHamiltonian νA νB J *ᵥ v) (1, 0) =
      ((J / 2 : ℝ) : ℂ) * v (0, 1) + (((νA - νB) / 2 - J / 4 : ℝ) : ℂ) * v (1, 0) := by
  simp [abHamiltonian, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, PauliMatrix.pauliMatrix, Matrix.one_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The `ββ` component of `H v` is `((νA + νB) / 2 + J / 4) v(ββ)`. -/
lemma abHamiltonian_mulVec_betaBeta (νA νB J : ℝ) (v : Fin 2 × Fin 2 → ℂ) :
    (abHamiltonian νA νB J *ᵥ v) (1, 1) = (((νA + νB) / 2 + J / 4 : ℝ) : ℂ) * v (1, 1) := by
  simp [abHamiltonian, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, PauliMatrix.pauliMatrix, Matrix.one_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The eigenvalue equation `H v = E v`, component by component: `αα` and `ββ` decouple, and
`αβ`, `βα` form a `2 × 2` system. -/
lemma abHamiltonian_mulVec_eq_smul_iff (νA νB J : ℝ) (E : ℂ) (v : Fin 2 × Fin 2 → ℂ) :
    abHamiltonian νA νB J *ᵥ v = E • v ↔
      (((-(νA + νB) / 2 + J / 4 : ℝ) : ℂ) - E) * v (0, 0) = 0 ∧
      (((-(νA - νB) / 2 - J / 4 : ℝ) : ℂ) - E) * v (0, 1) + ((J / 2 : ℝ) : ℂ) * v (1, 0) = 0 ∧
      ((J / 2 : ℝ) : ℂ) * v (0, 1) + ((((νA - νB) / 2 - J / 4 : ℝ) : ℂ) - E) * v (1, 0) = 0 ∧
      ((((νA + νB) / 2 + J / 4 : ℝ) : ℂ) - E) * v (1, 1) = 0 := by
  constructor
  · intro h
    have h00 := congrFun h (0, 0)
    have h01 := congrFun h (0, 1)
    have h10 := congrFun h (1, 0)
    have h11 := congrFun h (1, 1)
    rw [abHamiltonian_mulVec_alphaAlpha] at h00
    rw [abHamiltonian_mulVec_alphaBeta] at h01
    rw [abHamiltonian_mulVec_betaAlpha] at h10
    rw [abHamiltonian_mulVec_betaBeta] at h11
    simp only [Pi.smul_apply, smul_eq_mul] at h00 h01 h10 h11
    exact ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10,
      by linear_combination h11⟩
  · rintro ⟨h00, h01, h10, h11⟩
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [abHamiltonian_mulVec_alphaAlpha]
      linear_combination h00
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [abHamiltonian_mulVec_alphaBeta]
      linear_combination h01
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [abHamiltonian_mulVec_betaAlpha]
      linear_combination h10
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [abHamiltonian_mulVec_betaBeta]
      linear_combination h11

/-- `E` is an eigenvalue of `H`, as an endomorphism of `Fin 2 × Fin 2 → ℂ`, iff `H v = E v` has
a nonzero solution `v`. -/
lemma abHamiltonian_hasEigenvalue_iff_exists (νA νB J : ℝ) (E : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J)) E ↔
      ∃ v, v ≠ 0 ∧ abHamiltonian νA νB J *ᵥ v = E • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv.1
  · rintro ⟨v, hv0, hv⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [Matrix.toLin'_apply] using hv), hv0⟩

/-!

### E.2. Energy levels

-/

/-- Energy (Hz) of the state `αα`: `-(νA + νB) / 2 + J / 4`. -/
noncomputable def abEnergyAlphaAlpha (νA νB J : ℝ) : ℝ :=
  -(νA + νB) / 2 + J / 4

/-- Energy (Hz) of the state `ββ`: `(νA + νB) / 2 + J / 4`. -/
noncomputable def abEnergyBetaBeta (νA νB J : ℝ) : ℝ :=
  (νA + νB) / 2 + J / 4

/-- The upper of the two energies (Hz) of the mixed states, the eigenvectors of `H` spanned by
`αβ` and `βα`: `-J / 4 + √((νA - νB) ^ 2 + J ^ 2) / 2`. -/
noncomputable def abEnergyPlus (νA νB J : ℝ) : ℝ :=
  -J / 4 + Real.sqrt ((νA - νB) ^ 2 + J ^ 2) / 2

/-- The lower mixed-state energy (Hz): `-J / 4 - √((νA - νB) ^ 2 + J ^ 2) / 2`. -/
noncomputable def abEnergyMinus (νA νB J : ℝ) : ℝ :=
  -J / 4 - Real.sqrt ((νA - νB) ^ 2 + J ^ 2) / 2

/-- `(D / 2) ^ 2 = ((νA - νB) / 2) ^ 2 + (J / 2) ^ 2` for `D = √((νA - νB) ^ 2 + J ^ 2)`. -/
lemma ab_half_sqrt_sq (νA νB J : ℝ) :
    (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) / 2) ^ 2 = ((νA - νB) / 2) ^ 2 + (J / 2) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- `αα` is an eigenvector of `H` with energy `abEnergyAlphaAlpha`. -/
lemma abHamiltonian_hasEigenvalue_alphaAlpha (νA νB J : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J))
      (abEnergyAlphaAlpha νA νB J) := by
  rw [abHamiltonian_hasEigenvalue_iff_exists]
  refine ⟨Pi.single (0, 0) 1, fun h0 => by simpa using congrFun h0 (0, 0), ?_⟩
  rw [abHamiltonian_mulVec_eq_smul_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [abEnergyAlphaAlpha]

/-- `ββ` is an eigenvector of `H` with energy `abEnergyBetaBeta`. -/
lemma abHamiltonian_hasEigenvalue_betaBeta (νA νB J : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J))
      (abEnergyBetaBeta νA νB J) := by
  rw [abHamiltonian_hasEigenvalue_iff_exists]
  refine ⟨Pi.single (1, 1) 1, fun h0 => by simpa using congrFun h0 (1, 1), ?_⟩
  rw [abHamiltonian_mulVec_eq_smul_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [abEnergyBetaBeta]

/-- The upper mixed state is an eigenvector of `H` with energy `abEnergyPlus`: with
`a = (νA - νB) / 2`, `b = J / 2` and `r = √(a ^ 2 + b ^ 2)`, it is `b αβ + (r + a) βα`, or `αβ`
when that vector vanishes. -/
lemma abHamiltonian_hasEigenvalue_plus (νA νB J : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J))
      (abEnergyPlus νA νB J) := by
  set a : ℝ := (νA - νB) / 2 with ha
  set b : ℝ := J / 2 with hb
  set r : ℝ := Real.sqrt ((νA - νB) ^ 2 + J ^ 2) / 2 with hr
  have hr2C : (r : ℂ) ^ 2 = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    exact_mod_cast ab_half_sqrt_sq νA νB J
  have h : ((abEnergyPlus νA νB J : ℝ) : ℂ) = -J / 4 + r := by
    simp only [abEnergyPlus, hr]; push_cast; ring
  have hcast01 : ((((-(νA - νB)) / 2 - J / 4 : ℝ) : ℂ)) = -(a : ℂ) - J / 4 := by
    rw [ha]; push_cast; ring
  have hcast10 : ((((νA - νB) / 2 - J / 4 : ℝ) : ℂ)) = (a : ℂ) - J / 4 := by
    rw [ha]; push_cast; ring
  rw [abHamiltonian_hasEigenvalue_iff_exists]
  by_cases hcase : b = 0 ∧ r + a = 0
  · have hb0 : (b : ℂ) = 0 := by exact_mod_cast hcase.1
    have hra : (r : ℂ) + a = 0 := by exact_mod_cast hcase.2
    refine ⟨Pi.single (0, 1) 1, fun h0 => by simpa using congrFun h0 (0, 1), ?_⟩
    rw [abHamiltonian_mulVec_eq_smul_iff, hcast01, hcast10, ← hb]
    refine ⟨by simp, ?_, by simp [hb0], by simp⟩
    simp
    linear_combination -h - hra
  · refine ⟨Pi.single (0, 1) (b : ℂ) + Pi.single (1, 0) ((r : ℂ) + a), fun h0 => hcase ?_, ?_⟩
    · have h01 := congrFun h0 (0, 1)
      have h10 := congrFun h0 (1, 0)
      simp only [Fin.isValue, Pi.add_apply, Pi.single_eq_same, ne_eq, Prod.mk.injEq,
        zero_ne_one, one_ne_zero, and_self, not_false_eq_true, Pi.single_eq_of_ne, add_zero,
        Pi.zero_apply, zero_add, Complex.ofReal_eq_zero] at h01 h10
      exact ⟨h01, by exact_mod_cast h10⟩
    · rw [abHamiltonian_mulVec_eq_smul_iff, hcast01, hcast10, ← hb]
      refine ⟨by simp, ?_, ?_, by simp⟩
      · simp
        linear_combination -(b : ℂ) * h
      · simp
        linear_combination (-(r : ℂ) - a) * h - hr2C

/-- The lower mixed state is an eigenvector of `H` with energy `abEnergyMinus`: with
`a = (νA - νB) / 2`, `b = J / 2` and `r = √(a ^ 2 + b ^ 2)`, it is `(r + a) αβ - b βα`, or `βα`
when that vector vanishes. -/
lemma abHamiltonian_hasEigenvalue_minus (νA νB J : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J))
      (abEnergyMinus νA νB J) := by
  set a : ℝ := (νA - νB) / 2 with ha
  set b : ℝ := J / 2 with hb
  set r : ℝ := Real.sqrt ((νA - νB) ^ 2 + J ^ 2) / 2 with hr
  have hr2C : (r : ℂ) ^ 2 = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    exact_mod_cast ab_half_sqrt_sq νA νB J
  have h : ((abEnergyMinus νA νB J : ℝ) : ℂ) = -J / 4 - r := by
    simp only [abEnergyMinus, hr]; push_cast; ring
  have hcast01 : ((((-(νA - νB)) / 2 - J / 4 : ℝ) : ℂ)) = -(a : ℂ) - J / 4 := by
    rw [ha]; push_cast; ring
  have hcast10 : ((((νA - νB) / 2 - J / 4 : ℝ) : ℂ)) = (a : ℂ) - J / 4 := by
    rw [ha]; push_cast; ring
  rw [abHamiltonian_hasEigenvalue_iff_exists]
  by_cases hcase : b = 0 ∧ r + a = 0
  · have hb0 : (b : ℂ) = 0 := by exact_mod_cast hcase.1
    have hra : (r : ℂ) + a = 0 := by exact_mod_cast hcase.2
    refine ⟨Pi.single (1, 0) 1, fun h0 => by simpa using congrFun h0 (1, 0), ?_⟩
    rw [abHamiltonian_mulVec_eq_smul_iff, hcast01, hcast10, ← hb]
    refine ⟨by simp, by simp [hb0], ?_, by simp⟩
    simp
    linear_combination hra - h
  · refine ⟨Pi.single (0, 1) ((r : ℂ) + a) + Pi.single (1, 0) (-(b : ℂ)), fun h0 => hcase ?_,
      ?_⟩
    · have h01 := congrFun h0 (0, 1)
      have h10 := congrFun h0 (1, 0)
      simp only [Fin.isValue, Pi.add_apply, Pi.single_eq_same, ne_eq, Prod.mk.injEq,
        zero_ne_one, one_ne_zero, and_self, not_false_eq_true, Pi.single_eq_of_ne, add_zero,
        Pi.zero_apply, zero_add, neg_eq_zero, Complex.ofReal_eq_zero] at h01 h10
      exact ⟨h10, by exact_mod_cast h01⟩
    · rw [abHamiltonian_mulVec_eq_smul_iff, hcast01, hcast10, ← hb]
      refine ⟨by simp, ?_, ?_, by simp⟩
      · simp
        linear_combination hr2C - ((r : ℂ) + a) * h
      · simp
        linear_combination (b : ℂ) * h

/-- Every eigenvalue of `H` is one of the four energies: an eigenvector with a nonzero `αα` or
`ββ` component forces `abEnergyAlphaAlpha` or `abEnergyBetaBeta`; otherwise it lies in the
mixed subspace, where `E` solves `(E + J / 4) ^ 2 = ((νA - νB) ^ 2 + J ^ 2) / 4`. -/
lemma abHamiltonian_eigenvalue_cases {νA νB J : ℝ} {E : ℂ}
    (hE : Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J)) E) :
    E = abEnergyAlphaAlpha νA νB J ∨ E = abEnergyPlus νA νB J ∨
      E = abEnergyMinus νA νB J ∨ E = abEnergyBetaBeta νA νB J := by
  set a : ℝ := (νA - νB) / 2 with ha
  set b : ℝ := J / 2 with hb
  set r : ℝ := Real.sqrt ((νA - νB) ^ 2 + J ^ 2) / 2 with hr
  have hr2C : (r : ℂ) ^ 2 = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    exact_mod_cast ab_half_sqrt_sq νA νB J
  obtain ⟨v, hv0, hv⟩ := (abHamiltonian_hasEigenvalue_iff_exists νA νB J E).mp hE
  obtain ⟨h00, h01, h10, h11⟩ := (abHamiltonian_mulVec_eq_smul_iff νA νB J E v).mp hv
  by_cases hv00 : v (0, 0) = 0
  swap
  · left
    have := (mul_eq_zero.mp h00).resolve_right hv00
    simp only [abEnergyAlphaAlpha]
    linear_combination -this
  by_cases hv11 : v (1, 1) = 0
  swap
  · right; right; right
    have := (mul_eq_zero.mp h11).resolve_right hv11
    simp only [abEnergyBetaBeta]
    linear_combination -this
  right
  have hmix : v (0, 1) ≠ 0 ∨ v (1, 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · simpa using hv00
    · simpa using hcon.1
    · simpa using hcon.2
    · simpa using hv11
  have hcast01 : ((((-(νA - νB)) / 2 - J / 4 : ℝ) : ℂ)) = -(a : ℂ) - J / 4 := by
    rw [ha]; push_cast; ring
  have hcast10 : ((((νA - νB) / 2 - J / 4 : ℝ) : ℂ)) = (a : ℂ) - J / 4 := by
    rw [ha]; push_cast; ring
  rw [hcast01, ← hb] at h01
  rw [hcast10, ← hb] at h10
  have hq : ((E + J / 4) - r) * ((E + J / 4) + r) = 0 := by
    rcases hmix with h | h
    · have key : (((E + J / 4) - r) * ((E + J / 4) + r)) * v (0, 1) = 0 := by
        linear_combination ((a : ℂ) - J / 4 - E) * h01 - (b : ℂ) * h10 - v (0, 1) * hr2C
      exact (mul_eq_zero.mp key).resolve_right h
    · have key : (((E + J / 4) - r) * ((E + J / 4) + r)) * v (1, 0) = 0 := by
        linear_combination (-(b : ℂ)) * h01 + (-(a : ℂ) - J / 4 - E) * h10 - v (1, 0) * hr2C
      exact (mul_eq_zero.mp key).resolve_right h
  rcases mul_eq_zero.mp hq with h | h
  · left
    simp only [abEnergyPlus, ← hr]
    push_cast
    linear_combination h
  · right; left
    simp only [abEnergyMinus, ← hr]
    push_cast
    linear_combination h

/-- The energy levels of the AB system: `E` is an eigenvalue of the two-spin Hamiltonian `H` iff
it is one of `abEnergyAlphaAlpha`, `abEnergyPlus`, `abEnergyMinus` and `abEnergyBetaBeta`. -/
theorem abHamiltonian_hasEigenvalue_iff (νA νB J : ℝ) (E : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian νA νB J)) E ↔
      E = abEnergyAlphaAlpha νA νB J ∨ E = abEnergyPlus νA νB J ∨
        E = abEnergyMinus νA νB J ∨ E = abEnergyBetaBeta νA νB J := by
  refine ⟨abHamiltonian_eigenvalue_cases, ?_⟩
  rintro (rfl | rfl | rfl | rfl)
  · exact abHamiltonian_hasEigenvalue_alphaAlpha νA νB J
  · exact abHamiltonian_hasEigenvalue_plus νA νB J
  · exact abHamiltonian_hasEigenvalue_minus νA νB J
  · exact abHamiltonian_hasEigenvalue_betaBeta νA νB J

/-!

### E.3. The mixed-state block

On the mixed states `βα`, `αβ` (in that order) the Hamiltonian is the `2 × 2` matrix
`abMixingMatrix` minus the scalar `(νA + νB) / 2 + J / 4`. Its eigenvalues `abMixingEigenPlus`,
`abMixingEigenMinus` are the two mixed-state energies plus that scalar; they are not transition
frequencies.

-/

/-- The mixed states `βα = (1, 0)` and `αβ = (0, 1)`, indexed by `Fin 2` in that order. -/
def abMixedState : Fin 2 → Fin 2 × Fin 2 :=
  ![(1, 0), (0, 1)]

/-- The `2 × 2` matrix `!![νA, J / 2; J / 2, νB]`. By `abHamiltonian_submatrix_mixed` it is the
block of `abHamiltonian` on the mixed states `βα`, `αβ` plus the scalar
`(νA + νB) / 2 + J / 4`; it is not itself a Hamiltonian of the AB system. -/
noncomputable def abMixingMatrix (νA νB J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![νA, J / 2; J / 2, νB]

/-- The block of the AB Hamiltonian on the mixed states is `abMixingMatrix` minus the scalar
`(νA + νB) / 2 + J / 4`. -/
lemma abHamiltonian_submatrix_mixed (νA νB J : ℝ) :
    (abHamiltonian νA νB J).submatrix abMixedState abMixedState =
      (abMixingMatrix νA νB J - ((νA + νB) / 2 + J / 4) • 1).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [abHamiltonian, abMixingMatrix, abMixedState, Fin.sum_univ_three,
      PauliMatrix.pauliMatrix] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- Upper eigenvalue of `abMixingMatrix`:
`(νA + νB) / 2 + (1 / 2) * √((νA - νB) ^ 2 + J ^ 2)`. -/
noncomputable def abMixingEigenPlus (νA νB J : ℝ) : ℝ :=
  (νA + νB) / 2 + (1 / 2) * Real.sqrt ((νA - νB) ^ 2 + J ^ 2)

/-- Lower eigenvalue of `abMixingMatrix`:
`(νA + νB) / 2 - (1 / 2) * √((νA - νB) ^ 2 + J ^ 2)`. -/
noncomputable def abMixingEigenMinus (νA νB J : ℝ) : ℝ :=
  (νA + νB) / 2 - (1 / 2) * Real.sqrt ((νA - νB) ^ 2 + J ^ 2)

/-- The upper value satisfies the characteristic equation of `abMixingMatrix`,
`det (M - λ • 1) = 0`. -/
lemma ab_det_plus (νA νB J : ℝ) :
    Matrix.det (abMixingMatrix νA νB J - abMixingEigenPlus νA νB J • 1) = 0 := by
  have hD : (0 : ℝ) ≤ (νA - νB) ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt ((νA - νB) ^ 2 + J ^ 2)) ^ 2 =
      (νA - νB) ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  have hM : abMixingMatrix νA νB J - abMixingEigenPlus νA νB J • 1 =
      !![νA - abMixingEigenPlus νA νB J, J / 2; J / 2, νB - abMixingEigenPlus νA νB J] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [abMixingMatrix, show (0 : Fin 2) ≠ 1 from by decide,
        show (1 : Fin 2) ≠ 0 from by decide]
  rw [hM, Matrix.det_fin_two_of]
  simp only [abMixingEigenPlus]
  linear_combination (1 / 4 : ℝ) * hsq

/-- The lower value satisfies the characteristic equation of `abMixingMatrix`,
`det (M - λ • 1) = 0`. -/
lemma ab_det_minus (νA νB J : ℝ) :
    Matrix.det (abMixingMatrix νA νB J - abMixingEigenMinus νA νB J • 1) = 0 := by
  have hD : (0 : ℝ) ≤ (νA - νB) ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt ((νA - νB) ^ 2 + J ^ 2)) ^ 2 =
      (νA - νB) ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  have hM : abMixingMatrix νA νB J - abMixingEigenMinus νA νB J • 1 =
      !![νA - abMixingEigenMinus νA νB J, J / 2; J / 2, νB - abMixingEigenMinus νA νB J] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [abMixingMatrix, show (0 : Fin 2) ≠ 1 from by decide,
        show (1 : Fin 2) ≠ 0 from by decide]
  rw [hM, Matrix.det_fin_two_of]
  simp only [abMixingEigenMinus]
  linear_combination (1 / 4 : ℝ) * hsq

/-- Trace matching: the two eigenvalues of `abMixingMatrix` sum to `νA + νB`. Together with
`ab_eigen_prod` this is the provable form of `(X - λ₁)(X - λ₂)` equaling the
characteristic polynomial for the 2x2 case. -/
lemma ab_eigen_sum (νA νB J : ℝ) :
    abMixingEigenPlus νA νB J + abMixingEigenMinus νA νB J = νA + νB := by
  simp only [abMixingEigenPlus, abMixingEigenMinus]
  ring

/-- Determinant matching: the product of the two eigenvalues of `abMixingMatrix` equals
`νA * νB - (J / 2) ^ 2`. -/
lemma ab_eigen_prod (νA νB J : ℝ) :
    abMixingEigenPlus νA νB J * abMixingEigenMinus νA νB J =
      νA * νB - (J / 2) ^ 2 := by
  have hD : (0 : ℝ) ≤ (νA - νB) ^ 2 + J ^ 2 := by positivity
  have hsq : (Real.sqrt ((νA - νB) ^ 2 + J ^ 2)) ^ 2 =
      (νA - νB) ^ 2 + J ^ 2 :=
    Real.sq_sqrt hD
  simp only [abMixingEigenPlus, abMixingEigenMinus]
  linear_combination (-1 / 4 : ℝ) * hsq

/-- The mixed-state energies are the eigenvalues of `abMixingMatrix` minus the scalar
`(νA + νB) / 2 + J / 4`. -/
lemma abEnergyPlus_eq_abMixingEigenPlus (νA νB J : ℝ) :
    abEnergyPlus νA νB J = abMixingEigenPlus νA νB J - ((νA + νB) / 2 + J / 4) ∧
      abEnergyMinus νA νB J = abMixingEigenMinus νA νB J - ((νA + νB) / 2 + J / 4) := by
  constructor <;>
    simp only [abEnergyPlus, abEnergyMinus, abMixingEigenPlus, abMixingEigenMinus] <;> ring

/-!

### E.4. Candidate transitions and the weak-coupling limit

The candidate transitions are the four between `αα` or `ββ` (total magnetic quantum number
`M = 1` or `-1`) and the two mixed states (`M = 0`); the selection rule `ΔM = ±1` that leaves
only these is a model assumption here. Each candidate flips one spin from `α` to `β`. Its signed
transition offset (`abOffsetAlphaMinus`, ...) is the energy change `E(final) - E(initial)` in Hz,
and its line frequency (`abGapAlphaMinus`, ...) is the absolute energy gap
`|E(final) - E(initial)|`, by `ν = ΔE / h`. The offsets can be negative, for example for
frequencies measured from a carrier; when both resonance frequencies exceed `|J|` they are
positive and equal the line frequencies (`abGaps_eq_offsets`).

Transition moments are not formalized, and a candidate is an observed line only if its transition
moment is nonzero. For `J ≠ 0` all four candidates are observed only when `νA ≠ νB`: at
`νA = νB = ν0` the two at `ν0 ± J` (`abOffsets_self`) have zero transition moment, leaving the
single line `ν0` of the `A₂` spectrum.

-/

/-- Signed transition offset (Hz) of the candidate transition from `αα` to the lower mixed state:
`abEnergyMinus - abEnergyAlphaAlpha`. It can be negative; its absolute value is the line
frequency `abGapAlphaMinus`. -/
noncomputable def abOffsetAlphaMinus (νA νB J : ℝ) : ℝ :=
  abEnergyMinus νA νB J - abEnergyAlphaAlpha νA νB J

/-- Signed transition offset (Hz) of the candidate transition from `αα` to the upper mixed state:
`abEnergyPlus - abEnergyAlphaAlpha`. It can be negative; its absolute value is the line
frequency `abGapAlphaPlus`. -/
noncomputable def abOffsetAlphaPlus (νA νB J : ℝ) : ℝ :=
  abEnergyPlus νA νB J - abEnergyAlphaAlpha νA νB J

/-- Signed transition offset (Hz) of the candidate transition from the upper mixed state to `ββ`:
`abEnergyBetaBeta - abEnergyPlus`. It can be negative; its absolute value is the line
frequency `abGapPlusBeta`. -/
noncomputable def abOffsetPlusBeta (νA νB J : ℝ) : ℝ :=
  abEnergyBetaBeta νA νB J - abEnergyPlus νA νB J

/-- Signed transition offset (Hz) of the candidate transition from the lower mixed state to `ββ`:
`abEnergyBetaBeta - abEnergyMinus`. It can be negative; its absolute value is the line
frequency `abGapMinusBeta`. -/
noncomputable def abOffsetMinusBeta (νA νB J : ℝ) : ℝ :=
  abEnergyBetaBeta νA νB J - abEnergyMinus νA νB J

/-- Line frequency (Hz) of the candidate transition between `αα` and the lower mixed state: the
absolute energy gap `|abEnergyMinus - abEnergyAlphaAlpha|`. -/
noncomputable def abGapAlphaMinus (νA νB J : ℝ) : ℝ :=
  |abEnergyMinus νA νB J - abEnergyAlphaAlpha νA νB J|

/-- Line frequency (Hz) of the candidate transition between `αα` and the upper mixed state: the
absolute energy gap `|abEnergyPlus - abEnergyAlphaAlpha|`. -/
noncomputable def abGapAlphaPlus (νA νB J : ℝ) : ℝ :=
  |abEnergyPlus νA νB J - abEnergyAlphaAlpha νA νB J|

/-- Line frequency (Hz) of the candidate transition between the upper mixed state and `ββ`: the
absolute energy gap `|abEnergyBetaBeta - abEnergyPlus|`. -/
noncomputable def abGapPlusBeta (νA νB J : ℝ) : ℝ :=
  |abEnergyBetaBeta νA νB J - abEnergyPlus νA νB J|

/-- Line frequency (Hz) of the candidate transition between the lower mixed state and `ββ`: the
absolute energy gap `|abEnergyBetaBeta - abEnergyMinus|`. -/
noncomputable def abGapMinusBeta (νA νB J : ℝ) : ℝ :=
  |abEnergyBetaBeta νA νB J - abEnergyMinus νA νB J|

/-- The signed offsets of the four candidate transitions: with `D = √((νA - νB) ^ 2 + J ^ 2)`,
they are `(νA + νB) / 2 ± (D + J) / 2` and `(νA + νB) / 2 ± (D - J) / 2`. -/
theorem abOffsets_eq (νA νB J : ℝ) :
    abOffsetAlphaMinus νA νB J =
      (νA + νB) / 2 - (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) + J) / 2 ∧
    abOffsetAlphaPlus νA νB J =
      (νA + νB) / 2 + (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) - J) / 2 ∧
    abOffsetPlusBeta νA νB J =
      (νA + νB) / 2 - (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) - J) / 2 ∧
    abOffsetMinusBeta νA νB J =
      (νA + νB) / 2 + (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) + J) / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [abOffsetAlphaMinus, abOffsetAlphaPlus, abOffsetPlusBeta, abOffsetMinusBeta,
      abEnergyAlphaAlpha, abEnergyBetaBeta, abEnergyPlus, abEnergyMinus] <;> ring

/-- Equivalent shifts (`A₂`): at `νA = νB = ν0` with `J ≥ 0` the four candidate offsets are
`ν0 - J`, `ν0`, `ν0` and `ν0 + J`. For `J > 0` the outer two involve the lower mixed state, which
is then the antisymmetric singlet `αβ - βα`; their transition moments vanish (not formalized
here), so the observed spectrum is the single line `ν0`, not four lines. For `J < 0` the two
mixed states exchange roles. -/
lemma abOffsets_self (ν0 J : ℝ) (hJ : 0 ≤ J) :
    abOffsetAlphaMinus ν0 ν0 J = ν0 - J ∧ abOffsetAlphaPlus ν0 ν0 J = ν0 ∧
      abOffsetPlusBeta ν0 ν0 J = ν0 ∧ abOffsetMinusBeta ν0 ν0 J = ν0 + J := by
  have hD : Real.sqrt ((ν0 - ν0) ^ 2 + J ^ 2) = J := by simp [Real.sqrt_sq hJ]
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_eq ν0 ν0 J
  rw [hD] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; ring
  · rw [h2]; ring
  · rw [h3]; ring
  · rw [h4]; ring

/-- When both resonance frequencies exceed `|J|` (as lab-frame NMR frequencies do), all four
signed transition offsets are positive. -/
lemma abOffsets_pos (νA νB J : ℝ) (hA : |J| < νA) (hB : |J| < νB) :
    0 < abOffsetAlphaMinus νA νB J ∧ 0 < abOffsetAlphaPlus νA νB J ∧
      0 < abOffsetPlusBeta νA νB J ∧ 0 < abOffsetMinusBeta νA νB J := by
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_eq νA νB J
  have hJD : |J| ≤ Real.sqrt ((νA - νB) ^ 2 + J ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hDle : Real.sqrt ((νA - νB) ^ 2 + J ^ 2) ≤ |νA - νB| + |J| := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |νA - νB| + |J|)]
    exact Real.sqrt_le_sqrt (by
      nlinarith [sq_abs (νA - νB), sq_abs J, mul_nonneg (abs_nonneg (νA - νB)) (abs_nonneg J)])
  have hAB : |νA - νB| < νA + νB - 2 * |J| := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hJ := le_abs_self J
  have hJ' := neg_abs_le J
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; linarith
  · rw [h2]; linarith
  · rw [h3]; linarith
  · rw [h4]; linarith

/-- When both resonance frequencies exceed `|J|`, each line frequency equals the signed offset
of its candidate transition. -/
lemma abGaps_eq_offsets (νA νB J : ℝ) (hA : |J| < νA) (hB : |J| < νB) :
    abGapAlphaMinus νA νB J = abOffsetAlphaMinus νA νB J ∧
      abGapAlphaPlus νA νB J = abOffsetAlphaPlus νA νB J ∧
      abGapPlusBeta νA νB J = abOffsetPlusBeta νA νB J ∧
      abGapMinusBeta νA νB J = abOffsetMinusBeta νA νB J := by
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_pos νA νB J hA hB
  exact ⟨abs_of_pos h1, abs_of_pos h2, abs_of_pos h3, abs_of_pos h4⟩

/-- The four AB line frequencies: when both resonance frequencies exceed `|J|`, with
`D = √((νA - νB) ^ 2 + J ^ 2)`, they are `(νA + νB) / 2 ± (D + J) / 2` and
`(νA + νB) / 2 ± (D - J) / 2`. -/
theorem abGaps_eq (νA νB J : ℝ) (hA : |J| < νA) (hB : |J| < νB) :
    abGapAlphaMinus νA νB J = (νA + νB) / 2 - (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) + J) / 2 ∧
    abGapAlphaPlus νA νB J = (νA + νB) / 2 + (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) - J) / 2 ∧
    abGapPlusBeta νA νB J = (νA + νB) / 2 - (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) - J) / 2 ∧
    abGapMinusBeta νA νB J = (νA + νB) / 2 + (Real.sqrt ((νA - νB) ^ 2 + J ^ 2) + J) / 2 := by
  obtain ⟨g1, g2, g3, g4⟩ := abGaps_eq_offsets νA νB J hA hB
  rw [g1, g2, g3, g4]
  exact abOffsets_eq νA νB J

/-- First-order limit: for `Δν ≠ 0`,
`|√(Δν ^ 2 + J ^ 2) - |Δν|| ≤ J ^ 2 / (2 * |Δν|)`. With `Δν = νA - νB` this bounds how far
the AB transition offsets are from their first-order positions (`abOffsets_weakCoupling`). -/
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

/-- Weak-coupling limit of the AB transition offsets: when `νA ≠ νB`, the offsets of `− → ββ`
and `αα → +` lie within `J ^ 2 / (4 |νA - νB|)` of the first-order doublet `max νA νB ± J / 2`
of the nucleus with the larger resonance frequency, and those of `+ → ββ` and `αα → −` within
the same bound of the doublet `min νA νB ± J / 2` of the other one. -/
lemma abOffsets_weakCoupling (νA νB J : ℝ) (h : νA ≠ νB) :
    |abOffsetMinusBeta νA νB J - (max νA νB + J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) ∧
    |abOffsetAlphaPlus νA νB J - (max νA νB - J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) ∧
    |abOffsetPlusBeta νA νB J - (min νA νB + J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) ∧
    |abOffsetAlphaMinus νA νB J - (min νA νB - J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) := by
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_eq νA νB J
  have hlim := ab_first_order_limit (νA - νB) J (sub_ne_zero.mpr h)
  have hmax : max νA νB = (νA + νB) / 2 + |νA - νB| / 2 := by
    rcases le_total νA νB with hle | hle
    · rw [max_eq_right hle, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left hle, abs_of_nonneg (by linarith)]; ring
  have hmin : min νA νB = (νA + νB) / 2 - |νA - νB| / 2 := by
    rcases le_total νA νB with hle | hle
    · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring
  rw [hmax, hmin, h1, h2, h3, h4]
  set D := Real.sqrt ((νA - νB) ^ 2 + J ^ 2)
  set d := |νA - νB|
  have hbound : |D - d| / 2 ≤ J ^ 2 / (4 * d) := by
    have h4 : J ^ 2 / (4 * d) = J ^ 2 / (2 * d) / 2 := by
      rw [div_div]; ring_nf
    rw [h4]
    exact div_le_div_of_nonneg_right hlim (by norm_num)
  have e1 : |D - d| / 2 = |(D - d) / 2| := by rw [abs_div, abs_two]
  have e2 : |D - d| / 2 = |-((D - d) / 2)| := by rw [abs_neg, abs_div, abs_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc _ = |(D - d) / 2| := by congr 1; ring
      _ ≤ _ := e1 ▸ hbound
  · calc _ = |(D - d) / 2| := by congr 1; ring
      _ ≤ _ := e1 ▸ hbound
  · calc _ = |-((D - d) / 2)| := by congr 1; ring
      _ ≤ _ := e2 ▸ hbound
  · calc _ = |-((D - d) / 2)| := by congr 1; ring
      _ ≤ _ := e2 ▸ hbound

/-- Weak-coupling limit of the AB line frequencies: when both resonance frequencies exceed `|J|`
and `νA ≠ νB`, each line frequency obeys the bound of `abOffsets_weakCoupling`. -/
lemma abGaps_weakCoupling (νA νB J : ℝ) (hA : |J| < νA) (hB : |J| < νB) (h : νA ≠ νB) :
    |abGapMinusBeta νA νB J - (max νA νB + J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) ∧
    |abGapAlphaPlus νA νB J - (max νA νB - J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) ∧
    |abGapPlusBeta νA νB J - (min νA νB + J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) ∧
    |abGapAlphaMinus νA νB J - (min νA νB - J / 2)| ≤ J ^ 2 / (4 * |νA - νB|) := by
  obtain ⟨g1, g2, g3, g4⟩ := abGaps_eq_offsets νA νB J hA hB
  rw [g1, g2, g3, g4]
  exact abOffsets_weakCoupling νA νB J h

end Chemistry.QuantitativeNMR
