/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import MathlibExt.InformationTheory.LogSum
public import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
/-!

# Finite-state ensembles and partition functions

The canonical ensemble of a finite system: partition function, Boltzmann probabilities, maximum
entropy, thermodynamic functions, independent subsystems, a two-level system and Einstein solids.

## i. Overview

A system has a finite nonempty type `ι` of states (`Fintype ι`, `Nonempty ι`) with energies
`E : ι → ℝ`; a lemma whose proof needs `0 < Z` assumes `Nonempty ι` or derives it from
`∑ i, p i = 1`. The inverse temperature `β` is a real parameter, and the Boltzmann constant `kB`
is a symbolic parameter with `0 < kB`; no numerical value is fixed. The temperature
`T = 1 / (kB * β)` is a definition (`temperature`), not a new constant. Every sum is a finite sum
over a `Fintype`; infinite state spaces appear nowhere.

The canonical distribution `p i = exp (-β * E i) / Z` is a postulate: it models a system in
contact with a reservoir, from equal a priori probabilities of their joint microstates. It is not
derived here, in particular not from the CH11 equilibrium postulates. The predicate
`IsCanonical p E β`, that is `p = boltzmannProb E β`, records it as a hypothesis. Everything else
is a mathematical statement about finite sums, proved here. In the claim classification of the
source, the postulate is MOD and the finite-state identities are MC.

Physical temperatures have `0 < β`. A lemma that uses `0 < β` or `0 < kB` assumes it explicitly;
these are the lemmas on the temperature `T`, on `A = U - T S` and `A = -kB T log Z`, on
`C = Var(E) / (kB T ^ 2)` and on the sign of the heat capacity. The other identities are stated
for every real `β`, since their proofs do not use its sign; their physical reading is at `0 < β`.

The Shannon entropy is `H(p) = -∑ i, p i * log (p i)`, with Mathlib's convention `log 0 = 0`.
Gibbs' inequality `0 ≤ ∑ i, p i * log (p i / q i)` for probability distributions `p` and `q` with
`0 < q i` holds with equality exactly when `p = q`. With the Lagrange-multiplier form
`log (p i) = -β * E i - log Z` of the Boltzmann probabilities, it shows that among the probability
distributions with the mean energy of the Boltzmann distribution, the Boltzmann distribution has
the largest entropy and is the only one with that entropy. No optimization principle is assumed.

The thermodynamic functions are the mean energy `U`, the energy variance `Var(E)`, the Helmholtz
free energy `A = -(log Z) / β`, the entropy `S = kB * (log Z + β * U)` and the heat capacity
`C = kB * β ^ 2 * Var(E)`. They satisfy `S = kB * H(p)`, `A = U - T S`, `A = -kB T log Z`,
`d(log Z)/dβ = -U`, `dU/dβ = -Var(E)`, `C = -kB * β ^ 2 * dU/dβ` and `0 ≤ C`; the derivatives are
`HasDerivAt` statements for finite sums of exponentials. `A = U - T S` is the consistency with
the Legendre structure of CH14; no CH14 definition is imported or claimed.

For independent subsystems with energy `E (i, j) = E₁ i + E₂ j` on `ι × κ`, the partition
functions and the Boltzmann probabilities multiply and the mean energies add. Ensembles are
compared only for such explicit ideal models: these product identities are the only statements of
ensemble-equivalence type here.

The CHEM-C5 worked example is the two-level system with energies `0` and `Δ > 0` at
`β * Δ = log 3`: `Z = 4 / 3`, the excited state has probability `1 / 4`, `U = Δ / 4`,
`Var(E) = 3 * Δ ^ 2 / 16` and `C = kB * (3 * (log 3) ^ 2 / 16)`.

The microstates of an Einstein solid with `N` oscillators and `q` quanta are the functions
`f : Fin N → ℕ` with `∑ i, f i = q`; there are `(N + q - 1).choose q` of them. Stirling's formula
is asymptotic only and is used nowhere here, in particular never as an equality: at `n = 2` its
value `2 ^ (2 + 1 / 2) * exp (-2) * √(2 * π)` is strictly smaller than `2! = 2`.

Reuse was checked against Mathlib, Physlib and ATLAS main. Mathlib has no partition function and
no finite-sum Gibbs inequality; for relative entropy it has the measure-theoretic
`InformationTheory.klDiv` (`InformationTheory.klDiv_eq_zero_iff`) and the pointwise
`InformationTheory.klFun` (`InformationTheory.klFun_nonneg`,
`InformationTheory.klFun_eq_zero_iff`). Gibbs' inequality is the case `∑ i, p i = ∑ i, q i = 1`
of ATLAS's log-sum inequality `Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div`; its equality case
is proved here from the strict bound `mul_log_div_lt_sub`. ATLAS's
`InformationTheory.shannonEntropy` is the entropy in bits of a `PMF`, with Gibbs' inequality
`InformationTheory.shannonEntropy_le_crossEntropy`; `shannonEntropy` here is the real-valued
entropy in nats of the source. ATLAS's `StatMech.Ising.Z β E`
(`PhyslibExt.CondensedMatter.IsingModel.Pressure`) is the sum `partitionFunction E β` with the
arguments swapped, and `StatMech.Ising.Z_pos` and `StatMech.Ising.Z_prod` are the analogs of
`partitionFunction_pos` and `partitionFunction_combinedEnergy`; the Ising `StatMech.Ising.isingZ`
and `StatMech.Ising.isingProb` unfold to `partitionFunction` and `boltzmannProb` of the Ising
Hamiltonian. The source fixes `partitionFunction E β`, and that Ising module is not imported here.

The definitions are the elementary finite-sum forms of the canonical-ensemble API
`Physlib.StatisticalMechanics.CanonicalEnsemble`, not a competing API. Section H
proves the three that Physlib states in β-real form (`Z`, `p`, `U`) equal to
Physlib's `mathematicalPartitionFunctionBetaReal`, `probabilityBetaReal` and
`meanEnergyBetaReal` for the counting-measure ensemble `canonicalEnsemble E`.
The Atlas definitions stay finite-sum and universe-polymorphic (`ι : Type*`):
Physlib's `CanonicalEnsemble` is over `ι : Type` with `MeasurableSpace` and
`MeasurableSingletonClass` instances, and Physlib provides no β-real
energy-variance, entropy, Helmholtz or heat-capacity definitions, so those
results stay in finite-sum form:

- `partitionFunction` is `CanonicalEnsemble.mathematicalPartitionFunction` on a finite type
  (`CanonicalEnsemble.mathematicalPartitionFunction_of_fintype`,
  `CanonicalEnsemble.partitionFunction_of_fintype`); as a function of `β` it is
  `CanonicalEnsemble.mathematicalPartitionFunctionBetaReal`, and `partitionFunction_pos` and
  `hasDerivAt_partitionFunction` are `CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos`
  and `CanonicalEnsemble.deriv_mathematicalPartitionFunctionBetaReal`.
- `boltzmannProb` is `CanonicalEnsemble.probability` (`CanonicalEnsemble.probabilityBetaReal`);
  `boltzmannProb_pos`, `boltzmannProb_nonneg`, `sum_boltzmannProb_eq_one` and `log_boltzmannProb`
  are `CanonicalEnsemble.probability_pos`, `CanonicalEnsemble.probability_nonneg_finite`,
  `CanonicalEnsemble.sum_probability_eq_one` and `CanonicalEnsemble.log_probability`.
- `kB * shannonEntropy (boltzmannProb E β)` is `CanonicalEnsemble.shannonEntropy`, equal to the
  thermodynamic entropy by `CanonicalEnsemble.thermodynamicEntropy_eq_shannonEntropy`, and
  `entropy` is the form of
  `CanonicalEnsemble.differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ`.
- `meanEnergy` is `CanonicalEnsemble.meanEnergy` on a finite type
  (`CanonicalEnsemble.meanEnergy_of_fintype`, `CanonicalEnsemble.meanEnergyBetaReal`);
  `energyVariance` is `CanonicalEnsemble.energyVariance`, and
  `energyVariance_eq_sum_sub_meanEnergy_sq` is `CanonicalEnsemble.energyVariance_of_fintype`.
- `temperature` inverts Physlib's inverse temperature `Temperature.β = 1 / (kB * T)`
  (`CanonicalEnsemble.kB_mul_beta`).
- `helmholtzFreeEnergy` is `CanonicalEnsemble.helmholtzFreeEnergy`, and `A = U - T S` is
  `CanonicalEnsemble.helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy`.
- `deriv_log_partitionFunction` is `CanonicalEnsemble.meanEnergy_eq_neg_deriv_log_Z_of_beta`, and
  `deriv_meanEnergy` is `CanonicalEnsemble.deriv_meanEnergyBetaReal` (in the form
  `U ^ 2 - ∑ i, p i * E i ^ 2`) and, as a `derivWithin` at a positive `Temperature`,
  `CanonicalEnsemble.derivWithin_meanEnergy_Beta_eq_neg_variance`. `heatCapacity` is
  `CanonicalEnsemble.heatCapacity` through
  `CanonicalEnsemble.fluctuation_dissipation_theorem_finite`
  (`heatCapacity_eq_energyVariance_div`).
- `combinedEnergy E₁ E₂` is the energy of the sum of two ensembles
  (`CanonicalEnsemble.energy_add_apply`), and the product identities are the finite-sum forms of
  `CanonicalEnsemble.mathematicalPartitionFunction_add`, `CanonicalEnsemble.probability_add` and
  `CanonicalEnsemble.meanEnergy_add`.
- `twoLevelEnergy Δ` is the energy of `CanonicalEnsemble.twoState 0 Δ`.
- `IsCanonical` has no Physlib counterpart; Physlib defines the canonical probabilities directly.

Physlib's `kB` is the constant `Constants.kB` and its temperatures have type `Temperature`; here
`kB` and `β` are real parameters. New relative to Physlib are the maximum-entropy theorem, the
finite-sum product identities and the two-level worked example; the Einstein-solid count
transports Mathlib's `Sym.card_sym_eq_choose` along `Sym.equivNatSumOfFintype`. Besides Mathlib,
this module imports Physlib's `CanonicalEnsemble.Finite` (for the §H bridge) and the landed
ATLAS module `MathlibExt.InformationTheory.LogSum`: no unlanded ATLAS module
(CH01, MF02, MF04, MF06).

## ii. Key results

- `partitionFunction`, `boltzmannProb` : `Z = ∑ i, exp (-β * E i)` and `p i = exp (-β * E i) / Z`.
- `partitionFunction_pos`, `boltzmannProb_pos`, `sum_boltzmannProb_eq_one` : `0 < Z`, `0 < p i`
  and `∑ i, p i = 1`.
- `log_boltzmannProb` : the Lagrange-multiplier form `log (p i) = -β * E i - log Z`.
- `sum_mul_log_div_nonneg`, `sum_mul_log_div_eq_zero_iff` : Gibbs' inequality and its equality
  case, and `sum_mul_log_div_boltzmannProb_nonneg`, `sum_mul_log_div_boltzmannProb_eq_zero_iff`
  relative to the Boltzmann distribution.
- `shannonEntropy_le_shannonEntropy_boltzmannProb`,
  `shannonEntropy_eq_shannonEntropy_boltzmannProb_iff` : at fixed mean energy the Boltzmann
  distribution maximizes the Shannon entropy, and is the only maximizer.
- `entropy_eq_mul_shannonEntropy` : `S = kB * H(p)`.
- `helmholtzFreeEnergy_eq_meanEnergy_sub_entropy_div`,
  `helmholtzFreeEnergy_eq_meanEnergy_sub_temperature_mul_entropy`,
  `helmholtzFreeEnergy_eq_neg_mul_temperature_mul_log` : `A = U - S / (kB * β)`, `A = U - T S`
  and `A = -kB T log Z`.
- `deriv_log_partitionFunction`, `deriv_meanEnergy` : `d(log Z)/dβ = -U` and `dU/dβ = -Var(E)`.
- `heatCapacity_eq_neg_mul_deriv_meanEnergy`, `heatCapacity_nonneg` : `C = -kB * β ^ 2 * dU/dβ`
  and `0 ≤ C`.
- `partitionFunction_combinedEnergy`, `boltzmannProb_combinedEnergy`,
  `meanEnergy_combinedEnergy` : independent subsystems multiply and add.
- `twoLevelEnergy_workedExample` : the CHEM-C5 two-level worked example.
- `card_sum_eq_choose` : the Einstein-solid count `(N + q - 1).choose q`.
- `stirling_two_lt_factorial`, `factorial_two_ne_stirling` : Stirling's formula is not exact at
  `n = 2`.
- `IsCanonical` : the canonical postulate as a predicate.
- `canonicalEnsemble`, `partitionFunction_eq_mathematicalPartitionFunctionBetaReal`,
  `boltzmannProb_eq_probabilityBetaReal`, `meanEnergy_eq_meanEnergyBetaReal` : the bridge
  to Physlib's β-real canonical-ensemble API.

## iii. Table of contents

- A. Partition function and Boltzmann distribution
- B. Entropy maximization
- C. Thermodynamic functions and fluctuations
- D. Independent subsystems
- E. Two-level system
- F. Einstein-solid counting and Stirling's formula
- G. The canonical postulate
- H. Bridge to Physlib's canonical-ensemble API

## iv. References

- MIT OpenCourseWare, 5.60 *Thermodynamics & Kinetics* (Spring 2008): the canonical
  distribution, partition functions and thermodynamic functions from `ln Z`.
- Physlib, `Physlib.StatisticalMechanics.CanonicalEnsemble` (`Basic`, `Finite`, `Lemmas` and
  `TwoState`), revision `af04d60b` (`v4.35.0`).

-/

@[expose] public section

namespace Chemistry.FiniteEnsembles

/-!

## A. Partition function and Boltzmann distribution

-/

/-- The partition function `Z = ∑ i, exp (-β * E i)` of a system with finitely many states,
energies `E` and inverse temperature `β`. -/
noncomputable def partitionFunction {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * E i)

/-- The partition function of a nonempty finite system is positive. The empty state space, with
partition function `0`, is excluded by `Nonempty ι`. -/
lemma partitionFunction_pos {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    0 < partitionFunction E β :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The Boltzmann probability `exp (-β * E i) / Z` of the state `i`. -/
noncomputable def boltzmannProb {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i) / partitionFunction E β

/-- Boltzmann probabilities are positive; the state `i` makes the state space nonempty. -/
lemma boltzmannProb_pos {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 < boltzmannProb E β i := by
  have : Nonempty ι := ⟨i⟩
  exact div_pos (Real.exp_pos _) (partitionFunction_pos E β)

/-- Boltzmann probabilities are nonnegative. -/
lemma boltzmannProb_nonneg {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ boltzmannProb E β i :=
  (boltzmannProb_pos E β i).le

/-- The Boltzmann probabilities of a nonempty finite system sum to `1`. -/
lemma sum_boltzmannProb_eq_one {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    ∑ i, boltzmannProb E β i = 1 := by
  simp only [boltzmannProb]
  rw [← Finset.sum_div]
  exact div_self (partitionFunction_pos E β).ne'

/-- The Lagrange-multiplier form `log (p i) = -β * E i - log Z` of the Boltzmann
probabilities. -/
lemma log_boltzmannProb {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    Real.log (boltzmannProb E β i) = -β * E i - Real.log (partitionFunction E β) := by
  have : Nonempty ι := ⟨i⟩
  rw [boltzmannProb, Real.log_div (Real.exp_pos _).ne' (partitionFunction_pos E β).ne',
    Real.log_exp]

/-!

## B. Entropy maximization

-/

/-- The Shannon entropy `H(p) = -∑ i, p i * log (p i)`. With Mathlib's convention
`Real.log 0 = 0`, a state with `p i = 0` contributes `0`. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- A function on a finite type with sum `1` has a nonempty domain. -/
lemma nonempty_of_sum_eq_one {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp1 : ∑ i, p i = 1) :
    Nonempty ι :=
  Finset.univ_nonempty_iff.mp (Finset.nonempty_of_sum_ne_zero (by rw [hp1]; exact one_ne_zero))

/-- The pointwise bound `p * log (q / p) ≤ q - p` for `0 ≤ p` and `0 < q`, from
`log x ≤ x - 1`. Rearranged, it is `0 ≤ q * InformationTheory.klFun (p / q)`. -/
lemma mul_log_div_le_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log (q / p) ≤ q - p := by
  rcases hp.eq_or_lt with h | h
  · rw [← h, zero_mul, sub_zero]
    exact hq.le
  · calc p * Real.log (q / p) ≤ p * (q / p - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq h)) h.le
      _ = q - p := by field_simp

/-- The bound `mul_log_div_le_sub` is strict for `p ≠ q`, from `log x < x - 1` for `x ≠ 1`. -/
lemma mul_log_div_lt_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≠ q) :
    p * Real.log (q / p) < q - p := by
  rcases hp.eq_or_lt with h | h
  · rw [← h, zero_mul, sub_zero]
    exact hq
  · have hx : q / p ≠ 1 := fun h' => hpq ((div_eq_one_iff_eq h.ne').mp h').symm
    calc p * Real.log (q / p) < p * (q / p - 1) :=
          mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hq h) hx) h
      _ = q - p := by field_simp

/-- For `∑ i, p i = 1` and `∑ i, q i = 1`, the relative entropy is the sum of the pointwise gaps
`q i - p i - p i * log (q i / p i)`. -/
lemma sum_mul_log_div_eq_sum_sub {ι : Type*} [Fintype ι] {p q : ι → ℝ} (hp1 : ∑ i, p i = 1)
    (hq1 : ∑ i, q i = 1) :
    ∑ i, p i * Real.log (p i / q i) = ∑ i, (q i - p i - p i * Real.log (q i / p i)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp1, hq1, sub_self, zero_sub,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inv_div (q i) (p i), Real.log_inv, mul_neg]

/-- **Gibbs' inequality.** For a probability distribution `p` (`0 ≤ p i`, `∑ i, p i = 1`) and a
probability distribution `q` with `0 < q i`, the relative entropy `∑ i, p i * log (p i / q i)` is
nonnegative. No support hypothesis on `p` is needed: a state with `p i = 0` contributes `0`. This
is the case `∑ i, p i = ∑ i, q i = 1` of the log-sum inequality
`Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div`. -/
theorem sum_mul_log_div_nonneg {ι : Type*} [Fintype ι] {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div Finset.univ p q (fun i _ => hp i)
    (fun i _ => hq i)
  rwa [hp1, hq1, div_one, Real.log_one, mul_zero] at h

/-- Equality in Gibbs' inequality: the relative entropy vanishes exactly when `p = q`. -/
lemma sum_mul_log_div_eq_zero_iff {ι : Type*} [Fintype ι] {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1) :
    ∑ i, p i * Real.log (p i / q i) = 0 ↔ p = q := by
  refine ⟨fun h => funext fun i => ?_, ?_⟩
  · rw [sum_mul_log_div_eq_sum_sub hp1 hq1, Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => sub_nonneg.mpr (mul_log_div_le_sub (hp i) (hq i))] at h
    by_contra hpq
    exact (sub_pos.mpr (mul_log_div_lt_sub (hp i) (hq i) hpq)).ne' (h i (Finset.mem_univ i))
  · rintro rfl
    exact Finset.sum_eq_zero fun i _ => by rw [div_self (hq i).ne', Real.log_one, mul_zero]

/-- Gibbs' inequality relative to the Boltzmann distribution: for every probability distribution
`p`, `0 ≤ ∑ i, p i * log (p i / boltzmannProb E β i)`. -/
lemma sum_mul_log_div_boltzmannProb_nonneg {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / boltzmannProb E β i) := by
  have := nonempty_of_sum_eq_one hp1
  exact sum_mul_log_div_nonneg hp hp1 (boltzmannProb_pos E β) (sum_boltzmannProb_eq_one E β)

/-- The relative entropy to the Boltzmann distribution vanishes exactly at the Boltzmann
distribution. -/
lemma sum_mul_log_div_boltzmannProb_eq_zero_iff {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, p i * Real.log (p i / boltzmannProb E β i) = 0 ↔ p = boltzmannProb E β := by
  have := nonempty_of_sum_eq_one hp1
  exact sum_mul_log_div_eq_zero_iff hp hp1 (boltzmannProb_pos E β) (sum_boltzmannProb_eq_one E β)

/-- The Lagrange-multiplier form summed against `p` with `∑ i, p i = 1`: minus the cross entropy,
`∑ i, p i * log (boltzmannProb E β i) = -β * ∑ i, p i * E i - log Z`, depends on `p` only
through its mean energy. -/
lemma sum_mul_log_boltzmannProb {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) {p : ι → ℝ}
    (hp1 : ∑ i, p i = 1) :
    ∑ i, p i * Real.log (boltzmannProb E β i) =
      -β * ∑ i, p i * E i - Real.log (partitionFunction E β) := by
  have h : ∀ i, p i * Real.log (boltzmannProb E β i) =
      -β * (p i * E i) - Real.log (partitionFunction E β) * p i := fun i => by
    rw [log_boltzmannProb]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hp1, mul_one]

/-- For `p` with `∑ i, p i = 1` and the mean energy of the Boltzmann distribution, the relative
entropy to the Boltzmann distribution is the entropy deficit. No sign condition on `p` is
needed. -/
lemma sum_mul_log_div_boltzmannProb_eq {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ)
    {p : ι → ℝ} (hp1 : ∑ i, p i = 1)
    (hU : ∑ i, p i * E i = ∑ i, boltzmannProb E β i * E i) :
    ∑ i, p i * Real.log (p i / boltzmannProb E β i) =
      shannonEntropy (boltzmannProb E β) - shannonEntropy p := by
  have := nonempty_of_sum_eq_one hp1
  have h : ∀ i, p i * Real.log (p i / boltzmannProb E β i) =
      p i * Real.log (p i) - p i * Real.log (boltzmannProb E β i) := by
    intro i
    rcases eq_or_ne (p i) 0 with hpi | hpi
    · simp [hpi]
    · rw [Real.log_div hpi (boltzmannProb_pos E β i).ne', mul_sub]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib,
    sum_mul_log_boltzmannProb E β hp1, shannonEntropy, shannonEntropy,
    sum_mul_log_boltzmannProb E β (sum_boltzmannProb_eq_one E β), hU]
  ring

/-- **Maximum entropy.** Among probability distributions `p` with the mean energy of the
Boltzmann distribution, the Boltzmann distribution has the largest Shannon entropy. The proof
combines Gibbs' inequality with the Lagrange-multiplier form `log_boltzmannProb`; no optimization
principle is assumed. -/
theorem shannonEntropy_le_shannonEntropy_boltzmannProb {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (β : ℝ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hU : ∑ i, p i * E i = ∑ i, boltzmannProb E β i * E i) :
    shannonEntropy p ≤ shannonEntropy (boltzmannProb E β) := by
  have h := sum_mul_log_div_boltzmannProb_nonneg E β hp hp1
  rw [sum_mul_log_div_boltzmannProb_eq E β hp1 hU] at h
  exact sub_nonneg.mp h

/-- The Boltzmann distribution is the only maximizer: a probability distribution with the mean
energy and the entropy of the Boltzmann distribution is the Boltzmann distribution. -/
lemma shannonEntropy_eq_shannonEntropy_boltzmannProb_iff {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (β : ℝ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hU : ∑ i, p i * E i = ∑ i, boltzmannProb E β i * E i) :
    shannonEntropy p = shannonEntropy (boltzmannProb E β) ↔ p = boltzmannProb E β := by
  rw [← sum_mul_log_div_boltzmannProb_eq_zero_iff E β hp hp1,
    sum_mul_log_div_boltzmannProb_eq E β hp1 hU, sub_eq_zero]
  exact eq_comm

/-!

## C. Thermodynamic functions and fluctuations

-/

/-- The mean energy `U = ∑ i, p i * E i` of the Boltzmann distribution. -/
noncomputable def meanEnergy {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, boltzmannProb E β i * E i

/-- The energy variance `Var(E) = ∑ i, p i * (E i - U) ^ 2` of the Boltzmann distribution. -/
noncomputable def energyVariance {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, boltzmannProb E β i * (E i - meanEnergy E β) ^ 2

/-- The temperature `T = 1 / (kB * β)`: a definition, not a new constant, meaningful for
`0 < kB` and `0 < β`. -/
noncomputable def temperature (kB β : ℝ) : ℝ :=
  1 / (kB * β)

/-- The Helmholtz free energy `A = -(log Z) / β`, which is `-kB T log Z` because `kB T = 1 / β`
(`helmholtzFreeEnergy_eq_neg_mul_temperature_mul_log`). It does not depend on the Boltzmann
constant, so it takes no `kB` argument. -/
noncomputable def helmholtzFreeEnergy {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) : ℝ :=
  -(Real.log (partitionFunction E β)) / β

/-- The entropy `S = kB * (log Z + β * U)`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (kB : ℝ) (E : ι → ℝ) (β : ℝ) : ℝ :=
  kB * (Real.log (partitionFunction E β) + β * meanEnergy E β)

/-- The heat capacity `C = kB * β ^ 2 * Var(E)`. -/
noncomputable def heatCapacity {ι : Type*} [Fintype ι] (kB : ℝ) (E : ι → ℝ) (β : ℝ) : ℝ :=
  kB * β ^ 2 * energyVariance E β

/-- The energy variance is nonnegative. -/
lemma energyVariance_nonneg {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) :
    0 ≤ energyVariance E β :=
  Finset.sum_nonneg fun i _ => mul_nonneg (boltzmannProb_nonneg E β i) (sq_nonneg _)

/-- The heat capacity is nonnegative. -/
lemma heatCapacity_nonneg {ι : Type*} [Fintype ι] {kB : ℝ} (hkB : 0 < kB) (E : ι → ℝ) (β : ℝ) :
    0 ≤ heatCapacity kB E β :=
  mul_nonneg (mul_nonneg hkB.le (sq_nonneg β)) (energyVariance_nonneg E β)

/-- `Var(E) = ∑ i, p i * E i ^ 2 - U ^ 2`. -/
lemma energyVariance_eq_sum_sub_meanEnergy_sq {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ)
    (β : ℝ) :
    energyVariance E β = ∑ i, boltzmannProb E β i * E i ^ 2 - meanEnergy E β ^ 2 := by
  have h : ∀ i, boltzmannProb E β i * (E i - meanEnergy E β) ^ 2 =
      boltzmannProb E β i * E i ^ 2 - 2 * meanEnergy E β * (boltzmannProb E β i * E i) +
        meanEnergy E β ^ 2 * boltzmannProb E β i := fun i => by ring
  have hU : ∑ i, boltzmannProb E β i * E i = meanEnergy E β := rfl
  rw [energyVariance, Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hU, sum_boltzmannProb_eq_one]
  ring

/-- `S = kB * H(p)`: the entropy is `kB` times the Shannon entropy of the Boltzmann
distribution. -/
lemma entropy_eq_mul_shannonEntropy {ι : Type*} [Fintype ι] [Nonempty ι] (kB : ℝ) (E : ι → ℝ)
    (β : ℝ) : entropy kB E β = kB * shannonEntropy (boltzmannProb E β) := by
  rw [entropy, shannonEntropy, sum_mul_log_boltzmannProb E β (sum_boltzmannProb_eq_one E β),
    meanEnergy]
  ring

/-- `A = U - S / (kB * β)`. -/
lemma helmholtzFreeEnergy_eq_meanEnergy_sub_entropy_div {ι : Type*} [Fintype ι] {kB β : ℝ}
    (hkB : 0 < kB) (hβ : 0 < β) (E : ι → ℝ) :
    helmholtzFreeEnergy E β = meanEnergy E β - entropy kB E β / (kB * β) := by
  have hkB' := hkB.ne'
  have hβ' := hβ.ne'
  rw [helmholtzFreeEnergy, entropy]
  field_simp
  ring

/-- The temperature is positive. -/
lemma temperature_pos {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) : 0 < temperature kB β :=
  one_div_pos.mpr (mul_pos hkB hβ)

/-- `A = U - T S` with `T = 1 / (kB * β)`. -/
lemma helmholtzFreeEnergy_eq_meanEnergy_sub_temperature_mul_entropy {ι : Type*} [Fintype ι]
    {kB β : ℝ} (hkB : 0 < kB) (hβ : 0 < β) (E : ι → ℝ) :
    helmholtzFreeEnergy E β = meanEnergy E β - temperature kB β * entropy kB E β := by
  rw [helmholtzFreeEnergy_eq_meanEnergy_sub_entropy_div hkB hβ, temperature]
  ring

/-- `A = -kB T log Z`, the form of Physlib's `CanonicalEnsemble.helmholtzFreeEnergy`. -/
lemma helmholtzFreeEnergy_eq_neg_mul_temperature_mul_log {ι : Type*} [Fintype ι] {kB β : ℝ}
    (hkB : 0 < kB) (hβ : 0 < β) (E : ι → ℝ) :
    helmholtzFreeEnergy E β =
      -(kB * temperature kB β) * Real.log (partitionFunction E β) := by
  have hkB' := hkB.ne'
  have hβ' := hβ.ne'
  rw [helmholtzFreeEnergy, temperature]
  field_simp

/-- `d/dβ exp (-β * e) = exp (-β * e) * (-e)`. -/
lemma hasDerivAt_exp_neg_mul (e β : ℝ) :
    HasDerivAt (fun b => Real.exp (-b * e)) (Real.exp (-β * e) * (-e)) β := by
  simpa using ((hasDerivAt_id β).neg.mul_const e).exp

/-- `dZ/dβ = -∑ i, E i * exp (-β * E i)`. -/
lemma hasDerivAt_partitionFunction {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun b => partitionFunction E b) (-∑ i, E i * Real.exp (-β * E i)) β := by
  have h : HasDerivAt (fun b => ∑ i, Real.exp (-b * E i))
      (-∑ i, E i * Real.exp (-β * E i)) β := by
    rw [← Finset.sum_neg_distrib]
    exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_exp_neg_mul (E i) β).congr_deriv (by ring)
  exact h

/-- `U = (∑ i, E i * exp (-β * E i)) / Z`. -/
lemma meanEnergy_eq_div {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) :
    meanEnergy E β = (∑ i, E i * Real.exp (-β * E i)) / partitionFunction E β := by
  rw [meanEnergy, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [boltzmannProb]; ring

/-- `d(log Z)/dβ = -U`, as a `HasDerivAt` statement. -/
lemma hasDerivAt_log_partitionFunction {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ)
    (β : ℝ) : HasDerivAt (fun b => Real.log (partitionFunction E b)) (-meanEnergy E β) β := by
  rw [meanEnergy_eq_div, ← neg_div]
  exact (hasDerivAt_partitionFunction E β).log (partitionFunction_pos E β).ne'

/-- `d(log Z)/dβ = -U`. -/
lemma deriv_log_partitionFunction {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    deriv (fun b => Real.log (partitionFunction E b)) β = -(meanEnergy E β) :=
  (hasDerivAt_log_partitionFunction E β).deriv

/-- `dU/dβ = -Var(E)`, as a `HasDerivAt` statement. -/
lemma hasDerivAt_meanEnergy {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun b => meanEnergy E b) (-energyVariance E β) β := by
  have hN : HasDerivAt (fun b => ∑ i, E i * Real.exp (-b * E i))
      (-∑ i, E i ^ 2 * Real.exp (-β * E i)) β := by
    rw [← Finset.sum_neg_distrib]
    exact HasDerivAt.fun_sum fun i _ =>
      ((hasDerivAt_exp_neg_mul (E i) β).const_mul (E i)).congr_deriv (by ring)
  have hZ := (partitionFunction_pos E β).ne'
  have h2 : ∑ i, boltzmannProb E β i * E i ^ 2 =
      (∑ i, E i ^ 2 * Real.exp (-β * E i)) / partitionFunction E β := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [boltzmannProb]; ring
  have hfun : (fun b => meanEnergy E b) =
      (fun b => ∑ i, E i * Real.exp (-b * E i)) / fun b => partitionFunction E b :=
    funext fun b => meanEnergy_eq_div E b
  have key : ∀ S N Z : ℝ, Z ≠ 0 → -(S / Z - (N / Z) ^ 2) = (-S * Z - N * -N) / Z ^ 2 := by
    intro S N Z hZ
    field_simp
    ring
  rw [hfun, energyVariance_eq_sum_sub_meanEnergy_sq, h2, meanEnergy_eq_div]
  convert hN.div (hasDerivAt_partitionFunction E β) hZ using 1
  exact key _ _ _ hZ

/-- `dU/dβ = -Var(E)`. -/
lemma deriv_meanEnergy {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    deriv (fun b => meanEnergy E b) β = -(energyVariance E β) :=
  (hasDerivAt_meanEnergy E β).deriv

/-- **Fluctuation–dissipation.** The heat capacity is `C = -kB * β ^ 2 * dU/dβ`. -/
theorem heatCapacity_eq_neg_mul_deriv_meanEnergy {ι : Type*} [Fintype ι] [Nonempty ι] (kB : ℝ)
    (E : ι → ℝ) (β : ℝ) :
    heatCapacity kB E β = -(kB * β ^ 2) * deriv (fun b => meanEnergy E b) β := by
  rw [deriv_meanEnergy, heatCapacity]
  ring

/-- `C = Var(E) / (kB * T ^ 2)`, the form of Physlib's
`CanonicalEnsemble.fluctuation_dissipation_theorem_finite`. -/
lemma heatCapacity_eq_energyVariance_div {ι : Type*} [Fintype ι] {kB β : ℝ} (hkB : 0 < kB)
    (hβ : 0 < β) (E : ι → ℝ) :
    heatCapacity kB E β = energyVariance E β / (kB * temperature kB β ^ 2) := by
  have hkB' := hkB.ne'
  have hβ' := hβ.ne'
  rw [heatCapacity, temperature]
  field_simp

/-!

## D. Independent subsystems

-/

/-- The energy `E (i, j) = E₁ i + E₂ j` of two independent subsystems, on the product `ι × κ` of
their state spaces. -/
def combinedEnergy {ι κ : Type*} (E₁ : ι → ℝ) (E₂ : κ → ℝ) (x : ι × κ) : ℝ :=
  E₁ x.1 + E₂ x.2

/-- The partition function of independent subsystems is the product of their partition
functions. -/
lemma partitionFunction_combinedEnergy {ι κ : Type*} [Fintype ι] [Fintype κ] (E₁ : ι → ℝ)
    (E₂ : κ → ℝ) (β : ℝ) :
    partitionFunction (combinedEnergy E₁ E₂) β =
      partitionFunction E₁ β * partitionFunction E₂ β := by
  rw [partitionFunction, partitionFunction, partitionFunction, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [combinedEnergy, mul_add, Real.exp_add]

/-- The Boltzmann probabilities of independent subsystems multiply. -/
lemma boltzmannProb_combinedEnergy {ι κ : Type*} [Fintype ι] [Fintype κ] (E₁ : ι → ℝ)
    (E₂ : κ → ℝ) (β : ℝ) (i : ι) (j : κ) :
    boltzmannProb (combinedEnergy E₁ E₂) β (i, j) =
      boltzmannProb E₁ β i * boltzmannProb E₂ β j := by
  simp only [boltzmannProb, partitionFunction_combinedEnergy, combinedEnergy, mul_add,
    Real.exp_add]
  exact mul_div_mul_comm _ _ _ _

/-- The mean energy of independent subsystems is the sum of their mean energies. -/
lemma meanEnergy_combinedEnergy {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    [Nonempty κ] (E₁ : ι → ℝ) (E₂ : κ → ℝ) (β : ℝ) :
    meanEnergy (combinedEnergy E₁ E₂) β = meanEnergy E₁ β + meanEnergy E₂ β := by
  have h : ∀ i j, boltzmannProb (combinedEnergy E₁ E₂) β (i, j) * combinedEnergy E₁ E₂ (i, j) =
      boltzmannProb E₁ β i * E₁ i * boltzmannProb E₂ β j +
        boltzmannProb E₁ β i * (boltzmannProb E₂ β j * E₂ j) := fun i j => by
    rw [boltzmannProb_combinedEnergy]
    simp only [combinedEnergy]
    ring
  rw [meanEnergy, meanEnergy, meanEnergy, Fintype.sum_prod_type]
  simp_rw [h, Finset.sum_add_distrib, ← Finset.sum_mul_sum, sum_boltzmannProb_eq_one, mul_one,
    one_mul]

/-!

## E. Two-level system

-/

/-- The two-level system on `Fin 2`: state `0` has energy `0` and state `1` has energy `Δ`. For
`0 < Δ`, state `0` is the ground state and state `1` the excited state. -/
def twoLevelEnergy (Δ : ℝ) : Fin 2 → ℝ :=
  ![0, Δ]

/-- State `0` has energy `0`. -/
@[simp] lemma twoLevelEnergy_zero (Δ : ℝ) : twoLevelEnergy Δ 0 = 0 :=
  rfl

/-- State `1` has energy `Δ`. -/
@[simp] lemma twoLevelEnergy_one (Δ : ℝ) : twoLevelEnergy Δ 1 = Δ :=
  rfl

/-- The two-level partition function is the two-state sum `exp 0 + exp (-β * Δ)`. -/
lemma partitionFunction_twoLevelEnergy (Δ β : ℝ) :
    partitionFunction (twoLevelEnergy Δ) β = Real.exp 0 + Real.exp (-β * Δ) := by
  rw [partitionFunction, Fin.sum_univ_two, twoLevelEnergy_zero, twoLevelEnergy_one, mul_zero]

/-- At `β * Δ = log 3`, the Boltzmann factor of state `1` is `exp (-β * Δ) = 1 / 3`. -/
lemma exp_neg_mul_eq_one_third {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    Real.exp (-β * Δ) = 1 / 3 := by
  rw [neg_mul, hβΔ, Real.exp_neg, Real.exp_log (by norm_num), one_div]

/-- At `β * Δ = log 3`, `Z = 4 / 3`. -/
lemma partitionFunction_twoLevelEnergy_eq {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    partitionFunction (twoLevelEnergy Δ) β = 4 / 3 := by
  rw [partitionFunction_twoLevelEnergy, Real.exp_zero, exp_neg_mul_eq_one_third hβΔ]
  norm_num

/-- At `β * Δ = log 3`, state `0` (the ground state for `0 < Δ`) has probability `3 / 4`. -/
lemma boltzmannProb_twoLevelEnergy_zero {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    boltzmannProb (twoLevelEnergy Δ) β 0 = 3 / 4 := by
  rw [boltzmannProb, partitionFunction_twoLevelEnergy_eq hβΔ, twoLevelEnergy_zero, mul_zero,
    Real.exp_zero]
  norm_num

/-- At `β * Δ = log 3`, state `1` (the excited state for `0 < Δ`) has probability `1 / 4`. -/
lemma boltzmannProb_twoLevelEnergy_one {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    boltzmannProb (twoLevelEnergy Δ) β 1 = 1 / 4 := by
  rw [boltzmannProb, partitionFunction_twoLevelEnergy_eq hβΔ, twoLevelEnergy_one,
    exp_neg_mul_eq_one_third hβΔ]
  norm_num

/-- At `β * Δ = log 3`, `U = Δ / 4`. -/
lemma meanEnergy_twoLevelEnergy {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    meanEnergy (twoLevelEnergy Δ) β = Δ / 4 := by
  rw [meanEnergy, Fin.sum_univ_two, boltzmannProb_twoLevelEnergy_zero hβΔ,
    boltzmannProb_twoLevelEnergy_one hβΔ, twoLevelEnergy_zero, twoLevelEnergy_one]
  ring

/-- At `β * Δ = log 3`, `Var(E) = 3 * Δ ^ 2 / 16`. -/
lemma energyVariance_twoLevelEnergy {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    energyVariance (twoLevelEnergy Δ) β = 3 * Δ ^ 2 / 16 := by
  rw [energyVariance, meanEnergy_twoLevelEnergy hβΔ, Fin.sum_univ_two,
    boltzmannProb_twoLevelEnergy_zero hβΔ, boltzmannProb_twoLevelEnergy_one hβΔ,
    twoLevelEnergy_zero, twoLevelEnergy_one]
  ring

/-- At `β * Δ = log 3`, `C = kB * (3 * (log 3) ^ 2 / 16)`, that is
`C / kB = 3 * (log 3) ^ 2 / 16` for `kB ≠ 0`. -/
lemma heatCapacity_twoLevelEnergy (kB : ℝ) {β Δ : ℝ} (hβΔ : β * Δ = Real.log 3) :
    heatCapacity kB (twoLevelEnergy Δ) β = kB * (3 * Real.log 3 ^ 2 / 16) := by
  rw [heatCapacity, energyVariance_twoLevelEnergy hβΔ, ← hβΔ]
  ring

/-- For `0 < Δ`, `β * Δ = log 3` forces `0 < β`: the worked example is at a positive
temperature. -/
lemma pos_of_mul_eq_log_three {β Δ : ℝ} (hΔ : 0 < Δ) (hβΔ : β * Δ = Real.log 3) : 0 < β := by
  refine pos_of_mul_pos_left ?_ hΔ.le
  rw [hβΔ]
  exact Real.log_pos (by norm_num)

/-- **CHEM-C5 worked example.** For the two-level system with energies `0` and `Δ > 0` at
`β * Δ = log 3`: `0 < β`, `Z = exp 0 + exp (-β * Δ) = 4 / 3`, the excited state has probability
`1 / 4`, `U = Δ / 4`, `Var(E) = 3 * Δ ^ 2 / 16` and `C = kB * (3 * (log 3) ^ 2 / 16)`. -/
lemma twoLevelEnergy_workedExample (kB : ℝ) {β Δ : ℝ} (hΔ : 0 < Δ)
    (hβΔ : β * Δ = Real.log 3) :
    0 < β ∧ Real.exp 0 + Real.exp (-β * Δ) = 4 / 3 ∧
      partitionFunction (twoLevelEnergy Δ) β = 4 / 3 ∧
      boltzmannProb (twoLevelEnergy Δ) β 1 = 1 / 4 ∧ meanEnergy (twoLevelEnergy Δ) β = Δ / 4 ∧
      energyVariance (twoLevelEnergy Δ) β = 3 * Δ ^ 2 / 16 ∧
      heatCapacity kB (twoLevelEnergy Δ) β = kB * (3 * Real.log 3 ^ 2 / 16) :=
  ⟨pos_of_mul_eq_log_three hΔ hβΔ,
    (partitionFunction_twoLevelEnergy Δ β).symm.trans (partitionFunction_twoLevelEnergy_eq hβΔ),
    partitionFunction_twoLevelEnergy_eq hβΔ, boltzmannProb_twoLevelEnergy_one hβΔ,
    meanEnergy_twoLevelEnergy hβΔ, energyVariance_twoLevelEnergy hβΔ,
    heatCapacity_twoLevelEnergy kB hβΔ⟩

/-!

## F. Einstein-solid counting and Stirling's formula

-/

/-- **Stars and bars** for the Einstein solid: there are `(N + q - 1).choose q` ways to distribute
`q` indistinguishable quanta among `N` oscillators, that is functions `f : Fin N → ℕ` with
`∑ i, f i = q`. The count transports Mathlib's `Sym.card_sym_eq_choose` along
`Sym.equivNatSumOfFintype`. -/
theorem card_sum_eq_choose (N q : ℕ) :
    Nat.card {f : Fin N → ℕ // ∑ i, f i = q} = (N + q - 1).choose q := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin N) q), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The Einstein-solid microstates form the `Finset` `Finset.Nat.antidiagonalTuple N q`, which
has `(N + q - 1).choose q` elements. -/
lemma card_antidiagonalTuple (N q : ℕ) :
    (Finset.Nat.antidiagonalTuple N q).card = (N + q - 1).choose q := by
  rw [← card_sum_eq_choose, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Finset.Nat.mem_antidiagonalTuple)

/-- Stirling's formula is only asymptotic. At `n = 2` the Stirling value
`2 ^ (2 + 1 / 2) * exp (-2) * √(2 * π) = 8 * √π / exp 2 ≈ 1.92`, with the real exponent
`2 + 1 / 2`, is strictly smaller than `2! = 2`. -/
lemma stirling_two_lt_factorial :
    (2 : ℝ) ^ ((2 : ℝ) + 1 / 2) * Real.exp (-2) * Real.sqrt (2 * Real.pi) <
      (Nat.factorial 2 : ℝ) := by
  have h1 : (2 : ℝ) ^ ((2 : ℝ) + 1 / 2) = 4 * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]
    norm_num
  have h2 : Real.sqrt 2 * Real.sqrt (2 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * (2 * Real.pi) = 2 ^ 2 * Real.pi by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hpi : Real.sqrt Real.pi < 1.775 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith [Real.pi_lt_d2]
  have he : 7.38 < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  have hval : (2 : ℝ) ^ ((2 : ℝ) + 1 / 2) * Real.exp (-2) * Real.sqrt (2 * Real.pi) =
      4 * (Real.sqrt 2 * Real.sqrt (2 * Real.pi)) / Real.exp 2 := by
    rw [h1, Real.exp_neg]
    ring
  rw [hval, h2, Nat.factorial_two, Nat.cast_ofNat, div_lt_iff₀ (Real.exp_pos 2)]
  linarith

/-- `2!` differs from the Stirling value at `n = 2`: Stirling's formula is not an equality. -/
lemma factorial_two_ne_stirling :
    (Nat.factorial 2 : ℝ) ≠
      (2 : ℝ) ^ ((2 : ℝ) + 1 / 2) * Real.exp (-2) * Real.sqrt (2 * Real.pi) :=
  stirling_two_lt_factorial.ne'

/-!

## G. The canonical postulate

-/

/-- The canonical postulate as a predicate: `p` is canonical for the energies `E` at inverse
temperature `β` if `p = boltzmannProb E β`. The postulate (equal a priori probabilities for a
system and its reservoir) is a modelling assumption, not derived here; the predicate lets a
result about canonical distributions take `IsCanonical p E β` as an explicit hypothesis. -/
def IsCanonical {ι : Type*} [Fintype ι] (p : ι → ℝ) (E : ι → ℝ) (β : ℝ) : Prop :=
  p = boltzmannProb E β

/-- The Boltzmann distribution is canonical. -/
lemma isCanonical_boltzmannProb {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) :
    IsCanonical (boltzmannProb E β) E β :=
  rfl

/-!

## H. Bridge to Physlib's canonical-ensemble API

For a finite type of microstates with the discrete measure structure, the
energies `E` form a finite Physlib canonical ensemble with the counting
measure, no degrees of freedom and phase-space unit `1`. Its β-real
partition function, Boltzmann probabilities and mean energy are the
`partitionFunction`, `boltzmannProb` and `meanEnergy` of this module.
Physlib's remaining thermodynamic quantities are stated for a
`Temperature`, not for a real `β`, and it provides no β-real
energy-variance, entropy, Helmholtz or heat-capacity definitions, so those
stay in the finite-sum form proved above.

-/

/-- The finite canonical ensemble of a system with energies `E`: microstates
`ι`, counting measure, no degrees of freedom, phase-space unit `1`. -/
noncomputable def canonicalEnsemble {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (E : ι → ℝ) : CanonicalEnsemble ι where
  energy := E
  dof := 0
  μ := MeasureTheory.Measure.count
  energy_measurable := measurable_of_finite _

/-- The counting-measure ensemble of a finite system is finite in Physlib's
sense. -/
instance {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (E : ι → ℝ) : (canonicalEnsemble E).IsFinite where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

/-- `partitionFunction` is Physlib's β-real mathematical partition function. -/
lemma partitionFunction_eq_mathematicalPartitionFunctionBetaReal {ι : Type} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (E : ι → ℝ) (β : ℝ) :
    partitionFunction E β =
      (canonicalEnsemble E).mathematicalPartitionFunctionBetaReal β :=
  rfl

/-- `boltzmannProb` is Physlib's β-real Boltzmann probability. -/
lemma boltzmannProb_eq_probabilityBetaReal {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    boltzmannProb E β i = (canonicalEnsemble E).probabilityBetaReal β i :=
  rfl

/-- `meanEnergy` is Physlib's β-real mean energy (up to the order of the
factors in each summand). -/
lemma meanEnergy_eq_meanEnergyBetaReal {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (E : ι → ℝ) (β : ℝ) :
    meanEnergy E β = (canonicalEnsemble E).meanEnergyBetaReal β := by
  have h : ∀ i, boltzmannProb E β i = (canonicalEnsemble E).probabilityBetaReal β i :=
    fun _ => rfl
  calc meanEnergy E β = ∑ i, E i * boltzmannProb E β i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = ∑ i, E i * (canonicalEnsemble E).probabilityBetaReal β i :=
        Finset.sum_congr rfl fun i _ => by rw [h i]
    _ = (canonicalEnsemble E).meanEnergyBetaReal β := rfl

end Chemistry.FiniteEnsembles
