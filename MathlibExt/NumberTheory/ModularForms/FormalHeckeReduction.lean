/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_PowerSeries_FormalHeckeOperators.lean`,
`Definitions/Def_ModularForm_EisensteinChiNegThree.lean`,
`Definitions/Def_CuspForm_IntegralLattice.lean`,
`Definitions/Def_FormalHecke_Eigensystem.lean`,
`Theorems/Thm_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean`,
`P2M/Sol/S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean`,
`Theorems/Thm_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two.lean`,
`P2M/Sol/S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two.lean`,
`Theorems/Thm_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem.lean`,
`P2M/Sol/S_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem.lean`,
`Theorems/Thm_CuspForm_exists_reductionModule_of_isLatticeRealized.lean`,
`P2M/Sol/S_CuspForm_exists_reductionModule_of_isLatticeRealized.lean`,
`Theorems/Thm_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd.lean`, and
`P2M/Sol/S_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.ModularForms.HeckeLocal
import MathlibExt.NumberTheory.ModularForms.NormalizedEigenform
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

/-!
# Formal Hecke operators and reduction modulo `3` of weight-two cusp forms

This file sets up the formal side of a Deligne–Serre style lifting argument in weight two
on `Γ₀(N)`. A candidate system of eigenvalues `a : ℕ → ℤ` is turned into the power series
`bridgeProduct a = (∑ aₙ Xⁿ) · E₁,χ₋₃`, where `E₁,χ₋₃ ≡ 1 (mod 3)` is the weight-one Eisenstein
series of the character `χ₋₃`. When `a 1 = 1` and this product is congruent modulo `3` to the
`q`-expansion of an integral cusp form, the integral lattice modulo `3` gives a module over the
Hecke algebra, with a reduction map from integral power series, on which `T_ℓ - a ℓ` acts on the
reduction of `bridgeProduct a` as the formal Hecke operator does on power series. If moreover
`bridgeProduct a` satisfies the formal `T_ℓ` eigenvalue equation with eigenvalue `a ℓ` modulo `3`
for every prime `ℓ ∤ N`, the reduction of `bridgeProduct a` is nonzero (its first coefficient is
`1` modulo `3`) and killed by `3` and by every `T_ℓ - a ℓ`, so some maximal ideal of the Hecke
algebra contains `3` and every `T_ℓ - a ℓ`.

## Main definitions

* `PowerSeries.heckeU`, `PowerSeries.heckeV`, `PowerSeries.heckeT`: the formal Hecke operators
  `U_ℓ`, `V_ℓ` and `T_ℓ = U_ℓ + ℓ ^ (k - 1) V_ℓ` on power series.
* `EisensteinWeightOne.chiNegThree`, `EisensteinWeightOne.sigmaChi`,
  `EisensteinWeightOne.e1Chi3`, `EisensteinWeightOne.e1Chi3In`: the character `χ₋₃`, its twisted
  divisor sum and the `q`-expansion of the weight-one Eisenstein series `E₁,χ₋₃`.
* `bridgeProduct`, `CuspForm.IsLatticeRealized`: the product of a coefficient sequence with
  `E₁,χ₋₃`, and its realization modulo `3` by a cusp form in the integral lattice
  `CuspForm.intLattice N 2`.
* `FormalHecke.IsEigensystem`: the formal Hecke recursion for a coefficient sequence.

## Main statements

* `EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub`: multiplying by `E₁,χ₋₃` does not change
  coefficients modulo `3`.
* `CuspForm.exists_isMaximal_three_mem_heckeT_sub_mem`: if `a 1 = 1`, `bridgeProduct a`
  satisfies the formal `T_ℓ` eigenvalue equation modulo `3` for every prime `ℓ ∤ N`, and a
  reduction map to a module over the Hecke algebra detects `3`-divisibility of the first
  coefficient and intertwines `T_ℓ - a ℓ` with the formal operator, then some maximal ideal of the
  Hecke algebra contains `3` and every `T_ℓ - a ℓ`.
* `CuspForm.exists_reductionModule_of_isLatticeRealized`: a lattice realization with `a 1 = 1`
  gives such a reduction map and module (in the proof, the integral lattice modulo `3`).
* `FormalHecke.IsEigensystem.three_dvd_coeff_heckeT_bridgeProduct_sub_smul`: over any commutative
  ring, a formal eigensystem with nebentypus values `χ₋₃(ℓ)` at the primes `ℓ ∤ N` and `0` at the
  primes `ℓ ∣ N` makes `bridgeProduct a` satisfy the formal `T_ℓ` eigenvalue equation modulo `3`,
  coefficientwise, for every prime `ℓ ∤ N`.
-/

@[expose] public section

noncomputable section

open scoped PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The formal Hecke operator `U_ℓ` on power series: `∑ aₙ Xⁿ ↦ ∑ a_{ℓ n} Xⁿ`. -/
def heckeU (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => coeff (ℓ * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

@[simp] lemma coeff_heckeU (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeU ℓ f) = coeff (ℓ * n) f := by
  simp [heckeU]

/-- The formal operator `V_ℓ` on power series: for `ℓ ≠ 0` it is the substitution
`∑ aₙ Xⁿ ↦ ∑ aₙ X^{ℓ n}`; for `ℓ = 0` it keeps only the constant coefficient. -/
def heckeV (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => if ℓ ∣ n then coeff (n / ℓ) f else 0
  map_add' f g := by ext n; by_cases h : ℓ ∣ n <;> simp [h]
  map_smul' c f := by ext n; by_cases h : ℓ ∣ n <;> simp [h]

@[simp] lemma coeff_heckeV (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeV ℓ f) = if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeV]

lemma heckeU_heckeV (ℓ : ℕ) (hℓ : ℓ ≠ 0) (f : R⟦X⟧) : heckeU ℓ (heckeV ℓ f) = f := by
  ext n
  simp [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hℓ), Dvd.intro n rfl]

/-- The formal Hecke operator `T_ℓ = U_ℓ + ℓ ^ (k - 1) V_ℓ` of weight `k` on power series. The
exponent `k - 1` is computed in `ℕ`, so for `k = 0` the factor `ℓ ^ (k - 1)` is `1`. -/
def heckeT (ℓ k : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  heckeU ℓ + (ℓ : R) ^ (k - 1) • heckeV ℓ

lemma coeff_heckeT (ℓ k n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeT ℓ k f) =
      coeff (ℓ * n) f + (ℓ : R) ^ (k - 1) * if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeT]

end PowerSeries

namespace EisensteinWeightOne

/-- The quadratic character `χ₋₃` of conductor `3`, as a function on `ℕ`. -/
def chiNegThree (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

/-- The twisted divisor sum `∑_{d ∣ n} χ₋₃(d)`. -/
def sigmaChi (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, chiNegThree d

/-- The integral `q`-expansion `1 + 6 ∑ σ_χ(n) qⁿ` of the weight-one Eisenstein series
`E₁,χ₋₃`. -/
def e1Chi3 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 6 * sigmaChi n

/-- The `q`-expansion of `E₁,χ₋₃` with coefficients in a commutative ring `R`. -/
def e1Chi3In (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) e1Chi3

end EisensteinWeightOne

open EisensteinWeightOne

/-- The product `(∑ aₙ Xⁿ) · E₁,χ₋₃` of the power series with coefficients `a` and the
`q`-expansion of the weight-one Eisenstein series `E₁,χ₋₃`. -/
def bridgeProduct {R : Type*} [CommRing R] (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk a * e1Chi3In R

namespace CuspForm

/-- The coefficient sequence `a` is realized by the integral lattice at level `N`: some
weight-two cusp form on `Γ₀(N)` in the integral lattice `CuspForm.intLattice N 2`, the forms with
integral `q`-expansion, is congruent modulo `3`, coefficientwise, to `bridgeProduct a`. -/
def IsLatticeRealized (N : ℕ) (a : ℕ → ℤ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f ∈ CuspForm.intLattice N 2 ∧
    ∃ af : ℕ → ℤ, (∀ n, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      ∀ n, (3 : ℤ) ∣ af n - (bridgeProduct a).coeff n

end CuspForm

namespace FormalHecke

variable {R : Type*} [CommRing R]

/-- The sequence `a` is a formal Hecke eigensystem with nebentypus values `e`: `a 1 = 1` and
`a (ℓ n) + e ℓ · a (n / ℓ) = a ℓ · a n` for every prime `ℓ`, the middle term read as `0`
when `ℓ ∤ n`. -/
def IsEigensystem (e a : ℕ → R) : Prop :=
  a 1 = 1 ∧ ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ,
    a (ℓ * n) + e ℓ * (if ℓ ∣ n then a (n / ℓ) else 0) = a ℓ * a n

end FormalHecke

/-! ### Congruences for `E₁,χ₋₃` modulo `3` -/

namespace EisensteinWeightOne

private theorem coeff_e1Chi3In {R : Type*} [CommRing R] (j : ℕ) :
    PowerSeries.coeff j (e1Chi3In R) = if j = 0 then 1 else ((6 * sigmaChi j : ℤ) : R) := by
  simp only [e1Chi3In, e1Chi3, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

private theorem three_dvd_coeff_mul_e1Chi3In_sub {R : Type*} [CommRing R] (g : PowerSeries R)
    (n : ℕ) : (3 : R) ∣ PowerSeries.coeff n (g * e1Chi3In R) - PowerSeries.coeff n g := by
  classical
  rw [PowerSeries.coeff_mul]
  have hmem : (n, 0) ∈ Finset.antidiagonal n := by simp
  rw [← Finset.add_sum_erase _ _ hmem, coeff_e1Chi3In, ite_eq_left rfl, mul_one,
    add_sub_cancel_left]
  refine Finset.dvd_sum fun ij hij => ?_
  obtain ⟨hne, hanti⟩ := Finset.mem_erase.mp hij
  have hj : ij.2 ≠ 0 := by
    intro h0
    apply hne
    have : ij.1 = n := by simpa [h0] using Finset.mem_antidiagonal.mp hanti
    exact Prod.ext this h0
  rw [coeff_e1Chi3In, ite_eq_right hj]
  refine Dvd.dvd.mul_left ⟨((2 * sigmaChi ij.2 : ℤ) : R), ?_⟩ _
  push_cast
  ring

private theorem three_dvd_coeff_e1Chi3_sub_one (n : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff n (e1Chi3 - 1) := by
  rw [map_sub, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [e1Chi3, PowerSeries.coeff_mk]
  · rw [ite_eq_right hn, sub_zero, e1Chi3, PowerSeries.coeff_mk, ite_eq_right hn]
    exact ⟨2 * sigmaChi n, by ring⟩

/-- Multiplying an integral power series by `E₁,χ₋₃` does not change its coefficients
modulo `3`, since `E₁,χ₋₃ ≡ 1 (mod 3)`. -/
theorem three_dvd_coeff_mul_e1Chi3_sub (g : PowerSeries ℤ) (n : ℕ) :
    3 ∣ (PowerSeries.coeff n) (g * EisensteinWeightOne.e1Chi3) - (PowerSeries.coeff n) g := by
  have hfactor : g * e1Chi3 - g = g * (e1Chi3 - 1) := by ring
  rw [← map_sub, hfactor, PowerSeries.coeff_mul]
  exact Finset.dvd_sum fun p _ => (three_dvd_coeff_e1Chi3_sub_one p.2).mul_left _

end EisensteinWeightOne

private theorem three_dvd_coeff_bridgeProduct_sub {R : Type*} [CommRing R] (a : ℕ → R)
    (m : ℕ) : (3 : R) ∣ PowerSeries.coeff m (bridgeProduct a) - a m := by
  have h := EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3In_sub (PowerSeries.mk a) m
  rwa [PowerSeries.coeff_mk] at h

private theorem not_three_dvd_coeff_one_bridgeProduct {a : ℕ → ℤ} (h1 : a 1 = 1) :
    ¬ (3 : ℤ) ∣ PowerSeries.coeff 1 (bridgeProduct a) := by
  intro h3
  have h3' := three_dvd_coeff_bridgeProduct_sub a 1
  rw [h1] at h3'
  have : (3 : ℤ) ∣ 1 := by simpa using dvd_sub h3 h3'
  omega

/-! ### A maximal ideal above `3` from a reduction module -/

namespace CuspForm

/-- Let `N ≠ 0`, and let `red` be a reduction map from integral power series to a module `M` over
the Hecke algebra away from the level, which kills the series divisible by `3`, detects
`3`-divisibility of the first coefficient, and on which `T_ℓ - a ℓ` acts on
`red (bridgeProduct a)` as the formal operator `T_ℓ - a ℓ` does. If `a 1 = 1`, `bridgeProduct a`
is a formal `T_ℓ`-eigenvector modulo `3` and `3` kills `red (bridgeProduct a)`, then some maximal
ideal of the Hecke algebra contains `3` and every `T_ℓ - a ℓ`. -/
theorem exists_isMaximal_three_mem_heckeT_sub_mem {N : ℕ} [NeZero N] {a : ℕ → ℤ}
    (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    {M : Type*} [AddCommGroup M] [Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M]
    (red : PowerSeries ℤ → M)
    (hker : ∀ g : PowerSeries ℤ, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0)
    (hker' : ∀ g : PowerSeries ℤ, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g)
    (h3M : (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0)
    (hop : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      (CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) • red (bridgeProduct a)
        = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) :
    ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}), 𝔪₁.IsMaximal ∧
      ((3 : ℕ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ := by
  classical
  set v := red (bridgeProduct a) with hv
  set S : Set (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    insert (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})
      {x | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        x = CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})} with hS
  have hkill : ∀ s ∈ S, s • v = 0 := by
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | ⟨ℓ, hℓ, hℓN, rfl⟩
    · exact h3M
    · rw [hv, hop ℓ hℓ hℓN]
      exact hker _ (hT ℓ hℓ hℓN)
  have hv0 : v ≠ 0 := fun h0 => not_three_dvd_coeff_one_bridgeProduct h1 (hker' _ h0)
  have hle : Ideal.span S ≤ Ideal.torsionOf (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M v :=
    Ideal.span_le.mpr fun s hs => (Ideal.mem_torsionOf_iff v s).mpr (hkill s hs)
  have hne : Ideal.span S ≠ ⊤ := by
    intro htop
    have h1mem : (1 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ Ideal.torsionOf _ M v :=
      hle (htop ▸ Submodule.mem_top)
    rw [Ideal.mem_torsionOf_iff, one_smul] at h1mem
    exact hv0 h1mem
  obtain ⟨𝔪₁, h𝔪₁, h𝔪le⟩ := Ideal.exists_le_maximal _ hne
  refine ⟨𝔪₁, h𝔪₁, ?_, fun ℓ hℓ hℓN => ?_⟩
  · have : (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ Ideal.span S :=
      Ideal.subset_span (Set.mem_insert _ _)
    simpa using h𝔪le this
  · exact h𝔪le (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr ⟨ℓ, hℓ, hℓN, rfl⟩)))

end CuspForm

/-! ### The reduction modulo `3` of the integral lattice -/

namespace CuspForm.FormalHeckeReduction

open ModularFormClass

local notation "Γ₀(" N ")" => CongruenceSubgroup.Gamma0 N

variable {N : ℕ} {k : ℤ}

private theorem qCoeff_add (f g : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff_eq, FunLike.coe_add]
  rw [ModularForm.qExpansion_add one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
    f g, map_add]

private theorem qCoeff_zero (n : ℕ) : qCoeff ⇑(0 : CuspForm Γ₀(N) k) n = 0 := by
  simp only [qCoeff_eq, FunLike.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

private theorem qCoeff_zsmul (c : ℤ) (f : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  rw [← Int.cast_smul_eq_zsmul ℂ c f, CuspForm.qCoeff_smul]

private abbrev Lat (N : ℕ) : Submodule ℤ (CuspForm Γ₀(N) 2) := CuspForm.intLattice N 2

private theorem exists_intCast_of_mem {f : CuspForm Γ₀(N) 2} (hf : f ∈ Lat N) (n : ℕ) :
    ∃ m : ℤ, qCoeff ⇑f n = (m : ℂ) :=
  (CuspForm.mem_intLattice_iff f).mp hf n

/-- The integral `q`-expansion of a lattice element. -/
private def intQExpansion (f : Lat N) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (exists_intCast_of_mem f.2 n).choose

private theorem intQExpansion_cast (f : Lat N) (n : ℕ) :
    ((PowerSeries.coeff n (intQExpansion f) : ℤ) : ℂ) = qCoeff ⇑(f : CuspForm Γ₀(N) 2) n := by
  simp only [intQExpansion, PowerSeries.coeff_mk]
  exact (exists_intCast_of_mem f.2 n).choose_spec.symm

private theorem intQExpansion_zero : intQExpansion (0 : Lat N) = 0 := by
  ext n
  have h0 : ((PowerSeries.coeff n (intQExpansion (0 : Lat N)) : ℤ) : ℂ) = 0 := by
    rw [intQExpansion_cast]
    exact qCoeff_zero n
  have : PowerSeries.coeff n (intQExpansion (0 : Lat N)) = 0 := by exact_mod_cast h0
  simpa using this

private theorem intQExpansion_add (f g : Lat N) :
    intQExpansion (f + g) = intQExpansion f + intQExpansion g := by
  ext n
  have h : ((PowerSeries.coeff n (intQExpansion (f + g)) : ℤ) : ℂ)
      = ((PowerSeries.coeff n (intQExpansion f) + PowerSeries.coeff n (intQExpansion g) : ℤ) :
        ℂ) := by
    rw [intQExpansion_cast]
    push_cast
    rw [intQExpansion_cast, intQExpansion_cast]
    exact qCoeff_add (f : CuspForm Γ₀(N) 2) (g : CuspForm Γ₀(N) 2) n
  simpa using Int.cast_injective (α := ℂ) h

private theorem intQExpansion_sub (f g : Lat N) :
    intQExpansion (f - g) = intQExpansion f - intQExpansion g := by
  have hadd := intQExpansion_add (f - g) g
  rw [sub_add_cancel] at hadd
  exact eq_sub_of_add_eq hadd.symm

private theorem coeff_intQExpansion_zsmul (c : ℤ) (f : Lat N) (n : ℕ) :
    PowerSeries.coeff n (intQExpansion (c • f)) = c * PowerSeries.coeff n (intQExpansion f) := by
  have h : ((PowerSeries.coeff n (intQExpansion (c • f)) : ℤ) : ℂ)
      = ((c * PowerSeries.coeff n (intQExpansion f) : ℤ) : ℂ) := by
    rw [intQExpansion_cast, Submodule.coe_smul, qCoeff_zsmul]
    push_cast
    rw [intQExpansion_cast]
  exact Int.cast_injective (α := ℂ) h

/-- The multiples of `3` in the integral lattice. -/
private def threeMultiples (N : ℕ) : Submodule ℤ (Lat N) :=
  LinearMap.range ((3 : ℤ) • (LinearMap.id : Lat N →ₗ[ℤ] Lat N))

private theorem mem_threeMultiples_iff {f : Lat N} :
    f ∈ threeMultiples N ↔ ∃ g : Lat N, (3 : ℤ) • g = f :=
  Iff.rfl

private theorem mem_threeMultiples_iff_dvd {f : Lat N} :
    f ∈ threeMultiples N ↔ ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) := by
  constructor
  · rintro hf n
    obtain ⟨g, rfl⟩ := mem_threeMultiples_iff.mp hf
    rw [coeff_intQExpansion_zsmul]
    exact dvd_mul_right 3 _
  · intro hdvd
    have hmem : (3⁻¹ : ℂ) • (f : CuspForm Γ₀(N) 2) ∈ Lat N := by
      rw [CuspForm.mem_intLattice_iff]
      intro n
      obtain ⟨m, hm⟩ := hdvd n
      refine ⟨m, ?_⟩
      have hcoeff := intQExpansion_cast f n
      rw [hm] at hcoeff
      push_cast at hcoeff
      rw [← qCoeff_eq, CuspForm.qCoeff_smul, ← hcoeff, ← mul_assoc,
        inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_mul]
    refine mem_threeMultiples_iff.mpr ⟨⟨(3⁻¹ : ℂ) • (f : CuspForm Γ₀(N) 2), hmem⟩, ?_⟩
    ext1
    change (3 : ℤ) • ((3⁻¹ : ℂ) • (f : CuspForm Γ₀(N) 2)) = (f : CuspForm Γ₀(N) 2)
    rw [← Int.cast_smul_eq_zsmul ℂ (3 : ℤ), smul_smul]
    norm_num

/-- The integral lattice modulo `3`. -/
private abbrev LatticeMod3 (N : ℕ) : Type := Lat N ⧸ threeMultiples N

private abbrev latticeMk (f : Lat N) : LatticeMod3 N := Submodule.Quotient.mk f

private theorem latticeMk_eq_zero_iff {f : Lat N} :
    latticeMk f = 0 ↔ ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_threeMultiples_iff_dvd

private theorem latticeMk_eq_of_dvd_sub {f g : Lat N}
    (h : ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (intQExpansion g)) :
    latticeMk f = latticeMk g := by
  rw [Submodule.Quotient.eq, mem_threeMultiples_iff_dvd]
  intro n
  rw [intQExpansion_sub, map_sub]
  exact h n

section Action

variable [NeZero N]

private abbrev HA (N : ℕ) [NeZero N] := CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}

/-- The action of the Hecke algebra on the integral lattice: `main`'s
`CuspForm.latticeActionHom` at the primes dividing the level. -/
private abbrev latticeHom (N : ℕ) [NeZero N] : HA N →+* Module.End ℤ (Lat N) :=
  CuspForm.latticeActionHom N {ℓ | ℓ ∣ N}

private theorem latticeHom_apply_coe (T : HA N) (f : Lat N) :
    ((latticeHom N T f : Lat N) : CuspForm Γ₀(N) 2)
      = (T : Module.End ℂ (CuspForm Γ₀(N) 2)) (f : CuspForm Γ₀(N) 2) :=
  rfl

private theorem threeMultiples_le_comap_latticeHom (T : HA N) :
    threeMultiples N ≤ (threeMultiples N).comap (latticeHom N T) := by
  rintro f hf
  obtain ⟨g, rfl⟩ := mem_threeMultiples_iff.mp hf
  exact mem_threeMultiples_iff.mpr ⟨latticeHom N T g, (map_smul (latticeHom N T) _ _).symm⟩

/-- An element of the Hecke algebra, acting on the integral lattice modulo `3`. -/
private def heckeSMulAux (T : HA N) : LatticeMod3 N →ₗ[ℤ] LatticeMod3 N :=
  Submodule.mapQ (threeMultiples N) (threeMultiples N) (latticeHom N T)
    (threeMultiples_le_comap_latticeHom T)

private instance : SMul (HA N) (LatticeMod3 N) := ⟨fun T m => heckeSMulAux T m⟩

private theorem heckeSMul_mk (T : HA N) (f : Lat N) :
    T • latticeMk f = latticeMk (latticeHom N T f) :=
  rfl

private instance : Module (HA N) (LatticeMod3 N) where
  one_smul m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change (1 : HA N) • latticeMk f = latticeMk f
    rw [heckeSMul_mk, map_one]
    rfl
  mul_smul T S m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change (T * S) • latticeMk f = T • S • latticeMk f
    rw [heckeSMul_mk, heckeSMul_mk, heckeSMul_mk, map_mul]
    rfl
  smul_zero T := map_zero (heckeSMulAux T)
  smul_add T m m' := map_add (heckeSMulAux T) m m'
  add_smul T S m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change (T + S) • latticeMk f = T • latticeMk f + S • latticeMk f
    rw [heckeSMul_mk, heckeSMul_mk, heckeSMul_mk, (latticeHom N).map_add]
    rfl
  zero_smul m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change (0 : HA N) • latticeMk f = 0
    rw [heckeSMul_mk, map_zero]
    rfl

private theorem intCast_heckeSMul_mk (z : ℤ) (f : Lat N) :
    ((z : HA N)) • latticeMk f = latticeMk (z • f) := by
  rw [heckeSMul_mk, map_intCast, intCast_apply_eq_smul]

end Action

open Classical in
/-- The reduction of an integral power series modulo `3` into the lattice modulo `3`: the class
of a lattice element congruent to it modulo `3`, or the default `m₀` when there is none. -/
private def latticeReduction (m₀ : LatticeMod3 N) (g : PowerSeries ℤ) : LatticeMod3 N :=
  if h : ∃ f : Lat N, ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g then
    latticeMk h.choose
  else m₀

private theorem latticeReduction_eq_mk (m₀ : LatticeMod3 N) {g : PowerSeries ℤ} {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g) :
    latticeReduction m₀ g = latticeMk f := by
  have hex : ∃ f' : Lat N, ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f') - PowerSeries.coeff n g := ⟨f, hf⟩
  rw [latticeReduction, dite_eq_left hex]
  refine latticeMk_eq_of_dvd_sub fun n => ?_
  have hsplit :
      PowerSeries.coeff n (intQExpansion hex.choose) - PowerSeries.coeff n (intQExpansion f)
        = (PowerSeries.coeff n (intQExpansion hex.choose) - PowerSeries.coeff n g)
          - (PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g) := by ring
  rw [hsplit]
  exact dvd_sub (hex.choose_spec n) (hf n)

private theorem latticeReduction_eq_zero (m₀ : LatticeMod3 N) {g : PowerSeries ℤ}
    (hg : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) : latticeReduction m₀ g = 0 := by
  have h0 : ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion (0 : Lat N)) - PowerSeries.coeff n g := by
    intro n
    rw [intQExpansion_zero]
    simpa using hg n
  rw [latticeReduction_eq_mk m₀ h0, latticeMk_eq_zero_iff]
  intro n
  rw [intQExpansion_zero]
  simp

private theorem latticeReduction_dvd_of_eq_zero {m₀ : LatticeMod3 N} (hm₀ : m₀ ≠ 0)
    (g : PowerSeries ℤ) (hg : latticeReduction m₀ g = 0) :
    (3 : ℤ) ∣ PowerSeries.coeff 1 g := by
  by_cases hex : ∃ f : Lat N, ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g
  · obtain ⟨f, hf⟩ := hex
    rw [latticeReduction_eq_mk m₀ hf, latticeMk_eq_zero_iff] at hg
    have hsplit : PowerSeries.coeff 1 g
        = PowerSeries.coeff 1 (intQExpansion f)
          - (PowerSeries.coeff 1 (intQExpansion f) - PowerSeries.coeff 1 g) := by ring
    rw [hsplit]
    exact dvd_sub (hg 1) (hf 1)
  · rw [latticeReduction, dite_eq_right hex] at hg
    exact absurd hg hm₀

private theorem latticeMk_realization_ne_zero {a : ℕ → ℤ} (ha : a 1 = 1) {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a)) :
    latticeMk f ≠ 0 := by
  intro h0
  rw [latticeMk_eq_zero_iff] at h0
  refine not_three_dvd_coeff_one_bridgeProduct ha ?_
  have hsplit : PowerSeries.coeff 1 (bridgeProduct a)
      = PowerSeries.coeff 1 (intQExpansion f)
        - (PowerSeries.coeff 1 (intQExpansion f) - PowerSeries.coeff 1 (bridgeProduct a)) := by
    ring
  rw [hsplit]
  exact dvd_sub (h0 1) (hf 1)

private theorem exists_lat_of_isLatticeRealized {a : ℕ → ℤ} (h : CuspForm.IsLatticeRealized N a) :
    ∃ f : Lat N, ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a) := by
  obtain ⟨f, -, af, haf, hcong⟩ := h
  have hmem : f ∈ Lat N := (CuspForm.mem_intLattice_iff f).mpr fun n => ⟨af n, (haf n).symm⟩
  refine ⟨⟨f, hmem⟩, fun n => ?_⟩
  have hcast : ((PowerSeries.coeff n (intQExpansion ⟨f, hmem⟩) : ℤ) : ℂ) = (af n : ℂ) := by
    rw [intQExpansion_cast, haf n]
  rw [Int.cast_injective (α := ℂ) hcast]
  exact hcong n

section Clauses

variable [NeZero N]

private theorem intQExpansion_latticeHom_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : Lat N) :
    intQExpansion (latticeHom N (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) f)
      = PowerSeries.heckeT ℓ 2 (intQExpansion f) := by
  ext n
  have hcast :
      ((PowerSeries.coeff n
          (intQExpansion (latticeHom N (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) f)) : ℤ) : ℂ)
        = ((PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f)) : ℤ) : ℂ) := by
    rw [intQExpansion_cast, latticeHom_apply_coe, CuspForm.heckeAlgebra.coe_T,
      CuspForm.coe_heckeTLin_apply,
      ModularFormClass.qCoeff_heckeT _ (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
        hℓ.ne_zero,
      ModularForm.coeffHeckeT_apply, PowerSeries.coeff_heckeT]
    push_cast
    rw [intQExpansion_cast, mul_comm n ℓ]
    by_cases hdvd : ℓ ∣ n
    · rw [ite_eq_left hdvd, ite_eq_left hdvd, intQExpansion_cast]
      norm_num
    · rw [ite_eq_right hdvd, ite_eq_right hdvd]
      simp
  exact Int.cast_injective (α := ℂ) hcast

private theorem heckeSMul_latticeReduction {a : ℕ → ℤ} {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a))
    (m₀ : LatticeMod3 N) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : HA N)) •
        latticeReduction m₀ (bridgeProduct a)
      = latticeReduction m₀
          (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  rw [latticeReduction_eq_mk m₀ hf, sub_smul, heckeSMul_mk, intCast_heckeSMul_mk,
    ← Submodule.Quotient.mk_sub]
  symm
  refine latticeReduction_eq_mk m₀ fun n => ?_
  rw [intQExpansion_sub, map_sub, intQExpansion_latticeHom_T, coeff_intQExpansion_zsmul,
    map_sub]
  have hsm : PowerSeries.coeff n (a ℓ • bridgeProduct a)
      = a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    rw [map_zsmul, zsmul_eq_mul, Int.cast_id]
  rw [hsm]
  have hH : (3 : ℤ) ∣ PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f))
      - PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a)) := by
    rw [← map_sub, ← map_sub, PowerSeries.coeff_heckeT]
    refine dvd_add ?_ (Dvd.dvd.mul_left ?_ _)
    · simpa using hf (ℓ * n)
    · split_ifs
      · simpa using hf (n / ℓ)
      · simp
  have hS : (3 : ℤ) ∣ a ℓ * PowerSeries.coeff n (intQExpansion f)
      - a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    rw [← mul_sub]
    exact Dvd.dvd.mul_left (hf n) _
  have hsplit : PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f))
        - a ℓ * PowerSeries.coeff n (intQExpansion f)
        - (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
          - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      = (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f))
          - PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a)))
        - (a ℓ * PowerSeries.coeff n (intQExpansion f)
          - a ℓ * PowerSeries.coeff n (bridgeProduct a)) := by
    ring
  rw [hsplit]
  exact dvd_sub hH hS

private theorem three_heckeSMul_latticeReduction (m₀ : LatticeMod3 N) {a : ℕ → ℤ} {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣
      PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a)) :
    (3 : HA N) • latticeReduction m₀ (bridgeProduct a) = 0 := by
  rw [latticeReduction_eq_mk m₀ hf]
  have h3 : (3 : HA N) = ((3 : ℤ) : HA N) := by rw [Int.cast_ofNat]
  rw [h3, intCast_heckeSMul_mk, latticeMk_eq_zero_iff]
  intro n
  rw [coeff_intQExpansion_zsmul]
  exact dvd_mul_right 3 _

end Clauses

end CuspForm.FormalHeckeReduction

namespace CuspForm

open FormalHeckeReduction in
/-- For `N ≠ 0`, a lattice realization of `bridgeProduct a` with `a 1 = 1` gives some module `M`
over the Hecke algebra away from the level (in the proof, the integral lattice modulo `3`) with a
reduction map from integral power series that kills the series divisible by `3`, detects
`3`-divisibility of the first coefficient, is killed by `3` at `bridgeProduct a`, and on which
`T_ℓ - a ℓ` acts on `bridgeProduct a` as the formal operator `T_ℓ - a ℓ` does. -/
theorem exists_reductionModule_of_isLatticeRealized {N : ℕ} [NeZero N]
    {a : ℕ → ℤ} (h1 : a 1 = 1) (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M)
      (red : PowerSeries ℤ → M),
      (∀ g, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0) ∧
      (∀ g, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g) ∧
      (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        (CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
            ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) • red (bridgeProduct a)
          = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  obtain ⟨fF, hfF⟩ := exists_lat_of_isLatticeRealized hreal
  exact ⟨LatticeMod3 N, inferInstance, inferInstance, latticeReduction (latticeMk fF),
    fun g hg => latticeReduction_eq_zero _ hg,
    fun g hg => latticeReduction_dvd_of_eq_zero (latticeMk_realization_ne_zero h1 hfF) g hg,
    three_heckeSMul_latticeReduction _ hfF,
    fun ℓ hℓ hℓN => heckeSMul_latticeReduction hfF _ ℓ hℓ hℓN⟩

end CuspForm

/-! ### Formal eigensystems with nebentypus `χ₋₃` -/

namespace FormalHecke.IsEigensystem

private theorem three_dvd_natCast_sub_chiNegThree_cast (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by
  have h : (3 : ℤ) ∣ (ℓ : ℤ) - chiNegThree ℓ := by
    simp only [chiNegThree]
    split_ifs <;> omega
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : R), ?_⟩
  have h := congrArg (fun z : ℤ => (z : R)) hc
  push_cast at h
  convert h using 2

private theorem three_dvd_coeff_heckeT_two_sub_residual {R : Type*} [CommRing R] (a : ℕ → R)
    {ℓ : ℕ} (eℓ : R)
    (hrec : ∀ n : ℕ, a (ℓ * n) + eℓ * (if ℓ ∣ n then a (n / ℓ) else 0) = a ℓ * a n)
    (n : ℕ) :
    (3 : R) ∣ (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
        - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      - ((ℓ : R) - eℓ) * (if ℓ ∣ n then a (n / ℓ) else 0) := by
  have hA : ∀ m : ℕ, (3 : R) ∣ PowerSeries.coeff m (bridgeProduct a) - a m :=
    three_dvd_coeff_bridgeProduct_sub a
  have hD : (3 : R) ∣ (if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (bridgeProduct a) else 0)
      - (if ℓ ∣ n then a (n / ℓ) else 0) := by
    split
    · exact hA (n / ℓ)
    · simp
  have hkey : (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
        - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      - ((ℓ : R) - eℓ) * (if ℓ ∣ n then a (n / ℓ) else 0)
      = (PowerSeries.coeff (ℓ * n) (bridgeProduct a) - a (ℓ * n))
        + (ℓ : R) * ((if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (bridgeProduct a) else 0)
            - (if ℓ ∣ n then a (n / ℓ) else 0))
        - a ℓ * (PowerSeries.coeff n (bridgeProduct a) - a n) := by
    rw [PowerSeries.coeff_heckeT, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    linear_combination hrec n
  rw [hkey]
  exact dvd_sub (dvd_add (hA (ℓ * n)) (hD.mul_left (ℓ : R))) ((hA n).mul_left (a ℓ))

/-- Let `a` be a formal Hecke eigensystem over a commutative ring `R`, with nebentypus values
`χ₋₃(ℓ)` at the primes `ℓ ∤ N` and `0` at the primes `ℓ ∣ N`, where the recursion reads
`a (ℓ n) = a ℓ · a n`. Then for every prime `ℓ ∤ N` the series `bridgeProduct a` satisfies the
formal weight-two `T_ℓ` eigenvalue equation with eigenvalue `a ℓ` modulo `3`: every coefficient of
`T_ℓ (bridgeProduct a) - a ℓ • bridgeProduct a` is divisible by `3`. -/
theorem three_dvd_coeff_heckeT_bridgeProduct_sub_smul
    {R : Type*} [CommRing R] {N : ℕ} {a : ℕ → R}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : R)) a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  have hrec : ∀ m : ℕ,
      a (ℓ * m) + ((chiNegThree ℓ : ℤ) : R) * (if ℓ ∣ m then a (m / ℓ) else 0)
        = a ℓ * a m := by
    simpa only [ite_eq_right hℓN] using heig.2 ℓ hℓ
  have h1 := three_dvd_coeff_heckeT_two_sub_residual a ((chiNegThree ℓ : ℤ) : R) hrec n
  have h2 : (3 : R) ∣ ((ℓ : R) - ((chiNegThree ℓ : ℤ) : R)) *
      (if ℓ ∣ n then a (n / ℓ) else 0) :=
    (three_dvd_natCast_sub_chiNegThree_cast R ℓ).mul_right _
  rw [map_sub, map_smul, smul_eq_mul]
  simpa using dvd_add h1 h2

end FormalHecke.IsEigensystem

end

end
