/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_TaylorWiles_Primes.lean`,
`Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean`,
`Definitions/Def_FrobeniusDensity_BadPrimes.lean`,
`Definitions/Def_FrobeniusDensity_PrimeSums.lean`,
`Theorems/Thm_FrobeniusDensity_degOneAsymptotic.lean`,
`Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean`,
`Theorems/Thm_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer.lean`
and the corresponding `P2M/Sol/S_FrobeniusDensity_*.lean` proof files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer

public import Mathlib.RingTheory.Frobenius
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Frobenius density for degree-one primes

For a Galois number field, the degree-one prime counting function is
assembled from ideal and prime sums over the ring of integers.  The
prime sum has the same logarithmic pole at `s = 1` as the Dedekind zeta
function; discarding the finitely many bad (ramified or small) primes and
the higher-degree primes leaves the degree-one sum, whose
`log (s - 1)`-shifted form is bounded near `1`.  A separate finite-group
count gives `|conj class| * |centralizer| = |G|` for every group element.
-/

@[expose] public section

noncomputable section



namespace Matrix

variable {R : Type*} [CommRing R]

theorem sq_eq_trace_smul_sub_det_smul_one (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem pow_add_two_eq_trace_smul_sub_det_smul (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    M ^ (k + 2) = M.trace • M ^ (k + 1) - M.det • M ^ k := by
  have h : M ^ (k + 2) = M ^ k * M ^ 2 := by rw [← pow_add]
  rw [h, sq_eq_trace_smul_sub_det_smul_one, Matrix.mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    (M ^ (k + 2)).trace = M.trace * (M ^ (k + 1)).trace - M.det * (M ^ k).trace := by
  rw [pow_add_two_eq_trace_smul_sub_det_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

def HasDistinctRationalEigenvalues (M : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ∃ α β : R, α ≠ β ∧ M.trace = α + β ∧ M.det = α * β

end Matrix

namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

abbrev ratPrimeIdeal (ℓ : ℕ) : Ideal ℤ := Ideal.span {(ℓ : ℤ)}

theorem ratPrimeIdeal_ne_bot {ℓ : ℕ} (hℓ : ℓ.Prime) : ratPrimeIdeal ℓ ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ.ne_zero

instance isMaximal_ratPrimeIdeal (ℓ : ℕ) [Fact ℓ.Prime] : (ratPrimeIdeal ℓ).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp Fact.out).irreducible

variable {L}

omit [IsGalois ℚ L] in

theorem finite_quotient_of_ne_bot {Q : Ideal (𝓞 L)} (hQ : Q ≠ ⊥) : Finite (𝓞 L ⧸ Q) :=
  Ring.HasFiniteQuotients.finiteQuotient hQ

omit [IsGalois ℚ L] in

theorem ne_bot_of_liesOver_ratPrimeIdeal {ℓ : ℕ} (hℓ : ℓ.Prime) {Q : Ideal (𝓞 L)}
    [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] : Q ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (ratPrimeIdeal_ne_bot hℓ) Q

variable (L)

def RealizesCyclicAt (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : Prop :=
  ∃ _ : ℓ.Prime, ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
    (_ : Finite (𝓞 L ⧸ Q)),
    ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)

def Statement : Prop :=
  ∀ (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ), ∃ ℓ : ℕ, ℓ ∉ S ∧ RealizesCyclicAt L σ ℓ

end FrobeniusDensity

namespace TaylorWiles

open NumberField Ideal FrobeniusDensity

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
variable {𝕜 : Type*} [Field 𝕜]

variable (L) in

abbrev ResidualRep (𝕜 : Type*) [Field 𝕜] := (L ≃ₐ[ℚ] L) →* Matrix (Fin 2) (Fin 2) 𝕜

variable (ρ : ResidualRep L 𝕜) (p n : ℕ)

def IsTaylorWilesPrime (q : ℕ) : Prop :=
  q.Prime ∧ q ≡ 1 [MOD p ^ n] ∧
    ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal q))
      (_ : Finite (𝓞 L ⧸ Q)),
      (ρ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).HasDistinctRationalEigenvalues

structure Seed (S : Finset ℕ) where

  σ : L ≃ₐ[ℚ] L

  regular : (ρ σ).HasDistinctRationalEigenvalues

  congruent : ∀ ℓ : ℕ, ℓ ∉ S → RealizesCyclicAt L σ ℓ → ℓ ≡ 1 [MOD p ^ n]

def SeedExists (S : Finset ℕ) : Prop := Nonempty (Seed ρ p n S)

end TaylorWiles


open scoped NNReal
open Filter Topology Asymptotics

namespace FrobeniusDensity

open NumberField Ideal

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

noncomputable def degOneCount (ℓ : ℕ) : ℕ :=
  if ℓ.Prime then
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard
  else 0

end DegOneCount

section AnalyticInput

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

def DegOneAsymptotic : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[ℚ] L)) (S₀ : Finset ℕ),
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

end AnalyticInput

end FrobeniusDensity


namespace FrobeniusDensity

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

theorem card_quotient_ratPrimeIdeal (ℓ : ℕ) :
    Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [ratPrimeIdeal, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

theorem card_quotient_under_int {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
  rw [← Q.over_def (ratPrimeIdeal ℓ), card_quotient_ratPrimeIdeal]

section Ramified

variable {K : Type*} [Field K] [NumberField K]

lemma finite_setOf_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}.Finite := by
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      {v | v.asIdeal ∣ I} := fun v _ w _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (normalizedFactors I).toFinset.finite_toSet.subset ?_
  rintro J ⟨v, hv, rfl⟩
  simpa only [Finset.mem_coe, Multiset.mem_toFinset] using
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩

variable (L : Type*) [Field L] [NumberField L]

theorem exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) :
    ∃ x : 𝓞 L, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 L, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) z
  have hx : g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x :=
    congrArg (algebraMap (𝓞 L) L) (hcon x)
  have hy' : g (algebraMap (𝓞 L) L y) = algebraMap (𝓞 L) L y :=
    congrArg (algebraMap (𝓞 L) L) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

theorem finite_setOf_inertia_ne_bot_heightOneSpectrum :
    {v : HeightOneSpectrum (𝓞 L) | v.asIdeal.inertia (L ≃ₐ[ℚ] L) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : L ≃ₐ[ℚ] L // g ≠ 1} => exists_smul_ne L g.2
  refine Set.Finite.subset (Set.Finite.biUnion
    (Set.finite_univ (α := {g : L ≃ₐ[ℚ] L // g ≠ 1}))
    (fun g _ => finite_setOf_dvd (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨g, hgmem, hgne⟩ := (v.asIdeal.inertia (L ≃ₐ[ℚ] L)).bot_or_exists_ne_one.resolve_left hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

noncomputable def badPrimes : Finset ℕ :=
  insert 0 (insert 1 (((finite_setOf_inertia_ne_bot_heightOneSpectrum L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

theorem inertia_eq_bot_of_notMem_badPrimes {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓbad : ℓ ∉ badPrimes L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  by_contra hcon
  apply hℓbad
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨Q, inferInstance, hQbot⟩, hcon, card_quotient_under_int (ℓ := ℓ) Q⟩

end Ramified

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem degOneCount_of_not_prime {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) : degOneCount K ℓ = 0 := by
  rw [degOneCount, if_neg hℓ]

omit [NumberField K] in
theorem degOneCount_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    degOneCount K ℓ
      = {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard := by
  rw [degOneCount, if_pos hℓ]

end DegOneCount

section Frob

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

theorem isConj_arithFrobAt_of_liesOver {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₁ Q₂ : Ideal (𝓞 L))
    [Q₁.IsPrime] [Q₂.IsPrime] [Q₁.LiesOver (ratPrimeIdeal ℓ)] [Q₂.LiesOver (ratPrimeIdeal ℓ)] :
    letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    IsConj (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₂) := by
  letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  exact isConj_arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁ Q₂
    ((Q₁.over_def (ratPrimeIdeal ℓ)).symm.trans (Q₂.over_def (ratPrimeIdeal ℓ)))

variable (L)

theorem realizesCyclicAt_of_exists (σ : L ≃ₐ[ℚ] L) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime] [Q₀.LiesOver (ratPrimeIdeal ℓ)]
    (h : ∀ _ : Finite (𝓞 L ⧸ Q₀),
      ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)) :
    RealizesCyclicAt L σ ℓ := by
  refine ⟨hℓ, fun Q hQp hQl hQf => ?_⟩
  haveI : Finite (𝓞 L ⧸ Q₀) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := h ‹_›
  exact ⟨k, hk, hconj.trans (isConj_arithFrobAt_of_liesOver hℓ Q₀ Q)⟩

end Frob

end FrobeniusDensity


open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
  UniqueFactorizationMonoid
open scoped ENNReal NNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

noncomputable def normRpow (s : ℝ) (I : Ideal (𝓞 K)) : ℝ≥0∞ :=
  (Ideal.absNorm I : ℝ≥0∞) ^ (-s)

noncomputable def idealSum (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, normRpow K s I.1

noncomputable def primeSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal

noncomputable def primeSqSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal ^ 2

variable {K}

def IsFactoredBy (T : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → v ∈ T

variable (K) in

noncomputable def factoredSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal (𝓞 K) // IsFactoredBy T I}, normRpow K s I.1

lemma one_le_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 1 ≤ Ideal.absNorm I :=
  Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

variable (K) in

noncomputable def primeFactors (I : Ideal (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 K)) :=
  if hI : I = ⊥ then ∅ else (finite_setOf_dvd hI).toFinset

variable (K)

theorem exists_prime_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.LiesOver (ratPrimeIdeal ℓ) := by
  have hJp : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hmem : (Ideal.absNorm v.asIdeal : ℤ) ∈ v.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
    exact Ideal.absNorm_mem v.asIdeal
  have hJne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Int.natCast_eq_zero] at hmem
    exact Nat.one_le_iff_ne_zero.mp (one_le_absNorm v.ne_bot) hmem
  refine ⟨(Submodule.IsPrincipal.generator (v.asIdeal.under ℤ)).natAbs,
    Int.prime_iff_natAbs_prime.mp
      (Submodule.IsPrincipal.prime_generator_of_isPrime _ hJne), ⟨?_⟩⟩
  rw [ratPrimeIdeal, Int.span_natAbs, Ideal.span_singleton_generator]

variable {K}

noncomputable def ratBelow (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (exists_prime_liesOver K v).choose

theorem ratBelow_prime (v : HeightOneSpectrum (𝓞 K)) : (ratBelow v).Prime :=
  (exists_prime_liesOver K v).choose_spec.1

instance liesOver_ratBelow (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.LiesOver (ratPrimeIdeal (ratBelow v)) :=
  (exists_prime_liesOver K v).choose_spec.2

variable (K)

noncomputable def degOneSum (S₀ : Finset ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)

noncomputable def cutSum (S₀ : Finset ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)

noncomputable def tailSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K),
    if (Ideal.absNorm v.asIdeal).Prime then 0 else normRpow K s v.asIdeal

noncomputable def tailConst : ℝ≥0∞ :=
  ∑' ℓ : ℕ, if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0

noncomputable def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

noncomputable def zetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else idealCount K n * (n : ℝ) ^ (-s)

end FrobeniusDensity


open scoped ENNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm K s n := by
  unfold zetaTerm
  split
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private lemma tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  simp only [idealCount]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private lemma isBigO_sum_of_tendsto_div :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ))
      =O[atTop] (fun n => (n : ℝ) ^ (1:ℝ)) := by
  simp only [Real.rpow_one]
  rw [isBigO_iff]

  have hbdd : BddAbove (Set.range (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n)) :=
    (tendsto_sum_idealCount_div K).bddAbove_range
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg hn'.le,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  calc ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)
      = ((∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) * n := by field_simp
    _ ≤ C * n := mul_le_mul_of_nonneg_right (hC ⟨n, rfl⟩) hn'.le
    _ ≤ max C 0 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le

private lemma LSeriesSummable_idealCount {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    ?_ (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  exact isBigO_sum_of_tendsto_div K

private lemma term_eq_ofReal_zetaTerm (s : ℝ) (n : ℕ) :
    LSeries.term (fun n => (idealCount K n : ℂ)) s n = (zetaTerm K s n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zetaTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, zetaTerm, if_neg hn]
    have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_cpow hpos.le,
      Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_zetaTerm {s : ℝ} (hs : 1 < s) : Summable (zetaTerm K s) := by
  have h : Summable fun n => ((zetaTerm K s n : ℝ) : ℂ) := by
    refine (LSeriesSummable_idealCount K hs).congr fun n => ?_
    exact term_eq_ofReal_zetaTerm K s n
  exact Complex.summable_ofReal.mp h

private def NormFiber (n : ℕ) : Type _ :=
  {I : {I : Ideal (𝓞 K) // I ≠ ⊥} // Ideal.absNorm I.1 = n}

private noncomputable def normFiberEquiv :
    (Σ n : ℕ, NormFiber K n) ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} where
  toFun p := p.2.1
  invFun I := ⟨Ideal.absNorm I.1, I, rfl⟩
  left_inv p := by rcases p with ⟨n, I, rfl⟩; rfl
  right_inv I := rfl

private lemma tsum_normFiber (s : ℝ) (n : ℕ) :
    ∑' I : NormFiber K n, normRpow K s I.1.1 = ENNReal.ofReal (zetaTerm K s n) := by
  have hconst : ∀ I : NormFiber K n, normRpow K s I.1.1 = (n : ℝ≥0∞) ^ (-s) := fun I => by
    rw [normRpow, I.2]
  rw [tsum_congr hconst, ENNReal.tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty (NormFiber K 0) := ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp [zetaTerm, ENat.card_eq_coe_natCard]
  · have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hequiv : NormFiber K n ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      { toFun := fun I => ⟨I.1.1, I.2⟩
        invFun := fun I => ⟨⟨I.1, fun h => hn (by rw [← I.2, h, Ideal.absNorm_bot])⟩, I.2⟩
        left_inv := fun I => rfl
        right_inv := fun I => rfl }
    have hfin : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    have hfin' : Finite (NormFiber K n) := Finite.of_equiv _ hequiv.symm
    rw [zetaTerm, if_neg hn, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_pos hpos, ENat.card_eq_coe_natCard, Nat.card_congr hequiv]
    simp only [ENNReal.ofReal_natCast, idealCount]
    norm_cast

private lemma idealSum_eq_tsum_zetaTerm (s : ℝ) :
    idealSum K s = ∑' n : ℕ, ENNReal.ofReal (zetaTerm K s n) := by
  rw [idealSum, ← (normFiberEquiv K).tsum_eq (fun I => normRpow K s I.1),
    ENNReal.tsum_sigma']
  exact tsum_congr fun n => tsum_normFiber K s n

end FrobeniusDensity

theorem FrobeniusDensity.idealSum_ne_top (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by
  rw [FrobeniusDensity.idealSum_eq_tsum_zetaTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (FrobeniusDensity.zetaTerm_nonneg K s)
      (FrobeniusDensity.summable_zetaTerm K hs)]
  exact ENNReal.ofReal_ne_top


open scoped ENNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

private def PrimeNormFiber (ℓ : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // Ideal.absNorm v.asIdeal = ℓ}

private noncomputable def primeNormFiberEquiv :
    (Σ ℓ : ℕ, PrimeNormFiber K ℓ) ≃ HeightOneSpectrum (𝓞 K) where
  toFun p := p.2.1
  invFun v := ⟨Ideal.absNorm v.asIdeal, v, rfl⟩
  left_inv p := by rcases p with ⟨ℓ, v, rfl⟩; rfl
  right_inv v := rfl

private scoped instance (ℓ : ℕ) : Finite (PrimeNormFiber K ℓ) := by
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = ℓ} :=
    (Ideal.finite_setOfPred_absNorm_eq ℓ).to_subtype
  exact Finite.of_injective
    (fun v => (⟨v.1.asIdeal, v.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = ℓ}))
    fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))

private theorem liesOver_of_absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hv : Ideal.absNorm v.asIdeal = ℓ) : v.asIdeal.LiesOver (ratPrimeIdeal ℓ) := by
  refine ⟨?_⟩
  have := Ideal.span_singleton_absNorm (I := v.asIdeal) (by rw [hv]; exact hℓ)
  rw [hv] at this
  exact this

private theorem natCard_primeNormFiber {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Nat.card (PrimeNormFiber K ℓ) = degOneCount K ℓ := by
  rw [degOneCount_of_prime K hℓ, ← Nat.card_coe_set_eq]
  have hcard : ∀ I : Ideal (𝓞 K), Nat.card ((𝓞 K) ⧸ I) = Ideal.absNorm I := fun I =>
    (Submodule.cardQuot_apply _).symm.trans (Ideal.absNorm_apply I).symm
  refine Nat.card_congr ⟨fun v => ⟨v.1.asIdeal, ?_⟩, fun 𝔮 => ⟨⟨𝔮.1, 𝔮.2.1.1, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact ⟨⟨v.1.isPrime, liesOver_of_absNorm_eq K hℓ v.2⟩, (hcard _).trans v.2⟩
  · haveI := 𝔮.2.1.1
    haveI := 𝔮.2.1.2
    exact ne_bot_of_liesOver_ratPrimeIdeal hℓ
  · exact (hcard 𝔮.1).symm.trans 𝔮.2.2
  · intro v; rfl
  · intro 𝔮; rfl

private theorem tsum_degOne_eq (s : ℝ) :
    (∑' v : HeightOneSpectrum (𝓞 K),
        if (Ideal.absNorm v.asIdeal).Prime then normRpow K s v.asIdeal else 0)
      = ∑' ℓ : ℕ, (degOneCount K ℓ : ℝ≥0∞) * (ℓ : ℝ≥0∞) ^ (-s) := by
  rw [← (primeNormFiberEquiv K).tsum_eq
    (fun v => if (Ideal.absNorm v.asIdeal).Prime then normRpow K s v.asIdeal else 0),
    ENNReal.tsum_sigma']
  refine tsum_congr fun ℓ => ?_
  have hfib : ∀ v : PrimeNormFiber K ℓ,
      (if (Ideal.absNorm (primeNormFiberEquiv K ⟨ℓ, v⟩).asIdeal).Prime
        then normRpow K s (primeNormFiberEquiv K ⟨ℓ, v⟩).asIdeal else 0)
      = (if ℓ.Prime then (ℓ : ℝ≥0∞) ^ (-s) else 0) := by
    intro v
    have hv : Ideal.absNorm (primeNormFiberEquiv K ⟨ℓ, v⟩).asIdeal = ℓ := v.2
    rw [normRpow, hv]
  rw [tsum_congr hfib, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  by_cases hℓ : ℓ.Prime
  · rw [if_pos hℓ, natCard_primeNormFiber K hℓ]
    norm_cast
  · rw [if_neg hℓ, mul_zero, degOneCount_of_not_prime K hℓ, Nat.cast_zero, zero_mul]

end FrobeniusDensity


theorem FrobeniusDensity.primeSum_eq_degOneSum_add (K : Type*) [Field K] [NumberField K]
    (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by
  have hsplit : primeSum K s
      = (∑' v : HeightOneSpectrum (𝓞 K),
          if (Ideal.absNorm v.asIdeal).Prime then normRpow K s v.asIdeal else 0)
        + tailSum K s := by
    rw [primeSum, tailSum, ← ENNReal.tsum_add]
    refine tsum_congr fun v => ?_
    by_cases hv : (Ideal.absNorm v.asIdeal).Prime
    · rw [if_pos hv, if_pos hv, add_zero]
    · rw [if_neg hv, if_neg hv, zero_add]
  rw [hsplit, tsum_degOne_eq, degOneSum, cutSum, ← ENNReal.tsum_add]
  congr 1
  refine tsum_congr fun ℓ => ?_
  by_cases hℓ : ℓ ∈ S₀
  · rw [if_pos hℓ, if_pos hℓ, zero_mul, zero_add]
  · rw [if_neg hℓ, if_neg hℓ, zero_mul, add_zero]


open scoped ENNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

private lemma primeSum_le_idealSum (s : ℝ) : primeSum K s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (⟨v.asIdeal, v.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) :=
    fun v w h => HeightOneSpectrum.ext (by simpa using congrArg Subtype.val h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

private lemma degOneSum_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) : degOneSum K S₀ s ≠ ⊤ := by
  have h1 : degOneSum K S₀ s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K S₀ s, add_assoc]
    exact self_le_add_right _ _
  exact (h1.trans_lt ((primeSum_le_idealSum K s).trans_lt
    (idealSum_ne_top K hs).lt_top)).ne

omit [NumberField K] in
private theorem toReal_term (S₀ : Finset ℕ) (s : ℝ) (ℓ : ℕ) :
    ((if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)).toReal
      = (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

end FrobeniusDensity


theorem FrobeniusDensity.summable_degOne_term (K : Type*) [Field K] [NumberField K]
    (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) :=
  (ENNReal.summable_toReal (degOneSum_ne_top K S₀ hs)).congr (toReal_term K S₀ s)


open scoped ENNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

private lemma dedekindZeta_eq_ofReal_tsum (s : ℝ) :
    dedekindZeta K s = ((∑' n, zetaTerm K s n : ℝ) : ℂ) := by
  rw [dedekindZeta, LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => term_eq_ofReal_zetaTerm K s n

private lemma idealSum_toReal_eq {s : ℝ} (hs : 1 < s) :
    (idealSum K s).toReal = ∑' n, zetaTerm K s n := by
  rw [idealSum_eq_tsum_zetaTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (zetaTerm_nonneg K s) (summable_zetaTerm K hs),
    ENNReal.toReal_ofReal]
  exact tsum_nonneg (zetaTerm_nonneg K s)

private theorem tendsto_sub_one_mul_idealSum :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by
  rw [← Filter.tendsto_ofReal_iff]
  refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [idealSum_toReal_eq K hs, dedekindZeta_eq_ofReal_tsum]
  push_cast
  ring

end FrobeniusDensity



open scoped ENNReal NNReal

namespace FrobeniusDensity

variable {K : Type*} [Field K] [NumberField K]

section normRpow

variable {s : ℝ}

lemma two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  rw [Nat.two_le_iff]
  exact ⟨fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h),
    fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)⟩

lemma one_le_cast_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (1 : ℝ≥0∞) ≤ (Ideal.absNorm I : ℝ≥0∞) := by
  exact_mod_cast one_le_absNorm hI

lemma normRpow_le_one {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hs : 0 ≤ s) : normRpow K s I ≤ 1 := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [normRpow]
  · exact ENNReal.rpow_le_one_of_one_le_of_neg (one_le_cast_absNorm hI) (neg_neg_iff_pos.mpr hs)

lemma normRpow_ne_top {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hs : 0 ≤ s) : normRpow K s I ≠ ∞ :=
  ((normRpow_le_one hI hs).trans_lt ENNReal.one_lt_top).ne

lemma normRpow_pos {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 0 < normRpow K s I :=
  ENNReal.rpow_pos (zero_lt_one.trans_le (one_le_cast_absNorm hI)) (by simp)

lemma one_lt_cast_absNorm (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℝ≥0∞) < (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two (two_le_absNorm v)

lemma normRpow_lt_one (v : HeightOneSpectrum (𝓞 K)) (hs : 0 < s) :
    normRpow K s v.asIdeal < 1 :=
  ENNReal.rpow_lt_one_of_one_lt_of_neg (one_lt_cast_absNorm v) (neg_neg_iff_pos.mpr hs)

lemma normRpow_top : normRpow K s (⊤ : Ideal (𝓞 K)) = 1 := by
  simp [normRpow]

lemma normRpow_mul {I J : Ideal (𝓞 K)} :
    normRpow K s (I * J) = normRpow K s I * normRpow K s J := by
  unfold normRpow
  rw [map_mul, Nat.cast_mul, ENNReal.mul_rpow_of_ne_top (by simp) (by simp)]

lemma normRpow_pow {I : Ideal (𝓞 K)} (e : ℕ) :
    normRpow K s (I ^ e) = normRpow K s I ^ e := by
  induction e with
  | zero => simpa using normRpow_top
  | succ n ih => rw [pow_succ, pow_succ, normRpow_mul, ih]

end normRpow

section Factors
lemma mem_primeFactors {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ primeFactors K I ↔ v.asIdeal ∣ I := by
  simp [primeFactors, hI]

lemma isFactoredBy_primeFactors {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    IsFactoredBy (primeFactors K I) I :=
  ⟨hI, fun _ hv => (mem_primeFactors hI).mpr hv⟩

namespace IsFactoredBy
omit [NumberField K] in
private lemma _root_.FrobeniusDensity.IsFactoredBy.mono
    {T T' : Finset (HeightOneSpectrum (𝓞 K))} (hTT' : T ⊆ T')
    {I : Ideal (𝓞 K)} (hI : IsFactoredBy T I) : IsFactoredBy T' I :=
  ⟨hI.1, fun v hv => hTT' (hI.2 v hv)⟩

end IsFactoredBy
omit [NumberField K] in
lemma isFactoredBy_top (T : Finset (HeightOneSpectrum (𝓞 K))) :
    IsFactoredBy T (⊤ : Ideal (𝓞 K)) := by
  refine ⟨by simp, fun v hv => absurd ?_ v.isPrime.ne_top⟩
  exact top_le_iff.mp (Ideal.le_of_dvd hv)

lemma eq_top_of_isFactoredBy_empty {I : Ideal (𝓞 K)}
    (hI : IsFactoredBy (∅ : Finset (HeightOneSpectrum (𝓞 K))) I) : I = ⊤ := by
  by_contra hne
  obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI.1
    fun h => hne (Ideal.isUnit_iff.mp h)
  obtain ⟨hP1, hP2⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mp hP
  exact absurd (hI.2 ⟨P, Ideal.isPrime_of_prime hP1, hP1.ne_zero⟩ hP2) (Finset.notMem_empty _)

end Factors

section EulerProduct

variable {s : ℝ}

noncomputable def consFactored (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T)
    (p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I}) :
    {I : Ideal (𝓞 K) // IsFactoredBy (T.cons v hv) I} := by
  refine ⟨v.asIdeal ^ p.1 * p.2.1, mul_ne_zero (pow_ne_zero _ v.ne_bot) p.2.2.1, fun w hw => ?_⟩
  rcases (Prime.dvd_mul w.prime).mp hw with hw | hw
  · have h1 : w.asIdeal ∣ v.asIdeal := w.prime.dvd_of_dvd_pow hw
    have h2 : w = v := HeightOneSpectrum.ext <|
      associated_iff_eq.mp ((Prime.dvd_prime_iff_associated w.prime v.prime).mp h1)
    simp [h2]
  · exact Finset.mem_cons_of_mem (p.2.2.2 w hw)

lemma consFactored_injective (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    Function.Injective (consFactored v hv) := by
  classical
  have hcount : ∀ (e : ℕ) (J : {I : Ideal (𝓞 K) // IsFactoredBy T I}),
      Multiset.count v.asIdeal (normalizedFactors (v.asIdeal ^ e * J.1)) = e := by
    intro e J
    rw [normalizedFactors_mul (pow_ne_zero _ v.ne_bot) J.2.1, normalizedFactors_pow,
      normalizedFactors_irreducible v.prime.irreducible, Multiset.count_add,
      Multiset.count_nsmul, normalize_eq, Multiset.count_singleton_self, mul_one,
      Multiset.count_eq_zero_of_notMem, add_zero]
    intro hmem
    exact hv (J.2.2 v ((UniqueFactorizationMonoid.mem_normalizedFactors_iff J.2.1).mp hmem).2)
  rintro ⟨e, J⟩ ⟨e', J'⟩ h
  have h' : v.asIdeal ^ e * J.1 = v.asIdeal ^ e' * J'.1 := congrArg Subtype.val h
  have he : e = e' := by rw [← hcount e J, ← hcount e' J', h']
  subst he
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ v.ne_bot) h'))

lemma consFactored_surjective (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    Function.Surjective (consFactored v hv) := by
  rintro ⟨I, hI0, hIfac⟩
  have hfin : FiniteMultiplicity v.asIdeal I := .of_prime_left v.prime hI0
  obtain ⟨J, hJ, hvJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hI0 (by simpa using hJ)
  refine ⟨⟨multiplicity v.asIdeal I, J, hJ0, fun w hw => ?_⟩, Subtype.ext hJ.symm⟩
  have hwI : w.asIdeal ∣ I := hw.trans ((dvd_mul_left J _).trans (dvd_of_eq hJ.symm))
  rcases Finset.mem_cons.mp (hIfac w hwI) with rfl | hmem
  · exact absurd hw hvJ
  · exact hmem

noncomputable def consFactoredEquiv (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I} ≃
      {I : Ideal (𝓞 K) // IsFactoredBy (T.cons v hv) I} :=
  Equiv.ofBijective _ ⟨consFactored_injective v hv, consFactored_surjective v hv⟩

lemma factoredSum_empty (s : ℝ) :
    factoredSum K (∅ : Finset (HeightOneSpectrum (𝓞 K))) s = 1 := by
  have huniq : ∀ I : {I : Ideal (𝓞 K) // IsFactoredBy ∅ I},
      I = ⟨⊤, isFactoredBy_top ∅⟩ := fun I => Subtype.ext (eq_top_of_isFactoredBy_empty I.2)
  rw [factoredSum, tsum_eq_single (⟨⊤, isFactoredBy_top ∅⟩ : {I : Ideal (𝓞 K) // IsFactoredBy ∅ I})
    (fun b hb => absurd (huniq b) hb)]
  exact normRpow_top

lemma factoredSum_cons (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) (s : ℝ) :
    factoredSum K (T.cons v hv) s =
      (1 - normRpow K s v.asIdeal)⁻¹ * factoredSum K T s := by
  have h1 : factoredSum K (T.cons v hv) s =
      ∑' p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I},
        normRpow K s ((consFactoredEquiv v hv p).1) :=
    ((consFactoredEquiv v hv).tsum_eq fun I => normRpow K s I.1).symm
  have h2 : ∀ p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I},
      normRpow K s ((consFactoredEquiv v hv p).1) =
        normRpow K s v.asIdeal ^ p.1 * normRpow K s p.2.1 := by
    intro p
    show normRpow K s (v.asIdeal ^ p.1 * p.2.1) = _
    rw [normRpow_mul, normRpow_pow]
  calc factoredSum K (T.cons v hv) s
      = ∑' p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I},
          normRpow K s v.asIdeal ^ p.1 * normRpow K s p.2.1 := by rw [h1]; exact tsum_congr h2
    _ = ∑' (e : ℕ) (J : {I : Ideal (𝓞 K) // IsFactoredBy T I}),
          normRpow K s v.asIdeal ^ e * normRpow K s J.1 :=
        ENNReal.tsum_prod
          (f := fun e (J : {I : Ideal (𝓞 K) // IsFactoredBy T I}) =>
            normRpow K s v.asIdeal ^ e * normRpow K s J.1)
    _ = ∑' e : ℕ, normRpow K s v.asIdeal ^ e * factoredSum K T s := by
          simp_rw [ENNReal.tsum_mul_left]; rfl
    _ = (∑' e : ℕ, normRpow K s v.asIdeal ^ e) * factoredSum K T s := ENNReal.tsum_mul_right
    _ = (1 - normRpow K s v.asIdeal)⁻¹ * factoredSum K T s := by rw [ENNReal.tsum_geometric]

lemma factoredSum_eq_prod (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    factoredSum K T s = ∏ v ∈ T, (1 - normRpow K s v.asIdeal)⁻¹ := by
  induction T using Finset.cons_induction_on with
  | empty => simpa using factoredSum_empty s
  | cons v T hv ih => rw [factoredSum_cons v hv, ih, Finset.prod_cons]

lemma factoredSum_le_idealSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    factoredSum K T s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun I : {I : Ideal (𝓞 K) // IsFactoredBy T I} =>
        (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact h
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

lemma idealSum_eq_iSup_factoredSum (s : ℝ) :
    idealSum K s = ⨆ T : Finset (HeightOneSpectrum (𝓞 K)), factoredSum K T s := by
  classical
  refine le_antisymm ?_ (iSup_le fun T => factoredSum_le_idealSum T s)
  rw [idealSum, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  set T : Finset (HeightOneSpectrum (𝓞 K)) := F.biUnion fun I => primeFactors K I.1 with hT
  have hmem : ∀ I ∈ F, IsFactoredBy T I.1 := fun I hI =>
    (isFactoredBy_primeFactors I.2).mono (Finset.subset_biUnion_of_mem _ hI)
  have hinj : Function.Injective
      (fun I : F => (⟨I.1.1, hmem I.1 I.2⟩ : {I : Ideal (𝓞 K) // IsFactoredBy T I})) := by
    rintro ⟨⟨I, hI0⟩, hIF⟩ ⟨⟨J, hJ0⟩, hJF⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact h
  calc ∑ I ∈ F, normRpow K s I.1
      = ∑ I ∈ F.attach, normRpow K s I.1.1 := (Finset.sum_attach F _).symm
    _ = ∑' I : F, normRpow K s I.1.1 := by rw [tsum_fintype, Finset.univ_eq_attach]
    _ ≤ ∑' I : {I : Ideal (𝓞 K) // IsFactoredBy T I}, normRpow K s I.1 :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1
    _ = factoredSum K T s := rfl
    _ ≤ ⨆ T : Finset (HeightOneSpectrum (𝓞 K)), factoredSum K T s :=
        le_iSup (fun T => factoredSum K T s) T

end EulerProduct

section Comparisons

lemma primeSqSum_le_idealSum_two {s : ℝ} (hs : 1 ≤ s) : primeSqSum K s ≤ idealSum K 2 := by
  refine le_trans (ENNReal.tsum_le_tsum fun v => ?_) (primeSum_le_idealSum K 2)
  have h1 : normRpow K s v.asIdeal ^ (2 : ℕ) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-s * 2) := by
    rw [normRpow, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [h1, normRpow]
  refine ENNReal.rpow_le_rpow_of_exponent_le (one_le_cast_absNorm v.ne_bot) ?_
  nlinarith

lemma one_le_idealSum (s : ℝ) : 1 ≤ idealSum K s := by
  have h : normRpow K s (⊤ : Ideal (𝓞 K)) ≤ idealSum K s :=
    ENNReal.le_tsum (f := fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => normRpow K s I.1)
      (⟨⊤, by simp⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})
  rwa [normRpow_top] at h

lemma one_le_factoredSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    1 ≤ factoredSum K T s := by
  have h : normRpow K s (⊤ : Ideal (𝓞 K)) ≤ factoredSum K T s :=
    ENNReal.le_tsum
      (f := fun I : {I : Ideal (𝓞 K) // IsFactoredBy T I} => normRpow K s I.1)
      (⟨⊤, isFactoredBy_top T⟩ : {I : Ideal (𝓞 K) // IsFactoredBy T I})
  rwa [normRpow_top] at h

lemma factoredSum_toReal_pos {T : Finset (HeightOneSpectrum (𝓞 K))} {s : ℝ}
    (hfin : idealSum K s ≠ ∞) : 0 < (factoredSum K T s).toReal := by
  refine ENNReal.toReal_pos_iff.mpr ⟨lt_of_lt_of_le zero_lt_one (one_le_factoredSum T s), ?_⟩
  exact lt_top_iff_ne_top.mpr fun h => hfin (eq_top_iff.mpr (h ▸ factoredSum_le_idealSum T s))

lemma primeSum_ne_top {s : ℝ} (hfin : idealSum K s ≠ ∞) : primeSum K s ≠ ∞ :=
  fun h => hfin (eq_top_iff.mpr (h ▸ primeSum_le_idealSum K s))

lemma idealSum_toReal_pos {s : ℝ} (hfin : idealSum K s ≠ ∞) : 0 < (idealSum K s).toReal :=
  ENNReal.toReal_pos_iff.mpr
    ⟨lt_of_lt_of_le zero_lt_one (one_le_idealSum s), lt_top_iff_ne_top.mpr hfin⟩

lemma one_le_idealSum_toReal {s : ℝ} (hfin : idealSum K s ≠ ∞) : 1 ≤ (idealSum K s).toReal := by
  have := (ENNReal.toReal_le_toReal (by simp) hfin).mpr (one_le_idealSum (K := K) s)
  simpa using this

end Comparisons

section LogIneq

lemma le_neg_log_one_sub {x : ℝ} (hx1 : x < 1) : x ≤ -Real.log (1 - x) := by
  have h := Real.log_le_sub_one_of_pos (x := 1 - x) (by linarith)
  linarith

lemma neg_log_one_sub_le {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have h1 : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  have h2 : (1 + x + 2 * x ^ 2 : ℝ) ≤ Real.exp (x + 2 * x ^ 2) := by
    have := Real.add_one_le_exp (x + 2 * x ^ 2)
    linarith
  have h3 : Real.log (1 - x)⁻¹ ≤ x + 2 * x ^ 2 := by
    calc Real.log (1 - x)⁻¹ ≤ Real.log (Real.exp (x + 2 * x ^ 2)) :=
          Real.log_le_log (inv_pos.mpr (by linarith)) (h1.trans h2)
      _ = x + 2 * x ^ 2 := Real.log_exp _
  rwa [Real.log_inv] at h3

end LogIneq

section LogSandwich

variable {s : ℝ}

lemma normRpow_toReal_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ (normRpow K s v.asIdeal).toReal := ENNReal.toReal_nonneg

lemma normRpow_toReal_le_half (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    (normRpow K s v.asIdeal).toReal ≤ 1 / 2 := by
  have h1 : normRpow K s v.asIdeal ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-1 : ℝ) :=
    ENNReal.rpow_le_rpow_of_exponent_le (one_le_cast_absNorm v.ne_bot) (by linarith)
  have h2 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-1 : ℝ) ≤ (2 : ℝ≥0∞) ^ (-1 : ℝ) := by
    rw [ENNReal.rpow_neg_one, ENNReal.rpow_neg_one]
    exact ENNReal.inv_le_inv' (by exact_mod_cast two_le_absNorm v)
  have h3 : ((2 : ℝ≥0∞) ^ (-1 : ℝ)).toReal = 1 / 2 := by
    rw [ENNReal.rpow_neg_one]
    simp
  calc (normRpow K s v.asIdeal).toReal
      ≤ ((2 : ℝ≥0∞) ^ (-1 : ℝ)).toReal := by
        refine (ENNReal.toReal_le_toReal ?_ (by simp [ENNReal.rpow_neg_one])).mpr (h1.trans h2)
        exact normRpow_ne_top v.ne_bot (by linarith)
    _ = 1 / 2 := h3

lemma normRpow_toReal_lt_one (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    (normRpow K s v.asIdeal).toReal < 1 :=
  lt_of_le_of_lt (normRpow_toReal_le_half v hs) (by norm_num)

lemma toReal_eulerFactor (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    ((1 - normRpow K s v.asIdeal)⁻¹).toReal =
      (1 - (normRpow K s v.asIdeal).toReal)⁻¹ := by
  rw [ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le (normRpow_lt_one v (by linarith)).le (by simp), ENNReal.toReal_one]

lemma one_sub_normRpow_toReal_pos (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    (0 : ℝ) < 1 - (normRpow K s v.asIdeal).toReal := by
  linarith [normRpow_toReal_lt_one v hs]

lemma log_factoredSum_toReal (T : Finset (HeightOneSpectrum (𝓞 K))) (hs : 1 ≤ s) :
    Real.log ((factoredSum K T s).toReal) =
      ∑ v ∈ T, -Real.log (1 - (normRpow K s v.asIdeal).toReal) := by
  rw [factoredSum_eq_prod, ENNReal.toReal_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [toReal_eulerFactor v hs, Real.log_inv]
  · intro v _
    rw [toReal_eulerFactor v hs]
    exact (inv_pos.mpr (by linarith [normRpow_toReal_lt_one v hs])).ne'

lemma sum_normRpow_toReal_le (T : Finset (HeightOneSpectrum (𝓞 K))) (hs : 1 ≤ s)
    (hfin : primeSum K s ≠ ∞) :
    ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ≤ (primeSum K s).toReal := by
  have hne : ∀ v ∈ T, normRpow K s v.asIdeal ≠ ∞ := fun v _ =>
    normRpow_ne_top v.ne_bot (by linarith)
  rw [← ENNReal.toReal_sum hne]
  exact (ENNReal.toReal_le_toReal
    (ENNReal.sum_lt_top.mpr fun v hv => (hne v hv).lt_top).ne hfin).mpr (ENNReal.sum_le_tsum T)

lemma sum_normRpow_sq_toReal_le (T : Finset (HeightOneSpectrum (𝓞 K))) (hs : 1 ≤ s)
    (hfin2 : idealSum K 2 ≠ ∞) :
    ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ^ 2 ≤ (idealSum K 2).toReal := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal ^ (2:ℕ) ≠ ∞ := fun v =>
    ENNReal.pow_ne_top (normRpow_ne_top v.ne_bot (by linarith))
  have hsq : primeSqSum K s ≠ ∞ :=
    fun h => hfin2 (eq_top_iff.mpr (h ▸ primeSqSum_le_idealSum_two hs))
  calc ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ^ 2
      = ∑ v ∈ T, (normRpow K s v.asIdeal ^ (2:ℕ)).toReal := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [ENNReal.toReal_pow]
    _ = (∑ v ∈ T, normRpow K s v.asIdeal ^ (2:ℕ)).toReal :=
        (ENNReal.toReal_sum (fun v _ => hne v)).symm
    _ ≤ (primeSqSum K s).toReal :=
        (ENNReal.toReal_le_toReal
          (ENNReal.sum_lt_top.mpr fun v _ => (hne v).lt_top).ne hsq).mpr
          (ENNReal.sum_le_tsum T)
    _ ≤ (idealSum K 2).toReal :=
        (ENNReal.toReal_le_toReal hsq hfin2).mpr (primeSqSum_le_idealSum_two hs)

theorem primeSum_toReal_le_log_idealSum (hs : 1 ≤ s) (hfin : idealSum K s ≠ ∞) :
    (primeSum K s).toReal ≤ Real.log ((idealSum K s).toReal) := by

  rw [primeSum, ENNReal.tsum_toReal_eq
    (fun v => normRpow_ne_top v.ne_bot (by linarith))]
  refine Real.tsum_le_of_sum_le (fun v => ENNReal.toReal_nonneg) fun T => ?_
  calc ∑ v ∈ T, (normRpow K s v.asIdeal).toReal
      ≤ ∑ v ∈ T, -Real.log (1 - (normRpow K s v.asIdeal).toReal) :=
        Finset.sum_le_sum fun v _ => le_neg_log_one_sub (normRpow_toReal_lt_one v hs)
    _ = Real.log ((factoredSum K T s).toReal) := (log_factoredSum_toReal T hs).symm
    _ ≤ Real.log ((idealSum K s).toReal) := by
        refine Real.log_le_log (factoredSum_toReal_pos hfin)
          ((ENNReal.toReal_le_toReal ?_ hfin).mpr (factoredSum_le_idealSum T s))
        exact fun h => hfin (eq_top_iff.mpr (h ▸ factoredSum_le_idealSum T s))

theorem log_idealSum_le_primeSum_toReal (hs : 1 ≤ s) (hfin : idealSum K s ≠ ∞)
    (hfin2 : idealSum K 2 ≠ ∞) :
    Real.log ((idealSum K s).toReal) ≤
      (primeSum K s).toReal + 2 * (idealSum K 2).toReal := by
  set C : ℝ := (primeSum K s).toReal + 2 * (idealSum K 2).toReal with hC

  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Real.log ((factoredSum K T s).toReal) ≤ C := by
    intro T
    calc Real.log ((factoredSum K T s).toReal)
        = ∑ v ∈ T, -Real.log (1 - (normRpow K s v.asIdeal).toReal) := log_factoredSum_toReal T hs
      _ ≤ ∑ v ∈ T, ((normRpow K s v.asIdeal).toReal + 2 * (normRpow K s v.asIdeal).toReal ^ 2) :=
          Finset.sum_le_sum fun v _ => neg_log_one_sub_le (normRpow_toReal_nonneg v)
            (normRpow_toReal_le_half v hs)
      _ = (∑ v ∈ T, (normRpow K s v.asIdeal).toReal) +
            2 * ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ C := by
          rw [hC]
          have h1 := sum_normRpow_toReal_le T hs (primeSum_ne_top hfin)
          have h2 := sum_normRpow_sq_toReal_le T hs hfin2
          linarith

  have hCnonneg : 0 ≤ C := by
    have : (0:ℝ) ≤ (primeSum K s).toReal := ENNReal.toReal_nonneg
    have : (0:ℝ) ≤ (idealSum K 2).toReal := ENNReal.toReal_nonneg
    linarith
  rw [Real.log_le_iff_le_exp (idealSum_toReal_pos hfin)]
  rw [← ENNReal.toReal_ofReal (Real.exp_nonneg C)]
  refine (ENNReal.toReal_le_toReal hfin (by simp)).mpr ?_
  rw [idealSum_eq_iSup_factoredSum]
  refine iSup_le fun T => ?_
  have hTfin : factoredSum K T s ≠ ∞ :=
    fun h => hfin (eq_top_iff.mpr (h ▸ factoredSum_le_idealSum T s))
  rw [← ENNReal.ofReal_toReal hTfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_log (x := (factoredSum K T s).toReal) (factoredSum_toReal_pos hfin)]
  exact Real.exp_le_exp.mpr (key T)

end LogSandwich

variable (K)

private lemma log_idealSum_add_log_isBigO :
    (fun s : ℝ => Real.log ((idealSum K s).toReal) + Real.log (s - 1)) =O[𝓝[>] 1]
      (fun _ => (1:ℝ)) := by
  have h1 : Tendsto (fun s : ℝ => Real.log ((s - 1) * (idealSum K s).toReal)) (𝓝[>] 1)
      (𝓝 (Real.log (dedekindZeta_residue K))) :=
    (tendsto_sub_one_mul_idealSum K).log (dedekindZeta_residue_ne_zero K)
  refine (h1.isBigO_one ℝ).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [Real.log_mul (by linarith) (idealSum_toReal_pos (idealSum_ne_top K hs)).ne']
  ring

private lemma primeSum_sub_log_idealSum_isBigO :
    (fun s : ℝ => (primeSum K s).toReal - Real.log ((idealSum K s).toReal)) =O[𝓝[>] 1]
      (fun _ => (1:ℝ)) := by
  rw [isBigO_one_iff]
  refine isBoundedUnder_of_eventually_le (a := 2 * (idealSum K 2).toReal) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  have hfin := idealSum_ne_top K hs
  have hfin2 := idealSum_ne_top K (by norm_num : (1:ℝ) < 2)
  have hub := primeSum_toReal_le_log_idealSum hs.le hfin
  have hlb := log_idealSum_le_primeSum_toReal hs.le hfin hfin2
  have hC2 : (0:ℝ) ≤ 2 * (idealSum K 2).toReal := by positivity
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end FrobeniusDensity


public theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO (K : Type*)
    [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by
  have h := (primeSum_sub_log_idealSum_isBigO K).add (log_idealSum_add_log_isBigO K)
  refine h.congr' (Eventually.of_forall fun s => by ring) EventuallyEq.rfl


open scoped ENNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

private lemma cutSum_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) : cutSum K S₀ s ≠ ⊤ := by
  have h1 : cutSum K S₀ s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K S₀ s]
    exact le_add_self.trans (self_le_add_right _ _)
  exact (h1.trans_lt (primeSum_ne_top (idealSum_ne_top K hs)).lt_top).ne

private lemma tailSum_ne_top {s : ℝ} (hs : 1 < s) : tailSum K s ≠ ⊤ := by
  have h1 : tailSum K s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K ∅ s]
    exact le_add_self
  exact (h1.trans_lt (primeSum_ne_top (idealSum_ne_top K hs)).lt_top).ne

private theorem tailConst_ne_top : tailConst ≠ ⊤ := by
  have hsummable : Summable (fun ℓ : ℕ => if ℓ.Prime then (((ℓ : ℝ) ^ 2)⁻¹) else 0) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
      (Real.summable_nat_pow_inv.mpr one_lt_two)
    · split <;> positivity
    · split
      · exact le_rfl
      · positivity
  have hpt : ∀ ℓ : ℕ, (if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0)
      = ENNReal.ofReal (if ℓ.Prime then (((ℓ : ℝ) ^ 2)⁻¹) else 0) := by
    intro ℓ
    by_cases hℓ : ℓ.Prime
    · have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.pos
      rw [if_pos hℓ, if_pos hℓ, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow hℓ0.le, ENNReal.ofReal_natCast]
    · rw [if_neg hℓ, if_neg hℓ, ENNReal.ofReal_zero]
  rw [tailConst, tsum_congr hpt,
    ← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => by split <;> positivity) hsummable]
  exact ENNReal.ofReal_ne_top

private theorem absNorm_eq_pow_inertiaDeg_ratBelow (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm v.asIdeal
      = ratBelow v ^ ((ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal) :=
  Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal (ratBelow_prime v)

private theorem sq_ratBelow_le_absNorm (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ratBelow v ^ 2 ≤ Ideal.absNorm v.asIdeal := by
  have : Fact (ratBelow v).Prime := ⟨ratBelow_prime v⟩
  have h1 : 0 < (ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal :=
    Ideal.inertiaDeg'_pos (ratPrimeIdeal (ratBelow v)) v.asIdeal
  have h2 : (ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal ≠ 1 := by
    intro h
    rw [absNorm_eq_pow_inertiaDeg_ratBelow K v, h, pow_one] at hv
    exact hv (ratBelow_prime v)
  calc ratBelow v ^ 2
      ≤ ratBelow v ^ ((ratPrimeIdeal (ratBelow v)).inertiaDeg' v.asIdeal) :=
        Nat.pow_le_pow_right (ratBelow_prime v).pos (by omega)
    _ = Ideal.absNorm v.asIdeal := (absNorm_eq_pow_inertiaDeg_ratBelow K v).symm

private def RatBelowFiber (ℓ : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // ratBelow v = ℓ}

private theorem liesOver_of_ratBelow_eq {v : HeightOneSpectrum (𝓞 K)} {ℓ : ℕ}
    (h : ratBelow v = ℓ) : v.asIdeal.LiesOver (ratPrimeIdeal ℓ) :=
  h ▸ liesOver_ratBelow v

private noncomputable def ratBelowFiberEquiv :
    (Σ ℓ : ℕ, RatBelowFiber K ℓ) ≃ HeightOneSpectrum (𝓞 K) where
  toFun p := p.2.1
  invFun v := ⟨ratBelow v, v, rfl⟩
  left_inv p := by rcases p with ⟨ℓ, v, rfl⟩; rfl
  right_inv v := rfl

private theorem isEmpty_ratBelowFiber {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) :
    IsEmpty (RatBelowFiber K ℓ) :=
  ⟨fun v => hℓ (v.2 ▸ ratBelow_prime v.1)⟩

private scoped instance (ℓ : ℕ) : Finite (RatBelowFiber K ℓ) := by
  by_cases hℓ : ℓ.Prime
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    have hinj : Function.Injective (fun (v : RatBelowFiber K ℓ) =>
        (⟨v.1.asIdeal, v.1.isPrime, liesOver_of_ratBelow_eq K v.2⟩ :
          ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))))) :=
      fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    have hfin : Finite ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))) := by
      rw [← IsDedekindDomain.coe_primesOverFinset (ratPrimeIdeal_ne_bot hℓ) (𝓞 K)]
      exact (IsDedekindDomain.primesOverFinset (ratPrimeIdeal ℓ) (𝓞 K)).finite_toSet.to_subtype
    exact Finite.of_injective _ hinj
  · have := isEmpty_ratBelowFiber K hℓ
    infer_instance

private theorem natCard_ratBelowFiber_le {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Nat.card (RatBelowFiber K ℓ) ≤ Module.finrank ℚ K := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hinj : Function.Injective (fun (v : RatBelowFiber K ℓ) =>
      (⟨v.1.asIdeal, v.1.isPrime, liesOver_of_ratBelow_eq K v.2⟩ :
        ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))))) :=
    fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine le_trans (Nat.card_le_card_of_injective _ hinj) ?_
  rw [Nat.card_coe_set_eq, ← IsDedekindDomain.coe_primesOverFinset
    (ratPrimeIdeal_ne_bot hℓ) (𝓞 K), Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (S := 𝓞 K) (K := ℚ) (L := K)
    (p := ratPrimeIdeal ℓ) (ratPrimeIdeal_ne_bot hℓ)

private theorem tailSum_le {s : ℝ} (hs : 1 ≤ s) :
    tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * tailConst := by
  have hpt : ∀ v : HeightOneSpectrum (𝓞 K),
      (if (Ideal.absNorm v.asIdeal).Prime then 0 else normRpow K s v.asIdeal)
        ≤ ((ratBelow v : ℝ≥0∞) ^ 2)⁻¹ := by
    intro v
    by_cases hv : (Ideal.absNorm v.asIdeal).Prime
    · rw [if_pos hv]; exact zero_le
    · rw [if_neg hv]
      calc normRpow K s v.asIdeal
          ≤ normRpow K 1 v.asIdeal :=
            ENNReal.rpow_le_rpow_of_exponent_le (one_le_cast_absNorm v.ne_bot)
              (neg_le_neg hs)
        _ = ((Ideal.absNorm v.asIdeal : ℝ≥0∞))⁻¹ := ENNReal.rpow_neg_one _
        _ ≤ ((ratBelow v : ℝ≥0∞) ^ 2)⁻¹ := by
            refine ENNReal.inv_le_inv' ?_
            calc ((ratBelow v : ℝ≥0∞) ^ 2)
                = ((ratBelow v ^ 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
              _ ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) :=
                  Nat.cast_le.mpr (sq_ratBelow_le_absNorm K v hv)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [← (ratBelowFiberEquiv K).tsum_eq (fun v => ((ratBelow v : ℝ≥0∞) ^ 2)⁻¹),
    ENNReal.tsum_sigma']
  have hfib : ∀ ℓ : ℕ, ∀ v : RatBelowFiber K ℓ,
      ((ratBelow (ratBelowFiberEquiv K ⟨ℓ, v⟩) : ℝ≥0∞) ^ 2)⁻¹ = ((ℓ : ℝ≥0∞) ^ 2)⁻¹ := by
    intro ℓ v
    have : ratBelow (ratBelowFiberEquiv K ⟨ℓ, v⟩) = ℓ := v.2
    rw [this]
  calc ∑' (ℓ : ℕ) (v : RatBelowFiber K ℓ),
        ((ratBelow (ratBelowFiberEquiv K ⟨ℓ, v⟩) : ℝ≥0∞) ^ 2)⁻¹
      = ∑' ℓ : ℕ, (Nat.card (RatBelowFiber K ℓ) : ℝ≥0∞) * ((ℓ : ℝ≥0∞) ^ 2)⁻¹ := by
        refine tsum_congr fun ℓ => ?_
        rw [tsum_congr (hfib ℓ), ENNReal.tsum_const, ENat.card_eq_coe_natCard]
        norm_cast
    _ ≤ ∑' ℓ : ℕ, (Module.finrank ℚ K : ℝ≥0∞) *
          (if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0) := by
        refine ENNReal.tsum_le_tsum fun ℓ => ?_
        by_cases hℓ : ℓ.Prime
        · rw [if_pos hℓ]
          gcongr
          exact Nat.cast_le.mpr (natCard_ratBelowFiber_le K hℓ)
        · have : Nat.card (RatBelowFiber K ℓ) = 0 :=
            @Nat.card_of_isEmpty _ (isEmpty_ratBelowFiber K hℓ)
          rw [if_neg hℓ, mul_zero, this, Nat.cast_zero, zero_mul]
    _ = (Module.finrank ℚ K : ℝ≥0∞) * tailConst := by
        rw [tailConst, ENNReal.tsum_mul_left]

omit [NumberField K] in
private theorem cutSum_le (S₀ : Finset ℕ) {s : ℝ} (hs : 0 < s) :
    cutSum K S₀ s ≤ ∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞) := by
  have hterm : ∀ ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)
      ≤ (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) := by
    intro ℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · rw [degOneCount_of_not_prime K Nat.not_prime_zero]
      simp
    · calc (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)
          ≤ (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * 1 := by
            gcongr
            exact ENNReal.rpow_le_one_of_one_le_of_neg (by exact_mod_cast hℓ)
              (neg_neg_iff_pos.mpr hs)
        _ = _ := mul_one _
  calc cutSum K S₀ s
      ≤ ∑' ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑ ℓ ∈ S₀, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) :=
        tsum_eq_sum fun _ hℓ => if_neg hℓ
    _ = ∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞) :=
        Finset.sum_congr rfl fun _ hℓ => if_pos hℓ

omit [NumberField K] in
private theorem sum_degOneCount_ne_top (S₀ : Finset ℕ) :
    (∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞)) ≠ ⊤ :=
  (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.natCast_lt_top _).ne

omit [NumberField K] in
private theorem term_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 0 < s) (ℓ : ℕ) :
    (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [degOneCount_of_not_prime K Nat.not_prime_zero]
    simp
  · refine ENNReal.mul_ne_top (by split <;> simp) ?_
    exact ((ENNReal.rpow_le_one_of_one_le_of_neg (by exact_mod_cast hℓ)
      (neg_neg_iff_pos.mpr hs)).trans_lt ENNReal.one_lt_top).ne

omit [NumberField K] in
private theorem degOneSum_toReal_eq (S₀ : Finset ℕ) {s : ℝ} (hs : 0 < s) :
    (degOneSum K S₀ s).toReal
      = ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [degOneSum, ENNReal.tsum_toReal_eq (term_ne_top K S₀ hs)]
  exact tsum_congr (toReal_term K S₀ s)

private theorem tailSum_toReal_isBigO :
    (fun s : ℝ => (tailSum K s).toReal) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  rw [isBigO_one_iff]
  refine isBoundedUnder_of_eventually_le
    (a := ((Module.finrank ℚ K : ℝ≥0∞) * tailConst).toReal) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) tailConst_ne_top) (tailSum_le K hs.le)

omit [NumberField K] in
private theorem cutSum_toReal_isBigO (S₀ : Finset ℕ) :
    (fun s : ℝ => (cutSum K S₀ s).toReal) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  rw [isBigO_one_iff]
  refine isBoundedUnder_of_eventually_le
    (a := (∑ ℓ ∈ S₀, (degOneCount K ℓ : ℝ≥0∞)).toReal) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (sum_degOneCount_ne_top K S₀)
    (cutSum_le K S₀ (lt_trans zero_lt_one hs))

end FrobeniusDensity


theorem FrobeniusDensity.degOneSum_add_log_isBigO (K : Type*) [Field K] [NumberField K]
    (S₀ : Finset ℕ) :
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)) =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) := by
  have h1 := primeSum_toReal_add_log_isBigO K
  have h2 := cutSum_toReal_isBigO K S₀
  have h3 := tailSum_toReal_isBigO K
  refine ((h1.sub h2).sub h3).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  have hdecomp := congrArg ENNReal.toReal (primeSum_eq_degOneSum_add K S₀ s)
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨degOneSum_ne_top K S₀ hs, cutSum_ne_top K S₀ hs⟩)
      (tailSum_ne_top K hs),
    ENNReal.toReal_add (degOneSum_ne_top K S₀ hs) (cutSum_ne_top K S₀ hs)] at hdecomp
  show (primeSum K s).toReal + Real.log (s - 1) - (cutSum K S₀ s).toReal
      - (tailSum K s).toReal
    = (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)
  rw [← degOneSum_toReal_eq K S₀ (lt_trans zero_lt_one hs), hdecomp]
  ring


open NumberField

public theorem FrobeniusDensity.degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := fun H S₀ =>
  ⟨fun _ hs => FrobeniusDensity.summable_degOne_term
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀ hs,
    FrobeniusDensity.degOneSum_add_log_isBigO
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀⟩


open scoped Classical

namespace FrobeniusDensity

variable {G : Type*} [Group G]

theorem coprime_mod_iff {k n : ℕ} : (k % n).Coprime n ↔ k.Coprime n := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

theorem card_filter_conj_eq [Fintype G] (a b : G) (h : IsConj a b) :
    (Finset.univ.filter (fun g : G => g * a * g⁻¹ = b)).card
      = Fintype.card (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have key : ∀ g : G, g * a * g⁻¹ = b ↔ c⁻¹ * g ∈ Subgroup.centralizer ({a} : Set G) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have h1 : g * a * g⁻¹ = c * a * c⁻¹ := by rw [hg, hc]
      have h2 : c⁻¹ * (g * a * g⁻¹) * c = a := by
        rw [h1]; group
      calc c⁻¹ * g * a = c⁻¹ * (g * a * g⁻¹) * c * (c⁻¹ * g) := by group
        _ = a * (c⁻¹ * g) := by rw [h2]
    · intro hg
      have h3 : g * a * g⁻¹ = c * (c⁻¹ * g * a) * g⁻¹ := by group
      rw [h3, hg, ← hc]; group
  rw [← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft c⁻¹) (fun g => ?_))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft]
  exact key g

theorem card_filter_conj_eq_zero [Fintype G] (a b : G) (h : ¬ IsConj a b) :
    (Finset.univ.filter (fun g : G => g * a * g⁻¹ = b)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  exact h (isConj_iff.mpr ⟨g, hg⟩)

theorem centralizer_pow_eq_of_coprime (σ : G) {k : ℕ} (hk : k.Coprime (orderOf σ)) :
    Subgroup.centralizer ({σ ^ k} : Set G) = Subgroup.centralizer ({σ} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk
    rw [← hm]
    exact (Commute.pow_right (show Commute g (σ ^ k) from h) m)
  · intro h
    exact (Commute.pow_right (show Commute g σ from h) k)

theorem ncard_conj_gen_eq_of_rational [Finite G] (σ τ : G)
    (hrat : ∀ k : ℕ, k.Coprime (orderOf σ) → IsConj σ (σ ^ k)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = if IsConj σ τ then (orderOf σ).totient * Nat.card (Subgroup.centralizer ({σ} : Set G))
        else 0 := by
  haveI := Fintype.ofFinite G
  set n := orderOf σ with hn
  have hn0 : 0 < n := orderOf_pos σ
  set K : Finset ℕ := (Finset.range n).filter (fun k => n.Coprime k) with hK
  have hKcard : K.card = n.totient := (Nat.totient_eq_card_coprime n).symm
  set S : Set G := {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ} with hS
  set T : ℕ → Finset G := fun k => Finset.univ.filter (fun g : G => g * σ ^ k * g⁻¹ = τ) with hT
  have hST : S.toFinset = K.biUnion T := by
    ext g
    simp only [Set.mem_toFinset, hS, Set.mem_setOf_eq, Finset.mem_biUnion, hK, hT,
      Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, hgk⟩
      refine ⟨k % n, ⟨Nat.mod_lt _ hn0, ?_⟩, ?_⟩
      · exact Nat.coprime_comm.mp (coprime_mod_iff.mpr hk)
      · rwa [pow_mod_orderOf]
    · rintro ⟨k, ⟨-, hk⟩, hgk⟩
      exact ⟨k, Nat.coprime_comm.mp hk, hgk⟩
  have hdisj : (K : Set ℕ).PairwiseDisjoint T := by
    intro k hk k' hk' hne
    simp only [Finset.coe_filter, hK, Set.mem_setOf_eq, Finset.mem_range] at hk hk'
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
    apply hne
    have hpow : σ ^ k = σ ^ k' := by
      have := hg.trans hg'.symm
      simpa using this
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hk.1) (Set.mem_Iio.mpr hk'.1) hpow
  rw [Set.ncard_eq_toFinset_card' S, hST, Finset.card_biUnion hdisj]
  by_cases hc : IsConj σ τ
  · rw [if_pos hc]
    have hterm : ∀ k ∈ K, (T k).card = Nat.card (Subgroup.centralizer ({σ} : Set G)) := by
      intro k hk
      simp only [hK, Finset.mem_filter, Finset.mem_range] at hk
      have hk' : k.Coprime (orderOf σ) := Nat.coprime_comm.mp hk.2
      have hconj : IsConj (σ ^ k) τ := (hrat k hk').symm.trans hc
      rw [hT, card_filter_conj_eq _ _ hconj, centralizer_pow_eq_of_coprime σ hk',
        Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hKcard]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [hK, Finset.mem_filter, Finset.mem_range] at hk
    have hk' : k.Coprime (orderOf σ) := Nat.coprime_comm.mp hk.2
    have hnc : ¬ IsConj (σ ^ k) τ := fun h => hc ((hrat k hk').trans h)
    exact card_filter_conj_eq_zero _ _ hnc

theorem setOf_isConj_eq_orbit_conjAct (σ : G) :
    {τ : G | IsConj σ τ} = MulAction.orbit (ConjAct G) σ := by
  ext τ
  rw [ConjAct.orbit_eq_carrier_conjClasses, Set.mem_setOf_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

theorem card_stabilizer_conjAct_eq_card_centralizer (σ : G) :
    Nat.card (MulAction.stabilizer (ConjAct G) σ) =
      Nat.card (Subgroup.centralizer ({σ} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun g => ?_)
  show g ∈ MulAction.stabilizer (ConjAct G) σ ↔
    ConjAct.ofConjAct g ∈ Subgroup.centralizer ({σ} : Set G)
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff, ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]
  exact Iff.rfl

public theorem card_setOf_isConj_mul_card_centralizer (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G := by
  rw [setOf_isConj_eq_orbit_conjAct, ← card_stabilizer_conjAct_eq_card_centralizer,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) σ),
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rfl

theorem sum_moebius_mul_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ f ∈ n.divisors, (ArithmeticFunction.moebius (n / f)) * (f : ℤ) = (Nat.totient n : ℤ) := by
  have key : ∀ m > 0, ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.fst : ℤ) * (x.snd : ℤ) = (Nat.totient m : ℤ) := by
    refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun k => (Nat.totient k : ℤ)) (g := fun k => (k : ℤ))).mp ?_
    intro m _
    exact_mod_cast Nat.sum_totient m
  rw [← key n hn]
  exact (Nat.sum_divisorsAntidiagonal'
    (fun a b => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))).symm

end FrobeniusDensity

end
