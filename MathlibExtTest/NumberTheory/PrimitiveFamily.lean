/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The rank-excess consumer proof is adapted from
`P2M/Sol/S_flt_regular.lean:2011-2025`, anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
The frozen NOTICE and ATTRIBUTION.md §3 credit the flt-regular project,
Copyright (c) the flt-regular authors, also Apache License, Version 2.0:
Alex J. Best, Christopher Birkbeck, Riccardo Brasca, Eric Rodriguez Boidi,
Ruben Van de Velde, Andrew Yang.
The finite normalization type is reproduced from lines 1988-2009;
its proof and all other examples below are independently authored.
-/

import MathlibExt.NumberTheory.PrimitiveFamily
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.FiniteType
import Mathlib.Data.ZMod.Basic

/-! Source fidelity, applications, and separating normalization boundaries. -/

open Finset Module Polynomial

namespace PrimitiveFamilyTest

/-- The exact finite source interface, with no ambient number-field data. -/
theorem sourceFinite {ι : Type*} [Finite ι]
    (f : ι → ℤ) (hf : f ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ (n : ℕ) (f' : ι → ℤ), (f = p ^ n • f') ∧
      ∃ i, ¬ (p : ℤ) ∣ f' i :=
  Int.exists_pow_smul_eq_and_not_dvd f hf p hp

/-- The source rank-excess consumer, including its p-primary torsion input. -/
theorem rankExcessRelation (p : ℕ) (hp : p.Prime)
    {M : Type*} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r : ℕ) (hr : finrank ℤ (Additive M) < r)
    (η : Fin r → Additive M) :
    ∃ (a : ℤ) (c : Fin r → ℤ) (i : Fin r),
      ∑ j, c j • η j = a • Additive.ofMul ν ∧ ¬ (p : ℤ) ∣ c i := by
  obtain ⟨f, hrel, hnonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt (LinearIndependent.fintype_card_le_finrank (R := ℤ) (b := η))
      ((hr.trans_eq (Fintype.card_fin r).symm).not_ge))
  obtain ⟨n, g, hfg, i, hi⟩ := sourceFinite f
    (Function.ne_iff.mpr hnonzero) p hp.ne_one
  simp_rw [hfg, Pi.smul_apply, smul_assoc, ← smul_sum] at hrel
  obtain ⟨a, ha⟩ := hk _ _ hrel
  rw [← zpow_natCast] at ha
  exact ⟨a, g, i, ha.symm, hi⟩

/-- Removing a common nonzero scalar preserves an integer kernel relation. -/
theorem normalizeKernel {ι : Type*} [Fintype ι]
    (f η : ι → ℤ) (hf : f ≠ 0) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : p ≠ 1) (hrel : ∑ i, f i * η i = 0) :
    ∃ (n : ℕ) (g : ι → ℤ), f = p ^ n • g ∧
      (∑ i, g i * η i = 0) ∧ ∃ i, (g i : ZMod p) ≠ 0 := by
  obtain ⟨n, g, hfg, i, hi⟩ :=
    Int.exists_pow_smul_eq_and_not_dvd f hf p hp1
  have hpoint (j : ι) : f j = (p : ℤ) ^ n * g j := by
    simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] using
      congrFun hfg j
  have hscaled : (p : ℤ) ^ n * (∑ j, g j * η j) = 0 := by
    simpa only [hpoint, mul_assoc, ← mul_sum] using hrel
  refine ⟨n, g, hfg, ?_, i, ?_⟩
  · exact (mul_eq_zero.mp hscaled).resolve_left
      (pow_ne_zero n (Int.natCast_ne_zero.mpr hp0))
  · exact fun h => hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

/-- An infinite-index coefficient use, reconstructing a genuine polynomial. -/
theorem normalizePolynomial (P : ℤ[X]) (hP : P ≠ 0)
    (p : ℕ) (hp : p ≠ 1) :
    ∃ (n : ℕ) (Q : ℤ[X]), P = p ^ n • Q ∧
      Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  classical
  have hcoeff : (P.coeff : ℕ → ℤ) ≠ 0 := by
    intro h
    exact hP (Polynomial.ext (fun j => congrFun h j))
  obtain ⟨n, g, hg, i, hi⟩ :=
    Int.exists_pow_smul_eq_and_not_dvd P.coeff hcoeff p hp
  have hpow : p ^ n ≠ 0 := by
    intro h
    exact hcoeff (by simpa only [h, zero_smul] using hg)
  have hs : Function.support g ⊆ (P.support : Set ℕ) := by
    intro j hj
    apply Polynomial.mem_support_iff.mpr
    rw [show P.coeff j = (p ^ n : ℕ) • g j from congrFun hg j]
    exact smul_ne_zero hpow hj
  let Q : ℤ[X] := .ofFinsupp
    (.ofCoeff (.ofSupportFinite g (P.support.finite_toSet.subset hs)))
  have hQ (j : ℕ) : Q.coeff j = g j := rfl
  refine ⟨n, Q, Polynomial.ext (fun j => ?_), ?_⟩
  · simpa only [coeff_smul, hQ, Pi.smul_apply] using congrFun hg j
  · intro hzero
    apply hi
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [coeff_map, hQ, Int.coe_castRingHom, coeff_zero] using
      congrArg (fun R : (ZMod p)[X] => R.coeff i) hzero

/-- The composite-modulus kernel fixture calls the normalization API. -/
theorem compositeKernel :
    ∃ (n : ℕ) (g : Fin 3 → ℤ), ![0, 72, -108] = 6 ^ n • g ∧
      (∑ i, g i * (![0, 3, 2] : Fin 3 → ℤ) i = 0) ∧
      ∃ i, (g i : ZMod 6) ≠ 0 := by
  refine normalizeKernel ![0, 72, -108] ![0, 3, 2] ?_ 6
    (by decide) (by decide) ?_
  · intro h
    have := congrFun h 1
    norm_num at this
  · norm_num [Fin.sum_univ_succ]

/-- The concrete residual is nonzero modulo six, but has no coprime entry. -/
theorem compositeWitness :
    (![0, 72, -108] : Fin 3 → ℤ) =
        (6 ^ 2 : ℕ) • ![0, 2, -3] ∧
      (∑ i, (![0, 2, -3] : Fin 3 → ℤ) i *
        (![0, 3, 2] : Fin 3 → ℤ) i = 0) ∧
      (∃ i, ¬ (6 : ℤ) ∣ (![0, 2, -3] : Fin 3 → ℤ) i) ∧
      ∀ i, ¬ Nat.Coprime 6 ((![0, 2, -3] : Fin 3 → ℤ) i).natAbs := by
  refine ⟨?_, ?_, ⟨1, by norm_num⟩, ?_⟩
  · norm_num [funext_iff, Fin.forall_fin_succ, Pi.smul_apply]
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.forall_fin_succ, Nat.Coprime]

/-- Normalize the actual linear polynomial by its coefficient function. -/
theorem compositePolynomial :
    ∃ (n : ℕ) (Q : ℤ[X]), C (72 : ℤ) - C 108 * X = 6 ^ n • Q ∧
      Q.map (Int.castRingHom (ZMod 6)) ≠ 0 := by
  refine normalizePolynomial (C (72 : ℤ) - C 108 * X) ?_ 6 (by decide)
  intro h
  have := congrArg (fun P : ℤ[X] => P.coeff 0) h
  norm_num at this

/-- Explicit polynomial witnesses distinguish nonzero from unit reduction. -/
theorem compositePolynomialWitness :
    C (72 : ℤ) - C 108 * X =
        (6 ^ 2 : ℕ) • (C (2 : ℤ) - C 3 * X) ∧
      (C (2 : ZMod 6) - C 3 * X) ≠ 0 ∧
      ¬ IsUnit (2 : ZMod 6) ∧ ¬ IsUnit (-3 : ZMod 6) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [nsmul_eq_mul, mul_sub, ← mul_assoc]
  · intro h
    have := congrArg (fun P : (ZMod 6)[X] => P.coeff 0) h
    norm_num at this
    exact (by decide : (2 : ZMod 6) ≠ 0) this
  · exact fun h => (by decide : ¬ Nat.Coprime 2 6)
      ((ZMod.isUnit_iff_coprime 2 6).mp h)
  · rw [show (-3 : ZMod 6) = 3 by decide]
    exact fun h => (by decide : ¬ Nat.Coprime 3 6)
      ((ZMod.isUnit_iff_coprime 3 6).mp h)

/-- At base zero the API must return exponent zero for every nonzero family. -/
theorem zeroBase {ι : Type*} (f : ι → ℤ) (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : ι → ℤ), n = 0 ∧ f = (0 : ℕ) ^ n • g ∧
      ∃ i, ¬ (0 : ℤ) ∣ g i := by
  obtain ⟨n, g, hfg, hi⟩ :=
    Int.exists_pow_smul_eq_and_not_dvd f hf 0 (by decide)
  refine ⟨n, g, ?_, hfg, hi⟩
  by_contra hn
  exact hf (by simpa only [zero_pow hn, zero_smul] using hfg)

/-- Base one admits no residual coordinate, even for nonzero input. -/
theorem unitBaseImpossible {ι : Type*} (f : ι → ℤ) :
    ¬ ∃ (n : ℕ) (g : ι → ℤ), f = (1 : ℕ) ^ n • g ∧
      ∃ i, ¬ (1 : ℤ) ∣ g i := by
  rintro ⟨n, g, hfg, i, hi⟩
  exact hi (one_dvd _)

/-- An empty index type cannot satisfy the source's nonzero premise. -/
theorem emptyIndexImpossible : ¬ ∃ f : PEmpty → ℤ, f ≠ 0 := by
  rintro ⟨f, hf⟩
  exact hf (funext fun i => i.elim)

/-- Dropping the nonzero premise fails already at base two. -/
theorem zeroFamilyTwoImpossible {ι : Type*} :
    ¬ ∃ (n : ℕ) (g : ι → ℤ), 0 = (2 : ℕ) ^ n • g ∧
      ∃ i, ¬ (2 : ℤ) ∣ g i := by
  rintro ⟨n, g, hfg, i, hi⟩
  have hmul : (2 : ℤ) ^ n * g i = 0 := by
    simpa only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat] using (congrFun hfg i).symm
  have hgi : g i = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n (by decide))
  exact hi (hgi ▸ dvd_zero 2)

/-- The zero-family obstruction at two does not extend to base zero. -/
theorem zeroFamilyZeroPossible :
    ∃ (n : ℕ) (g : Unit → ℤ), 0 = (0 : ℕ) ^ n • g ∧
      ∃ i, ¬ (0 : ℤ) ∣ g i := by
  exact ⟨1, fun _ => 1, by simp, (), by norm_num⟩

/-- The admitted prime and zero-base fixtures have the stated witnesses. -/
theorem primeAndZeroFixtures :
    ((![0, 125, -250] : Fin 3 → ℤ) =
        (5 ^ 3 : ℕ) • ![0, 1, -2] ∧
      ¬ (5 : ℤ) ∣ (![0, 1, -2] : Fin 3 → ℤ) 1) ∧
    ((![0, 6, -10] : Fin 3 → ℤ) =
        (0 ^ 0 : ℕ) • ![0, 6, -10] ∧
      ¬ (0 : ℤ) ∣ (![0, 6, -10] : Fin 3 → ℤ) 1) := by
  norm_num [funext_iff, Fin.forall_fin_succ, Pi.smul_apply]

/-- The API also handles families with infinite support. -/
theorem infiniteFamily :
    ∃ (n : ℕ) (g : ℕ → ℤ), (fun i : ℕ => 6 * ((i : ℤ) + 1)) =
      (6 : ℕ) ^ n • g ∧ ∃ i, ¬ (6 : ℤ) ∣ g i := by
  refine Int.exists_pow_smul_eq_and_not_dvd _ ?_ 6 (by decide)
  intro h
  have := congrFun h 0
  norm_num at this

/-- A nontrivial finite torsion group satisfies the rank consumer's premises. -/
theorem rankTorsionFixture :
    ∃ (a : ℤ) (c : Fin 1 → ℤ) (i : Fin 1),
      (∑ j, c j • (![Additive.ofMul
        (Multiplicative.ofAdd (1 : ZMod 2))] :
        Fin 1 → Additive (Multiplicative (ZMod 2))) j) =
        a • Additive.ofMul (Multiplicative.ofAdd (1 : ZMod 2)) ∧
      ¬ (2 : ℤ) ∣ c i := by
  have hrank : finrank ℤ (Additive (Multiplicative (ZMod 2))) = 0 := by
    apply finrank_eq_zero_of_rank_eq_zero
    apply rank_eq_zero_iff.mpr
    intro x
    refine ⟨2, by decide, ?_⟩
    change (2 : ℤ) • (Additive.toMul x).toAdd = (0 : ZMod 2)
    rw [zsmul_eq_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]
  refine rankExcessRelation 2 Nat.prime_two
    (Multiplicative.ofAdd (1 : ZMod 2)) ?_ 1 (by omega) _
  intro ε n hε
  refine ⟨ε.toAdd.val, ?_⟩
  apply Multiplicative.toAdd.injective
  simp

/-- No alternative power normalization can create a coprime coordinate. -/
theorem compositeCoprimeImpossible :
    ¬ ∃ (n : ℕ) (g : Fin 3 → ℤ),
      ![0, 72, -108] = (6 : ℕ) ^ n • g ∧
        ∃ i, Nat.Coprime 6 (g i).natAbs := by
  rintro ⟨n, g, hfg, i, hi⟩
  have hpoint (j : Fin 3) :
      (![0, 72, -108] : Fin 3 → ℤ) j = (6 : ℤ) ^ n * g j := by
    simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat] using congrFun hfg j
  have hn : n ≤ 2 := by
    by_contra h
    have hthree : 3 ≤ n := by omega
    have hd : (6 : ℤ) ^ 3 ∣ 72 :=
      (pow_dvd_pow 6 hthree).trans ⟨g 1, hpoint 1⟩
    norm_num at hd
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  have hval := hpoint i
  have hv : g i = 0 ∨ g i = 72 ∨ g i = -108 ∨ g i = 12 ∨
      g i = -18 ∨ g i = 2 ∨ g i = -3 := by
    rcases hn' with rfl | rfl | rfl <;>
      fin_cases i <;> norm_num at hval ⊢ <;> omega
  rcases hv with h | h | h | h | h | h | h <;>
    norm_num [h, Nat.Coprime] at hi

end PrimitiveFamilyTest
