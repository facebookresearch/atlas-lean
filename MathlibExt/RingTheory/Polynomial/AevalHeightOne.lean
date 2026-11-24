/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero.lean` and
`P2M/Sol/S_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Polynomials with nonzero residue avoid height-one primes

Let `A` be a discrete valuation ring and `C` an integral domain with an
integral, injective `A[X]`-algebra structure given by evaluation at
`x : C`. A polynomial over `A` whose reduction in the residue field is
nonzero cannot evaluate into a height-one prime of `C` lying over the
maximal ideal of `A`.
-/

@[expose] public section

/-- A polynomial with nonzero residue does not evaluate into a height-one
prime above the maximal ideal. -/
public theorem Polynomial.aeval_notMem_of_height_eq_one_of_map_residue_ne_zero
    {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [Algebra A C]
    (x : C) (hx : Function.Injective (Polynomial.aeval (R := A) x))
    (hint : (Polynomial.aeval (R := A) x).toRingHom.IsIntegral)
    (Q : Ideal C) [Q.IsPrime] (hQ : Q.height = 1)
    (hQm : (IsLocalRing.maximalIdeal A).map (algebraMap A C) ≤ Q)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval x P ∉ Q := by
  classical
  intro hmem
  letI alg : Algebra (Polynomial A) C := (Polynomial.aeval (R := A) x).toRingHom.toAlgebra
  have halg : ∀ q : Polynomial A, algebraMap (Polynomial A) C q = Polynomial.aeval x q :=
    fun _ => rfl
  haveI : Algebra.IsIntegral (Polynomial A) C := ⟨hint⟩
  haveI : FaithfulSMul (Polynomial A) C :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial A) C).mpr hx
  let q : Ideal (Polynomial A) := Q.comap (algebraMap (Polynomial A) C)
  let q₀ : Ideal (Polynomial A) := (IsLocalRing.maximalIdeal A).map Polynomial.C
  haveI hq₀ : q₀.IsPrime := inferInstance
  haveI hq : q.IsPrime := inferInstance
  have hq₀q : q₀ ≤ q := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    show algebraMap (Polynomial A) C (Polynomial.C a) ∈ Q
    rw [halg, Polynomial.aeval_C]
    exact hQm (Ideal.mem_map_of_mem _ ha)
  have hPq : P ∈ q := hmem
  have hPq₀ : P ∉ q₀ := by
    intro h
    apply hP
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.mem_map_C_iff.mp h n
  have hlt : q₀ < q := lt_of_le_of_ne hq₀q (fun h => hPq₀ (h ▸ hPq))
  have hq₀ne : q₀ ≠ ⊥ := by
    intro h0
    exact IsDiscreteValuationRing.not_a_field A
      ((Ideal.map_eq_bot_iff_of_injective Polynomial.C_injective).mp h0)
  haveI hbp : (⊥ : Ideal (Polynomial A)).IsPrime := Ideal.isPrime_bot
  have hbot : (⊥ : Ideal (Polynomial A)) < q₀ := bot_lt_iff_ne_bot.mpr hq₀ne
  haveI : Q.LiesOver q := ⟨rfl⟩
  obtain ⟨Q₀, hQ₀Q, hQ₀p, hQ₀over⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := q₀) (q := q) Q hlt
  haveI := hQ₀p
  haveI := hQ₀over
  obtain ⟨Q', hQ'Q₀, -, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := q₀) Q₀ hbot
  have hQ₀ne : Q₀.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    exact ne_bot_of_gt hQ'Q₀
  have h1 : Q.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hQ]; exact_mod_cast le_rfl
  have hlt' := (Ideal.height_le_iff.mp h1) Q₀ hQ₀p hQ₀Q
  exact hQ₀ne (ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast hlt'))
