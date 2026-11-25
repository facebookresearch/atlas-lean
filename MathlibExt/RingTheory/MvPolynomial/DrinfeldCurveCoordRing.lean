/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_DrinfeldCurve_CoordRing.lean`,
`Theorems/Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one.lean`
and
`P2M/Sol/S_DrinfeldCurve_isDomain_coordRing_of_ne_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.Associated
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.ComputeDegree

@[expose] public section

open Polynomial

noncomputable section

namespace DrinfeldCurve

variable (q : ℕ) (k : Type*) [Field k]

/-- The Drinfeld polynomial `X₀ X₁ ^ q - X₀ ^ q X₁` in two variables. -/
public def drinfeldPoly : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1

/-- The ideal cutting out the Drinfeld curve `X₀ X₁ ^ q - X₀ ^ q X₁ = 1`. -/
public def drinfeldIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {drinfeldPoly q k - 1}

/-- The coordinate ring of the Drinfeld curve
`X₀ X₁ ^ q - X₀ ^ q X₁ = 1` over `k`. -/
public def CoordRing : Type _ := MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k

instance : CommRing (CoordRing q k) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k))

instance : Algebra k (CoordRing q k) :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k))

end DrinfeldCurve

namespace DrinfeldCurve

variable {k : Type*} [Field k]

private theorem irreducible_rev (m : ℕ) :
    Irreducible (X ^ (m + 2)
      - C ((MvPolynomial.X 0 : MvPolynomial (Fin 1) k) ^ (m + 2)) * X ^ (m + 1)
      + C (MvPolynomial.X 0 : MvPolynomial (Fin 1) k)) := by
  set y : MvPolynomial (Fin 1) k := MvPolynomial.X 0 with hy_def
  have hy : Prime y :=
    (MvPolynomial.X_prime : Prime (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k))
  have hy0 : y ≠ 0 := hy.ne_zero
  have hmonic : (X ^ (m + 2) - C (y ^ (m + 2)) * X ^ (m + 1) + C y).Monic := by
    monicity!
  have hdeg : (X ^ (m + 2) - C (y ^ (m + 2)) * X ^ (m + 1) + C y).natDegree = m + 2 := by
    compute_degree!
  have hP : (Ideal.span {y}).IsPrime := (Ideal.span_singleton_prime hy0).mpr hy
  refine Polynomial.IsEisensteinAt.irreducible (𝓟 := Ideal.span {y}) ⟨?_, ?_, ?_⟩ hP
    hmonic.isPrimitive ?_
  · rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]
    exact fun h => hy.not_isUnit (isUnit_of_dvd_one h)
  · intro n hn
    rw [hdeg] at hn
    rw [Ideal.mem_span_singleton]
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C]
    have h1 : n ≠ m + 2 := by omega
    rw [ite_eq_right h1, zero_sub]
    refine dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left (dvd_pow_self y (by omega)) _)) ?_
    split_ifs
    · exact dvd_rfl
    · exact dvd_zero y
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have hc : (X ^ (m + 2) - C (y ^ (m + 2)) * X ^ (m + 1) + C y).coeff 0 = y := by
      simp [coeff_zero_eq_eval_zero]
    rw [hc]
    intro h
    have h1 : y * y ∣ y * 1 := by rwa [mul_one, ← sq]
    exact hy.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hy0).mp h1))
  · omega

private theorem isUnit_of_isUnit_reverse {R : Type*} [CommRing R] [IsDomain R]
    {a : R[X]} (ha : a.coeff 0 ≠ 0) (hu : IsUnit a.reverse) : IsUnit a := by
  obtain ⟨r, hr, hra⟩ := Polynomial.isUnit_iff.mp hu
  have htrail : a.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr ha)
  have hdeg : a.natDegree = 0 := by
    have h := reverse_natDegree a
    rw [htrail, Nat.sub_zero, ← hra, natDegree_C] at h
    exact h.symm
  rw [eq_C_of_natDegree_eq_zero hdeg] at hra ⊢
  rw [reverse_C] at hra
  rw [← hra]
  exact isUnit_C.mpr hr

private theorem irreducible_of_reverse {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} (h0 : f.coeff 0 ≠ 0) (h : Irreducible f.reverse) : Irreducible f := by
  refine ⟨fun hu => h.not_isUnit ?_, fun a b hab => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [reverse_C]
    exact isUnit_C.mpr hr
  · have hab0 : a.coeff 0 * b.coeff 0 ≠ 0 := by rwa [← mul_coeff_zero, ← hab]
    have hrev : f.reverse = a.reverse * b.reverse := by rw [hab, reverse_mul_of_domain]
    rcases h.isUnit_or_isUnit hrev with ha | hb
    · exact Or.inl (isUnit_of_isUnit_reverse (left_ne_zero_of_mul hab0) ha)
    · exact Or.inr (isUnit_of_isUnit_reverse (right_ne_zero_of_mul hab0) hb)

private theorem irreducible_rel (m : ℕ) :
    Irreducible (C (MvPolynomial.X 0 : MvPolynomial (Fin 1) k) * X ^ (m + 2)
      - C ((MvPolynomial.X 0 : MvPolynomial (Fin 1) k) ^ (m + 2)) * X + 1) := by
  set y : MvPolynomial (Fin 1) k := MvPolynomial.X 0 with hy_def
  have hy0 : y ≠ 0 := MvPolynomial.X_ne_zero 0
  set F : Polynomial (MvPolynomial (Fin 1) k) :=
    C y * X ^ (m + 2) - C (y ^ (m + 2)) * X + 1 with hF_def
  have hdeg : F.natDegree = m + 2 := by
    rw [hF_def]
    compute_degree!
    all_goals (rw [ite_eq_right (by omega), sub_zero]; exact hy0)
  have h0 : F.coeff 0 ≠ 0 := by
    rw [hF_def]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
    rw [ite_eq_right (by omega : (0 : ℕ) ≠ m + 2)]
    simp
  refine irreducible_of_reverse h0 ?_
  have hrev : F.reverse
      = X ^ (m + 2) - C (y ^ (m + 2)) * X ^ (m + 1) + C y := by
    rw [Polynomial.reverse, hdeg, hF_def, reflect_add, reflect_sub, reflect_C_mul_X_pow,
      ← pow_one (X : (MvPolynomial (Fin 1) k)[X]), reflect_C_mul_X_pow, ← C_1, reflect_C,
      C_1, one_mul, revAt_le (le_refl _), revAt_le (by omega : 1 ≤ m + 2), Nat.sub_self,
      pow_zero, mul_one, pow_one]
    have : m + 2 - 1 = m + 1 := by omega
    rw [this]
    ring
  rw [hrev]
  exact irreducible_rev m

private theorem prime_rel (q : ℕ) (hq : q ≠ 1) :
    Prime (1 - drinfeldPoly q k) := by
  rw [← MulEquiv.prime_iff (MvPolynomial.finSuccEquiv k 1)]
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = MvPolynomial.X (Fin.succ 0) :=
    rfl
  have himg : MvPolynomial.finSuccEquiv k 1 (1 - drinfeldPoly q k)
      = C (MvPolynomial.X 0) * X ^ q
        - C ((MvPolynomial.X 0 : MvPolynomial (Fin 1) k) ^ q) * X + 1 := by
    rw [drinfeldPoly, hX1, map_sub, map_one, map_sub, map_mul, map_mul, map_pow, map_pow,
      MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ, ← C_pow]
    ring
  rw [himg]
  rcases q with _ | _ | m
  · have : C (MvPolynomial.X 0) * X ^ 0
        - C ((MvPolynomial.X 0 : MvPolynomial (Fin 1) k) ^ 0) * X + 1
        = -(X - C (MvPolynomial.X 0 + 1)) := by
      rw [pow_zero, pow_zero, mul_one, C_1, one_mul, map_add, C_1]
      ring
    rw [this]
    exact ((Associated.refl _).neg_right).prime (prime_X_sub_C _)
  · exact absurd rfl hq
  · exact (irreducible_rel m).prime

/-- The coordinate ring of the Drinfeld curve `X₀ X₁ ^ q - X₀ ^ q X₁ = 1`
over a field `k` is a domain for every natural `q ≠ 1`, including `q = 0`. -/
public theorem isDomain_coordRing_of_ne_one (q : ℕ) (hq : q ≠ 1) (k : Type*) [Field k] :
    IsDomain (CoordRing q k) := by
  have hp : Prime (1 - drinfeldPoly q k) := prime_rel q hq
  have hI : drinfeldIdeal q k = Ideal.span {1 - drinfeldPoly q k} := by
    rw [drinfeldIdeal, ← Ideal.span_singleton_neg, neg_sub]
  have hP : (Ideal.span {1 - drinfeldPoly q k}).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  change IsDomain (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k)
  rw [hI]
  infer_instance

end DrinfeldCurve
