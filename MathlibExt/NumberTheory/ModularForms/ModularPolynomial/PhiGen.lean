/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_PhiGen.lean`,
`Theorems/Thm_ModularCurve_aeval_jq_eq_zero.lean`,
`P2M/Sol/S_ModularCurve_aeval_jq_eq_zero.lean`,
`Theorems/Thm_ModularCurve_transcendental_jq.lean`,
and
`P2M/Sol/S_ModularCurve_transcendental_jq.lean`
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

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.LaurentCoeff
import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

noncomputable section

open scoped PowerSeries.WithPiTopology
open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve

section QTwist

variable {R : Type*} [CommRing R]

/-- The coefficientwise twist `∑ aₖ qᵏ ↦ ∑ uᵏ aₖ qᵏ` of a Laurent series by a unit. -/
def qTwistFun (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R where
  coeff k := (u ^ k : Rˣ) * f.coeff k
  isPWO_support' := f.isPWO_support'.mono fun k hk => by
    simp only [Function.mem_support] at hk ⊢
    exact fun h => hk (by rw [h, mul_zero])

@[simp]
theorem qTwistFun_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) :
    (qTwistFun u f).coeff k = (u ^ k : Rˣ) * f.coeff k := rfl

theorem support_qTwistFun (u : Rˣ) (f : LaurentSeries R) :
    (qTwistFun u f).support = f.support := by
  ext k
  rw [HahnSeries.mem_support, HahnSeries.mem_support, qTwistFun_coeff]
  exact not_congr (Units.mul_right_eq_zero _)

open Finset renaming antidiagonal → pwoAntidiagonal, mem_antidiagonal → mem_pwoAntidiagonal in
/-- The twist `q ↦ u q` by a unit `u`, as a ring endomorphism of Laurent series. -/
def qTwist (u : Rˣ) : LaurentSeries R →+* LaurentSeries R where
  toFun := qTwistFun u
  map_one' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [mul_zero]
  map_mul' f g := by
    ext k
    have hset : pwoAntidiagonal (qTwistFun u f).isPWO_support
        (qTwistFun u g).isPWO_support k =
        pwoAntidiagonal f.isPWO_support g.isPWO_support k := by
      ext ij
      simp only [mem_pwoAntidiagonal, support_qTwistFun]
    rw [qTwistFun_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, hset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, hsum⟩ := mem_pwoAntidiagonal.mp hij
    rw [qTwistFun_coeff, qTwistFun_coeff, mul_mul_mul_comm, ← Units.val_mul, ← zpow_add,
      hsum]
  map_zero' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_zero, mul_zero]
  map_add' f g := by
    ext k
    rw [HahnSeries.coeff_add]
    change (qTwistFun u (f + g)).coeff k = (qTwistFun u f).coeff k + (qTwistFun u g).coeff k
    rw [qTwistFun_coeff, qTwistFun_coeff, qTwistFun_coeff, HahnSeries.coeff_add, mul_add]

@[simp]
theorem qTwist_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) :
    (qTwist u f).coeff k = (u ^ k : Rˣ) * f.coeff k := rfl

theorem support_qTwist (u : Rˣ) (f : LaurentSeries R) : (qTwist u f).support = f.support :=
  support_qTwistFun u f

@[simp]
theorem qTwist_single (u : Rˣ) (k : ℤ) (r : R) :
    qTwist u (HahnSeries.single k r) = HahnSeries.single k ((u ^ k : Rˣ) * r) := by
  ext m
  rw [qTwist_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero]

theorem qTwist_one_apply (f : LaurentSeries R) : qTwist (1 : Rˣ) f = f := by
  ext k
  rw [qTwist_coeff, one_zpow, Units.val_one, one_mul]

theorem qTwist_qTwist (u v : Rˣ) (f : LaurentSeries R) :
    qTwist u (qTwist v f) = qTwist (u * v) f := by
  ext k
  rw [qTwist_coeff, qTwist_coeff, qTwist_coeff, ← mul_assoc, ← Units.val_mul, ← mul_zpow]

theorem qTwist_injective (u : Rˣ) : Function.Injective (qTwist u) := by
  intro f g h
  have := congrArg (qTwist u⁻¹) h
  rwa [qTwist_qTwist, qTwist_qTwist, inv_mul_cancel, qTwist_one_apply, qTwist_one_apply]
    at this

theorem qTwist_qExpand (v : Rˣ) (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    qTwist v (qExpand R N f) = qExpand R N (qTwist (v ^ (N : ℤ)) f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qTwist_coeff, qExpand_coeff_mul, qExpand_coeff_mul, qTwist_coeff, ← zpow_mul]
  · rw [qTwist_coeff, qExpand_coeff_of_not_dvd N f hk, mul_zero,
      qExpand_coeff_of_not_dvd N _ hk]

end QTwist

section CosetSubst

variable {K : Type*} [Field K]

/-- The substitution `f(t) ↦ f(ζ ^ (a * b) * t ^ (a * a))` of Laurent series: twist by
`ζ ^ (a * b)`, then expand `t ↦ t ^ (a * a)`. When `ζ = e^(2πi/ℓ)`, `a * d = ℓ` and
`t ^ ℓ = q`, it sends the `q`-expansion of `j(τ)` to the expansion in `t` of `j(στ)` for
`σ = !![a, b; 0, d]` (D. A. Cox, *Primes of the Form x² + ny²*, 3rd ed., 2022, (11.13)). -/
def cosetSubst (ζ : Kˣ) (a b : ℕ) [NeZero a] : LaurentSeries K →+* LaurentSeries K :=
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  (qExpand K (a * a)).comp (qTwist (ζ ^ (a * b)))

end CosetSubst

section EvalAtJqN

variable (N : ℕ) [NeZero N]

/-- Evaluation of an integral polynomial at the `q`-expansion of `j(Nτ)`. -/
def evalAtJqN : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) (jqN N)).toRingHom

@[simp]
theorem evalAtJqN_X : evalAtJqN N Polynomial.X = jqN N := by
  simp [evalAtJqN]

theorem evalAtJqN_def : evalAtJqN N = (Polynomial.aeval (R := ℤ) (jqN N)).toRingHom := rfl

theorem evalAtJ_def : evalAtJ = (Polynomial.aeval (R := ℤ) jq).toRingHom := rfl

theorem evalAtJqN_one : evalAtJqN 1 = evalAtJ := by
  rw [evalAtJqN_def, evalAtJ_def, jqN_one]

end EvalAtJqN

/-- A Laurent series has a pole of order at most `n`: its coefficients of index below `-n`
vanish. -/
def PoleOrderLE {R : Type*} [Zero R] (f : LaurentSeries R) (n : ℕ) : Prop :=
  ∀ k : ℤ, k < -(n : ℤ) → f.coeff k = 0

section Named

variable {N : ℕ} [NeZero N]

/-- The modular polynomial, viewed over `ℚ(j)`, is irreducible. -/
def PhiIrreducible (data : ModularPolynomialData N) : Prop :=
  Irreducible data.toAdjoin

end Named

section AdjoinRing

/-- The `ℚ`-subalgebra of Laurent series generated by `j`. -/
abbrev adjoinJq : Subalgebra ℚ (LaurentSeries ℚ) := Algebra.adjoin ℚ {jq}

/-- The element `j` of `adjoinJq`. -/
def jAdj : adjoinJq := ⟨jq, Algebra.self_mem_adjoin_singleton ℚ jq⟩

/-- Evaluation of an integral polynomial at `j` inside `adjoinJq`. -/
def evalAtJAdj : Polynomial ℤ →+* adjoinJq :=
  Polynomial.eval₂RingHom (Int.castRingHom adjoinJq) jAdj

end AdjoinRing

namespace PhiGen

section CosetIndex

variable (ℓ : ℕ)

/-- The upper-left entry of the `i`-th matrix of the prime-level list: `!![ℓ, 0; 0, 1]` for
`i = 0` and `!![1, b; 0, ℓ]` for `i = b + 1`. For prime `ℓ` these `ℓ + 1` matrices are the set
`C(ℓ)` that Lemma 11.11 of D. A. Cox, *Primes of the Form x² + ny²* (3rd ed., 2022) matches with
the right cosets of `Γ₀(ℓ)` in `SL(2, ℤ)`; for composite `ℓ` the list misses some of `C(ℓ)` (at
`ℓ = 4`, the matrix `!![2, 1; 0, 2]`). -/
def cosetA (i : Fin (ℓ + 1)) : ℕ := if i = 0 then ℓ else 1

/-- The upper-right entry of the `i`-th matrix of the prime-level list: `!![ℓ, 0; 0, 1]` for
`i = 0` and `!![1, b; 0, ℓ]` for `i = b + 1`, which for prime `ℓ` is the set `C(ℓ)` of
Lemma 11.11 of D. A. Cox, *Primes of the Form x² + ny²* (3rd ed., 2022). -/
def cosetB (i : Fin (ℓ + 1)) : ℕ := if i = 0 then 0 else (i : ℕ) - 1

@[simp]
theorem cosetA_zero : cosetA ℓ (0 : Fin (ℓ + 1)) = ℓ := by simp [cosetA]

@[simp]
theorem cosetB_zero : cosetB ℓ (0 : Fin (ℓ + 1)) = 0 := by simp [cosetB]

@[simp]
theorem cosetA_succ (b : Fin ℓ) : cosetA ℓ b.succ = 1 := by
  simp [cosetA, Fin.succ_ne_zero]

@[simp]
theorem cosetB_succ (b : Fin ℓ) : cosetB ℓ b.succ = (b : ℕ) := by
  simp [cosetB, Fin.succ_ne_zero]

instance instNeZeroPhiGenCosetA [hℓ : Fact (Nat.Prime ℓ)] (i : Fin (ℓ + 1)) :
    NeZero (cosetA ℓ i) :=
  ⟨by unfold cosetA; split <;> simp [hℓ.out.ne_zero]⟩

end CosetIndex

section CosetSeries

variable {K : Type*} [Field K]

theorem cosetSubst_congr (ζ : Kˣ) {a a' b b' : ℕ} [NeZero a] [NeZero a'] (ha : a = a')
    (hb : b = b') (f : LaurentSeries K) : cosetSubst ζ a b f = cosetSubst ζ a' b' f := by
  subst ha; subst hb; rfl

variable [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The Laurent series `j(t ^ (ℓ * ℓ))` (for `i = 0`) and `j(ζ ^ b * t)` (for `i = b + 1`) in a
variable `t`, with the coefficients of `j` mapped into `K`: `cosetSubst` for the `i`-th matrix of
`cosetA` and `cosetB`, applied to `j`. When `ζ` is a primitive `ℓ`-th root of unity and
`t ^ ℓ = q`, these `ℓ + 1` series are, in some order, the expansions in `t` of all the conjugates
`j(στ)`, `σ ∈ C(ℓ)`, of `j` (D. A. Cox, *Primes of the Form x² + ny²*, 3rd ed., 2022,
(11.13)–(11.15)). -/
def conj (i : Fin (ℓ + 1)) : LaurentSeries K :=
  cosetSubst ζ (cosetA ℓ i) (cosetB ℓ i) (coeffEmb K jq)

theorem conj_zero : conj ℓ ζ (0 : Fin (ℓ + 1)) = qExpand K (ℓ * ℓ) (coeffEmb K jq) := by
  have h1 : conj ℓ ζ (0 : Fin (ℓ + 1)) = cosetSubst ζ ℓ 0 (coeffEmb K jq) :=
    cosetSubst_congr ζ (cosetA_zero ℓ) (cosetB_zero ℓ) (coeffEmb K jq)
  rw [h1, cosetSubst, RingHom.comp_apply, mul_zero, pow_zero, qTwist_one_apply]

theorem conj_succ (b : Fin ℓ) : conj ℓ ζ b.succ = qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq) := by
  have h1 : conj ℓ ζ b.succ = cosetSubst ζ 1 ((b : ℕ)) (coeffEmb K jq) :=
    cosetSubst_congr ζ (cosetA_succ ℓ b) (cosetB_succ ℓ b) (coeffEmb K jq)
  rw [h1, cosetSubst, RingHom.comp_apply,
    qExpand_congr (show 1 * 1 = 1 by norm_num), qExpand_one_apply, one_mul]

end CosetSeries

section Product

variable {K : Type*} [Field K] (ℓ : ℕ)

/-- The monic polynomial with the given `ℓ + 1` roots. -/
def phiProd (conj : Fin (ℓ + 1) → LaurentSeries K) : Polynomial (LaurentSeries K) :=
  ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i))

theorem phiProd_monic (conj : Fin (ℓ + 1) → LaurentSeries K) : (phiProd ℓ conj).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (conj i)

theorem phiProd_natDegree (conj : Fin (ℓ + 1) → LaurentSeries K) :
    (phiProd ℓ conj).natDegree = ℓ + 1 := by
  rw [phiProd, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp

theorem phiProd_ne_zero (conj : Fin (ℓ + 1) → LaurentSeries K) : phiProd ℓ conj ≠ 0 :=
  (phiProd_monic ℓ conj).ne_zero

theorem phiProd_eval_conj (conj : Fin (ℓ + 1) → LaurentSeries K) (i : Fin (ℓ + 1)) :
    (phiProd ℓ conj).eval (conj i) = 0 := by
  rw [phiProd, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

end Product

/-- All coefficients of a rational Laurent series are integers. -/
def IntCoeffs (f : LaurentSeries ℚ) : Prop :=
  ∀ m : ℤ, ∃ z : ℤ, f.coeff m = (z : ℚ)

section Descends

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The coefficients of the product `phiProd ℓ (conj ℓ ζ)` of the series `conj ℓ ζ i` descend
to `ℚ`: for each `k`, its `k`-th coefficient is the rational Laurent series `c k` in `q = t ^ ℓ`,
with its coefficients mapped into `K`. -/
def PhiGenDescends (c : ℕ → LaurentSeries ℚ) : Prop :=
  ∀ k : ℕ, (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))

end Descends

end PhiGen

theorem coeff_aeval_jq_neg (P : Polynomial ℚ) {m : ℕ} (hm : P.natDegree ≤ m) :
    (Polynomial.aeval jq P).coeff (-(m : ℤ)) = P.coeff m := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single m]
  · rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_self,
      mul_one]
  · intro i hi hin
    have hilt : i < m :=
      lt_of_le_of_ne (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hm) hin
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro hm'
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simp only [Finset.mem_range, not_lt] at hm'; omega),
      zero_mul]

theorem aeval_jq_eq_zero {p : Polynomial ℚ} (hp : Polynomial.aeval jq p = 0) : p = 0 := by
  by_contra hp0
  have hcoeff := coeff_aeval_jq_neg p le_rfl
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

/-- The `q`-expansion of `j` is transcendental over `ℚ`. -/
theorem transcendental_jq : Transcendental ℚ jq :=
  transcendental_iff.mpr fun _ hp => aeval_jq_eq_zero hp

end ModularCurve

end
