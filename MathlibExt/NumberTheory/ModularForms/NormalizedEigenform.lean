/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_isNormalizedEigenform.lean`,
`P2M/Sol/S_CuspForm_exists_isNormalizedEigenform.lean`,
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean`,
`P2M/Sol/S_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean`,
`Theorems/Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean`,
`P2M/Sol/S_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean`,
`Theorems/Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean`,
`P2M/Sol/S_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean`,
`Theorems/Thm_CuspForm_finiteDimensional_Gamma0.lean`,
`Theorems/Thm_CuspForm_qCoeff_zero.lean`
and
`P2M/Sol/S_CuspForm_qCoeff_zero.lean`
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
The predicate `CuspForm.IsNormalizedEigenform` and the coefficient function
`ModularFormClass.qCoeff` are reused from existing files in this repository,
where they are definitionally the corresponding source carriers. The
finite-dimensionality of `S_k(Γ₀(N))` is derived here from the Sturm bound
for `Γ₀(N)` already in this repository, instead of the source's argument.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.NumberTheory.ModularForms.HeckeOperator
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector
import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
import MathlibExt.NumberTheory.ModularForms.HeckeOperator.CoeffCommute
import MathlibExt.NumberTheory.ModularForms.QCoeffExt
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0
import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0

/-!
# Existence of normalized eigenforms of weight two

For `N ≠ 0`, a nonzero space `S_2(Γ₀(N))` of weight-two cusp forms contains a normalized
eigenform: a cusp form whose `q`-expansion coefficients satisfy `a 1 = 1`,
multiplicativity at coprime indices and the Hecke recurrences at prime powers.

For `N ≠ 0` the space is finite-dimensional (by the Sturm bound), and the Hecke operators
`CuspForm.heckeTLin` (`T p` for primes `p ∤ N`) and `CuspForm.heckeULin` (`U p` for primes `p ∣ N`)
act on it as pairwise commuting endomorphisms, so they have a common eigenvector `f₀`
(`Module.End.exists_common_eigenvector_of_commute`). The Hecke eigen-relations force `a 1 ≠ 0` for
its coefficients `a`, and after dividing by `a 1` the eigenvalue of the operator at `p` is `a p`.
The eigen-relations with these eigenvalues are equivalent to the defining coefficient identities of
a normalized eigenform.

## Main results

* `CuspForm.finiteDimensional_Gamma0`: for `N ≠ 0`, `S_k(Γ₀(N))` is finite-dimensional (an
  instance).
* `CuspForm.isNormalizedEigenform_iff_coeffHecke`: normalized eigenforms are
  characterized by the Hecke eigen-relations on their coefficients.
* `CuspForm.exists_isNormalizedEigenform`: the main theorem.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped ModularForm MatrixGroups

namespace ModularForm

/-- If a coefficient sequence is an eigenvector of the coefficient Hecke operators of weight
`k` (`T p` for primes `p ∤ N`, `U p` for primes `p ∣ N`) and its first coefficient vanishes,
then all its coefficients of positive index vanish. -/
public theorem eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero (k : ℤ) (N : ℕ)
    (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      exact h1
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmlt : m < p * m := by nlinarith [hp.two_le]
      have ham : a m = 0 := ih m hmlt hm0
      by_cases hpN : p ∣ N
      · have h := hU p hp hpN m
        rw [coeffHeckeU_apply, ham, mul_zero, mul_comm m p] at h
        exact h
      · have h := hT p hp hpN m
        rw [coeffHeckeT_apply, ham, mul_zero, mul_comm m p] at h
        by_cases hpm : p ∣ m
        · obtain ⟨q, rfl⟩ := hpm
          have hq0 : q ≠ 0 := by rintro rfl; simp at hm0
          have hqlt : q < p * (p * q) := by
            have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
            nlinarith [hp.two_le]
          have haq : a q = 0 := ih q hqlt hq0
          rw [ite_eq_left (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos, haq, mul_zero,
            add_zero] at h
          exact h
        · rw [ite_eq_right hpm, add_zero] at h
          exact h

/-- If a coefficient sequence with first coefficient `1` is an eigenvector of the coefficient
Hecke operators of weight `k` (`T p` for primes `p ∤ N`, `U p` for primes `p ∣ N`), then the
eigenvalue at a prime `p` is its `p`-th coefficient. -/
public theorem coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one (k : ℤ) (N : ℕ)
    (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p := by
  intro p hp
  by_cases hpN : p ∣ N
  · have h := hU p hp hpN 1
    rw [coeffHeckeU_apply, one_mul, h1, mul_one] at h
    exact h.symm
  · have h := hT p hp hpN 1
    rw [coeffHeckeT_apply, ite_eq_right hp.not_dvd_one, add_zero, one_mul, h1, mul_one] at h
    exact h.symm

end ModularForm

namespace CuspForm

/-- The constant `q`-expansion coefficient of a cusp form on `Γ₀(N)` vanishes. -/
public theorem qCoeff_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularFormClass.qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)

/-- The `q`-expansion coefficients of a cusp form on `Γ₀(N)` are linear in the form
with respect to scalar multiplication. -/
public theorem qCoeff_smul {N : ℕ} {k : ℤ} (c : ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(c • f) n = c * ModularFormClass.qCoeff ⇑f n := by
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) c f, map_smul, smul_eq_mul]

private theorem qCoeff_add {N : ℕ} {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff ⇑(f + g) n =
      ModularFormClass.qCoeff ⇑f n + ModularFormClass.qCoeff ⇑g n := by
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) f g, map_add]

/-- For `N ≠ 0`, the space `S_k(Γ₀(N))` of cusp forms of weight `k` on `Γ₀(N)` is
finite-dimensional. -/
public instance finiteDimensional_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by
  set B := (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12
  let Φ : CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] (Fin (B + 1) → ℂ) :=
    { toFun := fun f i => ModularFormClass.qCoeff f i
      map_add' := fun f g => funext fun i => qCoeff_add f g i
      map_smul' := fun c f => funext fun i => qCoeff_smul c f i }
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).mpr fun f hf => ?_)
  apply CuspForm.toModularFormₗ_injective
  rw [map_zero]
  refine ModularForm.sturm_bound_Gamma0 N _ fun n hn => ?_
  have := congrFun hf ⟨n, Nat.lt_succ_of_le hn⟩
  exact this

open ModularForm ModularFormClass

section Arithmetic

variable (a : ℕ → ℂ)

private theorem coeffHeckeT_two (p n : ℕ) :
    coeffHeckeT 2 p a n = a (n * p) + if p ∣ n then (p : ℂ) * a (n / p) else 0 := by
  rw [coeffHeckeT_apply, show (p : ℂ) ^ ((2 : ℤ) - 1) = p by norm_num]

private theorem coprime_pow_of_not_dvd {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (k : ℕ) :
    (p ^ k).Coprime m :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)

private theorem heckeT_eigen_of_rec {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r)) (n : ℕ) :
    coeffHeckeT 2 p a n = a p * a n := by
  rw [coeffHeckeT_two]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  cases r with
  | zero =>
    have hpm : ¬ p ∣ p ^ 0 * m := by simpa using hm
    rw [ite_eq_right hpm, add_zero, pow_zero, one_mul, hmul m p
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)), mul_comm]
  | succ s =>
    have hpn : p ∣ p ^ (s + 1) * m :=
      dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
    have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
      rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [ite_eq_left hpn, hdiv, show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 2)),
      hmul _ _ (coprime_pow_of_not_dvd hp hm s),
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 1)), hrec s]
    ring

private theorem heckeU_eigen_of_rec {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1))) (n : ℕ) :
    coeffHeckeU p a n = a p * a n := by
  rw [coeffHeckeU_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hstep : a (p ^ (r + 1)) = a p * a (p ^ r) := by
    cases r with
    | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
    | succ s => exact hrec s
  rw [show p ^ r * m * p = p ^ (r + 1) * m by ring,
    hmul _ _ (coprime_pow_of_not_dvd hp hm (r + 1)),
    hmul _ _ (coprime_pow_of_not_dvd hp hm r), hstep]
  ring

private theorem rec_of_heckeT_eigen {p : ℕ} (hp : p.Prime)
    (hT : ∀ n : ℕ, coeffHeckeT 2 p a n = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r) := by
  have h := hT (p ^ (r + 1))
  have hpn : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
  have hdiv : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ', Nat.mul_div_cancel_left _ hp.pos]
  rw [coeffHeckeT_two, ite_eq_left hpn, hdiv, ← pow_succ] at h
  linear_combination h

private theorem rec_of_heckeU_eigen {p : ℕ} (hU : ∀ n : ℕ, coeffHeckeU p a n = a p * a n)
    (r : ℕ) : a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) := by
  have h := hU (p ^ (r + 1))
  rwa [coeffHeckeU_apply, ← pow_succ] at h

private theorem pow_mul_of_heckeT_eigen {p : ℕ} (hp : p.Prime) (h1 : a 1 = 1)
    (hT : ∀ n : ℕ, coeffHeckeT 2 p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro m hm
    match r, ih with
    | 0, _ => rw [pow_zero, one_mul, h1, one_mul]
    | 1, _ =>
      have h := hT m
      rw [coeffHeckeT_two, ite_eq_right hm, add_zero] at h
      rw [pow_one, mul_comm p m, h]
    | s + 2, ih =>
      have h := hT (p ^ (s + 1) * m)
      have hpn : p ∣ p ^ (s + 1) * m :=
        dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
      have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
        rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
      rw [coeffHeckeT_two, ite_eq_left hpn, hdiv,
        show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
        ih (s + 1) (by omega) m hm, ih s (by omega) m hm] at h
      rw [rec_of_heckeT_eigen a hp hT s]
      linear_combination h

private theorem pow_mul_of_heckeU_eigen {p : ℕ} (h1 : a 1 = 1)
    (hU : ∀ n : ℕ, coeffHeckeU p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r with
  | zero => intro m _; rw [pow_zero, one_mul, h1, one_mul]
  | succ s ih =>
    intro m hm
    have h := hU (p ^ s * m)
    rw [coeffHeckeU_apply, show p ^ s * m * p = p ^ (s + 1) * m by ring, ih m hm] at h
    have hstep : a (p ^ (s + 1)) = a p * a (p ^ s) := by
      cases s with
      | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
      | succ t => exact rec_of_heckeU_eigen a hU t
    rw [h, hstep]
    ring

private theorem mul_of_coprime_of_pow_mul (h1 : a 1 = 1)
    (hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [Nat.coprime_zero_left] at hmn
        subst hmn
        rw [mul_one, h1, mul_one]
      · rw [one_mul, h1, one_mul]
    · have hm0 : m ≠ 0 := by omega
      have hm1 : m ≠ 1 := by omega
      set p := m.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      obtain ⟨r, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
      have hr : r ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hmeq
        exact hm' (hmeq ▸ hpm)
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero (fun h0 => hm0 (by rw [hmeq, h0, mul_zero]))
      have hm'lt : m' < m := by
        have hpr : 2 ≤ p ^ r := by
          calc 2 ≤ p := hp.two_le
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hr)
        calc m' = 1 * m' := (one_mul _).symm
          _ < p ^ r * m' := Nat.mul_lt_mul_of_pos_right (by omega) hm'pos
          _ = m := hmeq.symm
      have hpn : ¬ p ∣ n := fun hdvd =>
        hp.ne_one (Nat.eq_one_of_dvd_coprimes hmn hpm hdvd)
      have hm'n : m'.Coprime n :=
        Nat.Coprime.coprime_dvd_left (⟨p ^ r, by rw [hmeq]; ring⟩ : m' ∣ m) hmn
      have hpm'n : ¬ p ∣ m' * n := fun hdvd =>
        (hp.dvd_mul.mp hdvd).elim hm' hpn
      rw [hmeq, show p ^ r * m' * n = p ^ r * (m' * n) by ring, hpow p hp r (m' * n) hpm'n,
        ih m' hm'lt n hm'n, hpow p hp r m' hm']
      ring

end Arithmetic

/-- A weight-two cusp form on `Γ₀(N)` is a normalized eigenform if and only if its
first coefficient is `1` and its coefficient sequence is an eigenvector of the
coefficient Hecke operators `T p` (for primes `p ∤ N`) and `U p` (for primes
`p ∣ N`) with eigenvalue its `p`-th coefficient. -/
public theorem isNormalizedEigenform_iff_coeffHecke {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔
      (qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
        ((¬ p ∣ N → ∀ n : ℕ, coeffHeckeT 2 p (qCoeff f) n = qCoeff f p * qCoeff f n) ∧
          (p ∣ N → ∀ n : ℕ, coeffHeckeU p (qCoeff f) n = qCoeff f p * qCoeff f n))) := by
  have h0 : qCoeff f 0 = 0 := qCoeff_zero f
  constructor
  · intro hf
    refine ⟨hf.qCoeff_one, fun p hp => ⟨fun hpN n => ?_, fun hpN n => ?_⟩⟩
    · exact heckeT_eigen_of_rec (qCoeff f) hp h0 hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_not_dvd p r hp hpN) n
    · exact heckeU_eigen_of_rec (qCoeff f) hp h0 hf.qCoeff_one hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_dvd p r hp hpN) n
  · rintro ⟨h1, hE⟩
    have hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m →
        qCoeff f (p ^ r * m) = qCoeff f (p ^ r) * qCoeff f m := by
      intro p hp
      by_cases hpN : p ∣ N
      · exact pow_mul_of_heckeU_eigen (qCoeff f) h1 ((hE p hp).2 hpN)
      · exact pow_mul_of_heckeT_eigen (qCoeff f) hp h1 ((hE p hp).1 hpN)
    exact
      { qCoeff_one := h1
        qCoeff_mul_of_coprime := mul_of_coprime_of_pow_mul (qCoeff f) h1 hpow
        qCoeff_prime_pow_of_not_dvd := fun p r hp hpN =>
          rec_of_heckeT_eigen (qCoeff f) hp ((hE p hp).1 hpN) r
        qCoeff_prime_pow_of_dvd := fun p r hp hpN =>
          rec_of_heckeU_eigen (qCoeff f) ((hE p hp).2 hpN) r }

section Operators

/-- The coefficient Hecke operator at `p`: `U p` when `p ∣ N`, `T p` otherwise. -/
private def ck (N p : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  if p ∣ N then coeffHeckeU p a else coeffHeckeT 2 p a

private theorem ck_comm (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a : ℕ → ℂ) : ck N p (ck N q a) = ck N q (ck N p a) := by
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  unfold ck; split_ifs with h1 h2
  · exact coeffHeckeU_comm p q a
  · exact (coeffHeckeT_coeffHeckeU_comm_of_coprime 2 hco.symm a).symm
  · exact coeffHeckeT_coeffHeckeU_comm_of_coprime 2 hco a
  · exact coeffHeckeT_comm_of_coprime 2 hco a

private theorem qCoeff_zero' {N : ℕ} (n : ℕ) :
    qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) n = 0 := by
  have := qCoeff_smul (N := N) (k := 2) 0 0 n
  rwa [zero_smul, zero_mul] at this

variable {N : ℕ} [NeZero N]

/-- The Hecke operator at `p` on `S_2(Γ₀(N))`: `CuspForm.heckeULin` when `p ∣ N`,
`CuspForm.heckeTLin` for a prime `p ∤ N`, and `0` when `p` is not prime. -/
private def op (N : ℕ) [NeZero N] (p : ℕ) :
    Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  if hp : p.Prime then
    if hpN : p ∣ N then CuspForm.heckeULin 2 hpN else CuspForm.heckeTLin 2 hp hpN
  else 0

private theorem op_of_not_prime {p : ℕ} (hp : ¬ p.Prime) : op N p = 0 := by
  unfold op; rw [dite_eq_right hp]

private theorem qCoeff_op {p : ℕ} (hp : p.Prime) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    qCoeff ⇑(op N p f) = ck N p (qCoeff ⇑f) := by
  funext n
  unfold op ck
  rw [dite_eq_left hp]
  by_cases hpN : p ∣ N
  · rw [dite_eq_left hpN, ite_eq_left hpN, CuspForm.coe_heckeULin_apply]
    exact qCoeff_heckeU f (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) hp.ne_zero n
  · rw [dite_eq_right hpN, ite_eq_right hpN, CuspForm.coe_heckeTLin_apply]
    exact qCoeff_heckeT f (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) hp.ne_zero n

private theorem op_commute (p q : ℕ) : Commute (op N p) (op N q) := by
  by_cases hp : p.Prime
  swap
  · rw [op_of_not_prime hp]; exact Commute.zero_left _
  by_cases hq : q.Prime
  swap
  · rw [op_of_not_prime hq]; exact Commute.zero_right _
  rcases eq_or_ne p q with rfl | hpq
  · exact Commute.refl _
  refine LinearMap.ext fun f => ?_
  change op N p (op N q f) = op N q (op N p f)
  apply eq_of_forall_qCoeff_eq (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
  intro n
  have h1 := congrFun (qCoeff_op hp (op N q f)) n
  have h2 := congrFun (qCoeff_op hq (op N p f)) n
  rw [h1, h2, qCoeff_op hq f, qCoeff_op hp f, ck_comm N hp hq hpq]

end Operators

/-- For `N ≠ 0`, a nonzero space `S_2(Γ₀(N))` of weight-two cusp forms on `Γ₀(N)` contains a
normalized eigenform. -/
public theorem exists_isNormalizedEigenform {N : ℕ} [NeZero N]
    (h : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g ≠ 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform := by
  classical
  obtain ⟨g, hg⟩ := h
  have : Nontrivial (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := nontrivial_of_ne g 0 hg
  obtain ⟨c, f₀, hf₀, hc⟩ := Module.End.exists_common_eigenvector_of_commute (op N)
    fun p q => op_commute p q
  set a : ℕ → ℂ := qCoeff ⇑f₀ with ha
  have hck : ∀ p : ℕ, p.Prime → ∀ n, ck N p a n = c p * a n := by
    intro p hp n
    have := congrFun (qCoeff_op hp f₀) n
    rw [hc p] at this
    rw [← this, qCoeff_smul]
  have hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, coeffHeckeT 2 p a n = c p * a n := by
    intro p hp hpN n; have := hck p hp n; unfold ck at this; rwa [ite_eq_right hpN] at this
  have hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, coeffHeckeU p a n = c p * a n := by
    intro p hp hpN n; have := hck p hp n; unfold ck at this; rwa [ite_eq_left hpN] at this
  have ha1 : a 1 ≠ 0 := by
    intro h1
    apply hf₀
    apply eq_of_forall_qCoeff_eq (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
    intro n
    rw [qCoeff_zero']
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact qCoeff_zero f₀
    · exact eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero 2 N a c hT hU h1 n hn.ne'
  set f : CuspForm (CongruenceSubgroup.Gamma0 N) 2 := (a 1)⁻¹ • f₀ with hf
  have hqf : ∀ n, qCoeff ⇑f n = (a 1)⁻¹ * a n := fun n => qCoeff_smul _ _ n
  have hqf' : qCoeff ⇑f = (a 1)⁻¹ • a := funext fun n => by rw [hqf n]; rfl
  have hf1 : qCoeff ⇑f 1 = 1 := by rw [hqf 1, inv_mul_cancel₀ ha1]
  have hT' : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      coeffHeckeT 2 p (qCoeff ⇑f) n = c p * qCoeff ⇑f n := by
    intro p hp hpN n
    rw [hqf', coeffHeckeT_smul, Pi.smul_apply, hT p hp hpN n, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  have hU' : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ,
      coeffHeckeU p (qCoeff ⇑f) n = c p * qCoeff ⇑f n := by
    intro p hp hpN n
    rw [hqf', coeffHeckeU_smul, Pi.smul_apply, hU p hp hpN n, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  have hcp : ∀ p : ℕ, p.Prime → c p = qCoeff ⇑f p :=
    coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one 2 N _ c hT' hU' hf1
  refine ⟨f, (isNormalizedEigenform_iff_coeffHecke f).mpr ⟨hf1, fun p hp => ⟨?_, ?_⟩⟩⟩
  · intro hpN n; rw [hT' p hp hpN n, hcp p hp]
  · intro hpN n; rw [hU' p hp hpN n, hcp p hp]

end CuspForm
