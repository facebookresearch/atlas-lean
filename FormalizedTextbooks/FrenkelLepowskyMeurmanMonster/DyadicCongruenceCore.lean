/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module

/-! Arithmetic ingredients for the principal congruence kernel modulo three.

These statements concern arbitrary matrices over a characteristic-zero domain.
They do not claim that the constructed Griess action has dyadic entries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A first-order binomial expansion with an explicit higher-order remainder,
valid in a noncommutative ring. -/
theorem congruence_one_add_pow_first_order {S : Type*} [Ring S]
    (X : S) (q : ℕ) : ∃ C : S, (1 + X) ^ q = 1 + q • X + X ^ 2 * C := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨(q : S) + C + X * C, ?_⟩
    rw [pow_succ', hC, succ_nsmul, nsmul_eq_mul]
    noncomm_ring
    rw [Nat.cast_comm q X]
    abel

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem congruence_matrix_pow_first_order (c : R) (B : Matrix n n R) (q : ℕ) :
    ∃ C : Matrix n n R, (1 + c • B) ^ q = 1 + c • (q • B + c • C) := by
  obtain ⟨C, hC⟩ := congruence_one_add_pow_first_order (c • B) q
  refine ⟨B ^ 2 * C, ?_⟩
  rw [hC]
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    smul_comm q c, mul_assoc]
  abel

/-- The extra factor of three in the cubic case is the reason reduction
modulo three, rather than modulo two, excludes finite torsion. -/
theorem congruence_matrix_cube (c : R) (B : Matrix n n R) :
    (1 + (3 * c) • B) ^ 3 =
      1 + (9 * c) • (B + (3 * c) • B ^ 2 + (3 * c ^ 2) • B ^ 3) := by
  simp only [pow_succ, pow_zero, mul_one, mul_add, add_mul, one_mul,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, mul_assoc]
  module

omit [Fintype n] [DecidableEq n] in
/-- In characteristic three a different prime acts invertibly. -/
theorem congruence_matrix_residue_first_order (π : R →+* ZMod 3)
    (q : ℕ) (hq : q.Prime) (hq3 : q ≠ 3)
    (B C : Matrix n n R) (k : ℕ) (hk : 0 < k)
    (heq : q • B + (3 : R) ^ k • C = 0) : B.map π = 0 := by
  have hqne : (q : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with he | he
    · exact (by decide : (3 : ℕ) ≠ 1) he
    · exact hq3 he.symm
  ext i j
  change π (B i j) = 0
  have h := congrArg (fun A : Matrix n n R => π (A i j)) heq
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.smul_apply,
    smul_eq_mul, map_zero] at h
  have hπ3 : π (3 : R) = 0 := by rw [map_ofNat]; rfl
  have h' : (q : ZMod 3) * π (B i j) = 0 := by
    simpa only [nsmul_eq_mul, map_add, map_mul, map_natCast, map_pow, hπ3,
      zero_pow (Nat.ne_of_gt hk), zero_mul, add_zero] using h
  exact (mul_eq_zero.mp h').resolve_left hqne

omit [Fintype n] [DecidableEq n] in
/-- Exactness of scalar reduction lifts zero residue matrices entrywise. -/
theorem congruence_matrix_kernel_lift (π : R →+* ZMod 3)
    (hker : ∀ x : R, π x = 0 → ∃ y : R, x = 3 * y)
    (B : Matrix n n R) (hB : B.map π = 0) :
    ∃ D : Matrix n n R, B = (3 : R) • D := by
  classical
  have hex (i j : n) : ∃ y : R, B i j = 3 * y :=
    hker _ (congrFun (congrFun hB i) j)
  choose D hD using hex
  exact ⟨D, by ext i j; exact hD i j⟩

variable [IsDomain R] [CharZero R]

/-- Prime-order matrices congruent to one modulo a positive power of three
are congruent modulo the next power. Scalar kernel exactness is explicit. -/
theorem congruence_matrix_prime_step (π : R →+* ZMod 3)
    (hker : ∀ x : R, π x = 0 → ∃ y : R, x = 3 * y)
    (q : ℕ) (hq : q.Prime) (A : Matrix n n R) (horder : A ^ q = 1)
    (k : ℕ) (B : Matrix n n R) (hA : A = 1 + (3 : R) ^ (k + 1) • B) :
    ∃ D : Matrix n n R, A = 1 + (3 : R) ^ (k + 2) • D := by
  have hB : B.map π = 0 := by
    by_cases hq3 : q = 3
    · subst q
      have hc : (3 : R) ^ (k + 1) = 3 * (3 : R) ^ k := by
        rw [pow_succ, mul_comm]
      rw [hA, hc, congruence_matrix_cube] at horder
      have hzero : (9 * (3 : R) ^ k) •
          (B + (3 * (3 : R) ^ k) • B ^ 2 + (3 * ((3 : R) ^ k) ^ 2) • B ^ 3) = 0 :=
        (add_eq_left.mp horder)
      have hinner := (smul_eq_zero.mp hzero).resolve_left
        (mul_ne_zero (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0))
          (pow_ne_zero _ (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0))))
      ext i j
      change π (B i j) = 0
      have h := congrArg (fun M : Matrix n n R => π (M i j)) hinner
      simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.smul_apply,
        smul_eq_mul, map_add, map_mul, map_zero] at h
      have hπ3 : π (3 : R) = 0 := by rw [map_ofNat]; rfl
      simpa only [hπ3, zero_mul, add_zero] using h
    · obtain ⟨C, hC⟩ := congruence_matrix_pow_first_order ((3 : R) ^ (k + 1)) B q
      rw [hA, hC] at horder
      have hzero : (3 : R) ^ (k + 1) • (q • B + (3 : R) ^ (k + 1) • C) = 0 :=
        add_eq_left.mp horder
      have hinner := (smul_eq_zero.mp hzero).resolve_left
        (pow_ne_zero _ (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)))
      exact congruence_matrix_residue_first_order π q hq hq3 B C (k + 1)
        (Nat.succ_pos _) hinner
  obtain ⟨D, hD⟩ := congruence_matrix_kernel_lift π hker B hB
  refine ⟨D, ?_⟩
  rw [hA, hD, smul_smul]
  congr 2
  exact (pow_succ (3 : R) (k + 1)).symm

variable [IsNoetherianRing R]

omit [Fintype n] [DecidableEq n] [CharZero R] in
/-- Krull intersection separates the powers of three in any Noetherian
domain admitting reduction to F₃. -/
theorem congruence_three_power_separated (π : R →+* ZMod 3) (x : R)
    (hx : ∀ k : ℕ, (3 : R) ^ k ∣ x) : x = 0 := by
  let I : Ideal R := Ideal.span {3}
  have hI : I ≠ ⊤ := by
    intro h
    have hu : IsUnit (3 : R) := Ideal.span_singleton_eq_top.mp h
    have hv := hu.map π
    have hπ3 : π (3 : R) = 0 := by rw [map_ofNat]; rfl
    rw [hπ3] at hv
    exact not_isUnit_zero hv
  have hmem : x ∈ ⨅ k : ℕ, I ^ k := by
    simp only [Submodule.mem_iInf]
    intro k
    change x ∈ (Ideal.span {(3 : R)}) ^ k
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k
  rw [Ideal.iInf_pow_eq_bot_of_isDomain I hI] at hmem
  exact hmem

/-- Prime-order torsion cannot lie in the principal congruence kernel
modulo three. This is a matrix theorem with an exact scalar reduction input. -/
theorem congruence_matrix_prime_order_eq_one (π : R →+* ZMod 3)
    (hker : ∀ x : R, π x = 0 → ∃ y : R, x = 3 * y)
    (q : ℕ) (hq : q.Prime) (A : Matrix n n R) (horder : A ^ q = 1)
    (hcongr : A.map π = 1) : A = 1 := by
  have hdiff : (A - 1).map π = 0 := by
    ext i j
    have h := congrFun (congrFun hcongr i) j
    change π (A i j) = (1 : Matrix n n (ZMod 3)) i j at h
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [h]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨B, hB⟩ := congruence_matrix_kernel_lift π hker (A - 1) hdiff
  have hstart : A = 1 + (3 : R) ^ (0 + 1) • B := by
    rw [pow_one]
    exact sub_eq_iff_eq_add.mp hB |>.trans (add_comm _ _)
  have hiter : ∀ k : ℕ, ∃ B : Matrix n n R,
      A = 1 + (3 : R) ^ (k + 1) • B := by
    intro k
    induction k with
    | zero => exact ⟨B, hstart⟩
    | succ k ih =>
      obtain ⟨B, hB⟩ := ih
      exact congruence_matrix_prime_step π hker q hq A horder k B hB
  ext i j
  apply sub_eq_zero.mp
  apply congruence_three_power_separated π
  intro k
  obtain ⟨B, hB⟩ := hiter k
  refine ⟨3 * B i j, ?_⟩
  have hsub : A - 1 = (3 : R) ^ (k + 1) • B := by rw [hB, add_sub_cancel_left]
  have h := congrFun (congrFun hsub i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [h, pow_succ, mul_assoc]

/-- Every finite-order matrix congruent to the identity modulo three is
the identity. The argument extracts a prime-order power if necessary. -/
theorem congruence_matrix_finite_order_eq_one (π : R →+* ZMod 3)
    (hker : ∀ x : R, π x = 0 → ∃ y : R, x = 3 * y)
    (A : Matrix n n R) (hfinite : IsOfFinOrder A) (hcongr : A.map π = 1) : A = 1 := by
  by_contra hA
  have hord : orderOf A ≠ 1 := mt orderOf_eq_one_iff.mp hA
  obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hord
  let B := A ^ (orderOf A / q)
  have hBord : orderOf B = q :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt hfinite.orderOf_pos) hqdiv
  have hBpow : B ^ q = 1 := hBord ▸ pow_orderOf_eq_one B
  have hBcongr : B.map π = 1 := by
    change π.mapMatrix (A ^ (orderOf A / q)) = 1
    rw [map_pow]
    change (A.map π) ^ (orderOf A / q) = 1
    rw [hcongr, one_pow]
  have hB := congruence_matrix_prime_order_eq_one π hker q hq B hBpow hBcongr
  rw [hB, orderOf_one] at hBord
  exact hq.ne_one hBord.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
