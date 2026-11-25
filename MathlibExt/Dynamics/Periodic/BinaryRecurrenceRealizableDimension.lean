/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! # Binary recurrence realizable subspace

The discriminant determines the dimension of the complex span of realizable solutions of a
nondegenerate integer binary recurrence.
-/

open Function
open scoped Matrix ComplexConjugate

namespace MetaMathlibExt.binaryrec_realizable_subspace_dim

private def Rec {K : Type*} [Ring K] (B C : K) (u : ℕ → K) : Prop :=
  ∀ n : ℕ, u (n + 2) = B * u (n + 1) - C * u n

private def Realizable (u : ℕ → ℤ) : Prop :=
  ∃ (X : Type) (T : X → X),
    ∀ n : ℕ, ∃ S : Set X, S = {x | T^[n + 1] x = x} ∧ S.Finite ∧
      S.ncard = (u n).natAbs

private theorem rec_unique {K : Type*} [Ring K] {B C : K} {u v : ℕ → K}
    (hu : Rec B C u) (hv : Rec B C v) (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n h₀ h₁ => rw [hu, hv, h₀, h₁]

/-! ## Fixed-point counts and the recurrence modulo a prime -/

private theorem realizable_modEq {u : ℕ → ℤ} (hu : Realizable u)
    {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (u (m * p ^ k - 1)).natAbs ≡ (u (m - 1)).natAbs [MOD p] := by
  classical
  obtain ⟨X, T, hT⟩ := hu
  have hmp : 0 < m * p ^ k := Nat.mul_pos hm (pow_pos (Fact.out : p.Prime).pos _)
  obtain ⟨S, rfl, hS, hcard⟩ := hT (m * p ^ k - 1)
  obtain ⟨U, rfl, hU, hcard'⟩ := hT (m - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m * p ^ k)] at hS hcard
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hU hcard'
  let Y := {x : X // T^[m * p ^ k] x = x}
  let f : Y → Y := fun x => ⟨T^[m] x, by
    rw [← iterate_add_apply, add_comm, iterate_add_apply, x.property]⟩
  have hf (n : ℕ) (x : Y) : (f^[n] x : X) = T^[m * n] x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', Nat.mul_succ, add_comm, iterate_add_apply]
      change T^[m] (f^[n] x : X) = _
      rw [ih]
  have hfp : f^[p ^ k] = id := by
    funext x
    exact Subtype.ext ((hf _ x).trans x.property)
  let _ : Fintype Y := hS.fintype
  let _ : Fintype {x : X // T^[m] x = x} := hU.fintype
  let e : {x : Y // f x = x} ≃ {x : X // T^[m] x = x} := {
    toFun x := ⟨x.1.1, congrArg Subtype.val x.property⟩
    invFun x := ⟨⟨x.1, by
      rw [iterate_mul]
      exact (IsFixedPt.iterate x.property (p ^ k))⟩, Subtype.ext x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have h := Equiv.Perm.card_fixedPoints_modEq hfp
  rw [← hcard, ← hcard', ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card Y ≡ Nat.card {x : X // T^[m] x = x} [MOD p]
  rw [← Nat.card_congr e]
  change Nat.card Y ≡ Nat.card f.fixedPoints [MOD p]
  simpa only [Nat.card_eq_fintype_card] using h

private def disc {K : Type*} [Ring K] (B C : K) : K := B ^ 2 - 4 * C

private theorem rec_pow {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    {B C : K} {r : A}
    (hr : r ^ 2 = algebraMap K A B * r - algebraMap K A C) (L : A →ₗ[K] K) :
    Rec B C (fun n => L (r ^ (n + 1))) := by
  intro n
  change L (r ^ (n + 2 + 1)) = B * L (r ^ (n + 1 + 1)) - C * L (r ^ (n + 1))
  rw [show n + 2 + 1 = 2 + (n + 1) by omega, pow_add, hr, sub_mul, mul_assoc, ← pow_succ',
    map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]
  rfl

private theorem quad_eval {K : Type*} [CommRing K] {B C : K} {u : ℕ → K}
    (hu : Rec B C u) (n : ℕ) :
    let x : QuadraticAlgebra K (-C) B := QuadraticAlgebra.omega
    (B * u 0 - u 1) * (x ^ (n + 1)).re + C * u 0 * (x ^ (n + 1)).im = C * u n := by
  dsimp only
  let x : QuadraticAlgebra K (-C) B := QuadraticAlgebra.omega
  let L : QuadraticAlgebra K (-C) B →ₗ[K] K :=
    (B * u 0 - u 1) • (QuadraticAlgebra.reₗ (-C) B) + (C * u 0) • (QuadraticAlgebra.imₗ (-C) B)
  change L (x ^ (n + 1)) = C * u n
  have hx : x ^ 2 = algebraMap K _ B * x - algebraMap K _ C := by
    ext <;> simp [x, pow_two]
  have huv : Rec B C (fun n => C * u n) := by
    intro k
    simp only [hu k]
    ring
  have he := rec_unique (rec_pow hx L) huv (by simp [L, x])
    (by simp [L, hx, x]; ring)
  exact congrFun he n

private theorem omega_frobenius {p : ℕ} [Fact p.Prime] (hp : 2 < p) (B C : ZMod p) :
    let x : QuadraticAlgebra (ZMod p) (-C) B := QuadraticAlgebra.omega
    let e := disc B C ^ (p / 2)
    (x ^ p).re = (1 - e) * B / 2 ∧ (x ^ p).im = e := by
  dsimp
  let K := ZMod p
  let A := QuadraticAlgebra K (-C) B
  let _ : ExpChar A p := expChar_of_injective_ringHom (algebraMap K A).injective p
  let x : A := QuadraticAlgebra.omega
  let y : A := algebraMap K A 2 * x - algebraMap K A B
  have hy : y ^ 2 = algebraMap K A (disc B C) := by
    ext <;> simp [y, x, A, K, disc, pow_two] <;> ring
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have hpow : y ^ p = algebraMap K A (disc B C ^ (p / 2)) * y := by
    calc
      y ^ p = y ^ (2 * (p / 2) + 1) := congrArg (y ^ ·) (by omega)
      _ = _ := by rw [pow_succ, pow_mul, hy, map_pow]
  have hsc (t : K) : (algebraMap K A t) ^ p = algebraMap K A t := by
    rw [← map_pow, ZMod.pow_card]
  have h := hpow
  conv_lhs at h => rw [show y = algebraMap K A 2 * x - algebraMap K A B by rfl,
    sub_pow_expChar, mul_pow, hsc, hsc]
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  dsimp only [y, x, A, K] at hre him
  simp [-map_pow] at hre him
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hv := ZMod.val_natCast_of_lt hp
    intro he
    simp [he] at hv
  constructor
  · apply (eq_div_iff h2).mpr
    linear_combination hre
  · exact mul_left_cancel₀ h2 (him.trans (mul_comm _ _))

private theorem intCast_ne_zero {z : ℤ} (hz : z ≠ 0) {p : ℕ} (hp : z.natAbs < p) :
    (z : ZMod p) ≠ 0 := by
  intro h
  have hd := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h)
  exact (not_le_of_gt hp) (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hd)

private theorem eq_zero_of_large_mod {z : ℤ}
    (h : ∃ p : ℕ, z.natAbs < p ∧ (z : ZMod p) = 0) : z = 0 := by
  obtain ⟨p, hp, h⟩ := h
  by_contra hz
  exact intCast_ne_zero hz hp h

private theorem recurrence_cast {u : ℕ → ℤ} {B C : ℤ}
    (h : Rec B C u) (p : ℕ) : Rec (B : ZMod p) (C : ZMod p) (fun n => (u n : ZMod p)) := by
  intro n
  simpa only [Int.cast_sub, Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod p)) (h n)

private theorem realizable_sq {u : ℕ → ℤ} (hu : Realizable u)
    {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (u (m * p ^ k - 1) : ZMod p) ^ 2 = (u (m - 1) : ZMod p) ^ 2 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (realizable_modEq hu (p := p) hm k)
  have hsq (z : ℤ) : (z : ZMod p) ^ 2 = (z.natAbs : ZMod p) ^ 2 := by
    rcases Int.natAbs_eq z with hz | hz <;> rw [hz] <;> simp
  rw [hsq, hsq, h]

private theorem exists_jacobi_factor {d : ℤ} {a : ℕ} (h : jacobiSym d a = -1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ jacobiSym d p = -1 := by
  classical
  by_contra! H
  rw [jacobiSym] at h
  have hge : 0 ≤ (a.primeFactorsList.pmap (fun p hp => @legendreSym p ⟨hp⟩ d)
      (fun _ hp => Nat.prime_of_mem_primeFactorsList hp)).prod := by
    apply List.prod_nonneg
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp he
    let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactorsList hp⟩
    rw [jacobiSym.legendreSym.to_jacobiSym]
    rcases jacobiSym.trichotomy d p with h | h | h
    · rw [h]
    · rw [h]; decide
    · exact (H _ Fact.out (Nat.dvd_of_mem_primeFactorsList hp) h).elim
  omega

/-! ## Nonresidue primes for a nonsquare discriminant -/

private theorem jacobi_left_congr {a b d : ℕ} (h : a ≡ b [MOD d]) :
    jacobiSym a d = jacobiSym b d :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)

private theorem jacobi_right_congr {a b d : ℕ} (ha : Odd a) (hb : Odd b)
    (h : a ≡ b [MOD 4 * d]) : jacobiSym d a = jacobiSym d b := by
  rw [jacobiSym.mod_right' d ha, jacobiSym.mod_right' d hb, h]

private theorem exists_large_nonsquare_prime {d : ℕ} (hd : ¬ IsSquare d) (N : ℕ) :
    ∃ p > N, ∃ _ : p.Prime, ¬ IsSquare (d : ZMod p) := by
  classical
  have hd0 : d ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  rw [Nat.isSquare_iff_even_factorization] at hd
  push Not at hd
  obtain ⟨q, hq, he⟩ := hd
  let _ : Fact q.Prime := ⟨hq⟩
  let e := d.factorization q
  let d' := ordCompl[q] d
  let n' := ordCompl[q] N.factorial
  have heo : Odd e := he
  have hdc : q.Coprime d' := Nat.coprime_ordCompl hq hd0
  have hnc : q.Coprime n' := Nat.coprime_ordCompl hq N.factorial_ne_zero
  have hdecomp : q ^ e * d' = d := Nat.ordProj_mul_ordCompl_eq_self d q
  have hndecomp : q ^ N.factorial.factorization q * n' = N.factorial :=
    Nat.ordProj_mul_ordCompl_eq_self N.factorial q
  have hextract (a : ℕ) (ha : Odd a) (hac : a ≡ 1 [MOD n'])
      (hqca : ¬q ∣ a) (hJ : jacobiSym d a = -1) :
      ∃ p > N, ∃ _ : p.Prime, ¬ IsSquare (d : ZMod p) := by
    obtain ⟨p, hp, hpa, hpJ⟩ := exists_jacobi_factor hJ
    let _ : Fact p.Prime := ⟨hp⟩
    refine ⟨p, ?_, hp, ?_⟩
    · by_contra! hple
      have hpd : p ∣ N.factorial := hp.dvd_factorial.mpr hple
      rw [← hndecomp, hp.dvd_mul] at hpd
      rcases hpd with hpd | hpd
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
        exact hqca hpa
      · have hmod := hac.of_dvd hpd
        have hzero := Nat.modEq_zero_iff_dvd.mpr hpa
        have hbad := hmod.symm.trans hzero
        exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp hbad)
    · simpa using (ZMod.nonsquare_of_jacobiSym_eq_neg_one hpJ)
  have hJ_formula (a : ℕ) :
      jacobiSym d a = jacobiSym q a ^ e * jacobiSym d' a := by
    rw [← hdecomp]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left]
  rcases eq_or_ne q 2 with rfl | hq2
  · have hcop : Nat.Coprime 8 (d' * n') := by
      rw [show 8 = 2 ^ 3 by decide]
      exact (hdc.mul_right hnc).pow_left _
    obtain ⟨a, ha8, haodd⟩ := Nat.chineseRemainder hcop 5 1
    have ham : a % 8 = 5 := ha8
    have hao : Odd a := Nat.odd_iff.mpr (by omega)
    have hdo : Odd d' := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      ((Nat.prime_two.coprime_iff_not_dvd).mp hdc))
    refine hextract a hao (haodd.of_dvd (dvd_mul_left n' d'))
      (fun h => by obtain ⟨k, hk⟩ := h; omega) ?_
    rw [hJ_formula, Nat.cast_two, jacobiSym.at_two hao, ZMod.χ₈_nat_eq_if_mod_eight, ham]
    have hJd : jacobiSym d' a = 1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hdo (by omega : a % 4 = 1),
        jacobi_left_congr (haodd.of_dvd (dvd_mul_right d' n'))]
      simp
    simp [hJd, heo.neg_one_pow, Nat.odd_iff.mp hao]
  · have hcop : q.Coprime (8 * d' * n') := by
      apply Nat.Coprime.mul_right _ hnc
      apply Nat.Coprime.mul_right _ hdc
      rw [show 8 = 2 ^ 3 by decide]
      exact ((Nat.coprime_primes hq Nat.prime_two).mpr hq2).pow_right _
    obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare ((ZMod.ringChar_zmod_n q).trans_ne hq2)
    obtain ⟨a, haq, ham⟩ := Nat.chineseRemainder hcop b.val 1
    have ha8 : a % 8 = 1 := ham.of_dvd (dvd_mul_of_dvd_left (dvd_mul_right 8 d') n')
    have hao : Odd a := Nat.odd_iff.mpr (by omega)
    have hbo : b ≠ 0 := by rintro rfl; exact hb ⟨0, by simp⟩
    have haq0 : ¬q ∣ a := by
      rw [← Nat.modEq_zero_iff_dvd]
      intro h
      have h' := haq.symm.trans h
      have hb' : b.val % q = b.val := Nat.mod_eq_of_lt (ZMod.val_lt b)
      change b.val % q = 0 % q at h'
      rw [hb', Nat.zero_mod] at h'
      exact hbo (by simpa using congrArg (fun n : ℕ => (n : ZMod q)) h')
    refine hextract a hao (ham.of_dvd (dvd_mul_left n' (8 * d'))) haq0 ?_
    have hJq : jacobiSym q a = -1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' (hq.odd_of_ne_two hq2)
        (by omega : a % 4 = 1), jacobi_left_congr haq]
      apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hb
    have hJd : jacobiSym d' a = 1 := by
      rw [jacobi_right_congr hao odd_one (b := 1), jacobiSym.one_right]
      apply ham.of_dvd
      exact (show 4 * d' ∣ 8 * d' by use 2; ring).trans (dvd_mul_right _ _)
    rw [hJ_formula, hJq, heo.neg_one_pow, hJd, mul_one]

/-! ## Initial-value constraints in the real-root cases -/

private theorem nonsquare_pow_half {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {d : ZMod p} (hd : ¬ IsSquare d) : d ^ (p / 2) = -1 := by
  have hn : d ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  have hodd := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have hs : (d ^ (p / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show p / 2 * 2 = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hn]
  have hne : d ^ (p / 2) ≠ 1 := fun h => hd ((ZMod.euler_criterion p hn).mpr h)
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans (one_pow 2).symm)).resolve_left hne

private theorem recurrence_mod_inert {B C : ℤ} {u : ℕ → ℤ} (hu : Rec B C u)
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) (hd : ¬ IsSquare (disc (B : ZMod p) (C : ZMod p))) :
    (C : ZMod p) * (u (p - 1) : ZMod p) =
      (B : ZMod p) * ((B : ZMod p) * (u 0 : ZMod p) - (u 1 : ZMod p)) -
        (C : ZMod p) * (u 0 : ZMod p) := by
  have h := quad_eval (recurrence_cast hu p) (p - 1)
  have ⟨hr, hi⟩ := omega_frobenius hp (B : ZMod p) (C : ZMod p)
  dsimp only at h hr hi
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p), hr, hi, nonsquare_pow_half hp hd] at h
  have hb : (1 - (-1 : ZMod p)) * (B : ZMod p) / 2 = B := by
    have h2 := intCast_ne_zero (z := 2) (by decide) hp
    push_cast at h2
    field_simp
    ring
  rw [hb] at h
  linear_combination -h

private theorem repeated_initial {B C : ℤ} {u : ℕ → ℤ} (hC : C ≠ 0)
    (hd : disc B C = 0) (hu : Rec B C u) (hreal : Realizable u) :
    2 * u 1 = B * u 0 := by
  have hD : B ^ 2 = 4 * C := sub_eq_zero.mp hd
  have hB : B ≠ 0 := by rintro rfl; norm_num at hD; omega
  let t := B * u 0 - u 1
  let z := (2 * C * u 0) ^ 2 - (B * t) ^ 2
  let w := (4 * C * u 1) ^ 2 - (B ^ 2 * t) ^ 2
  obtain ⟨p, hpg, hpP⟩ := Nat.exists_infinite_primes (max (max z.natAbs w.natAbs) 2 + 1)
  have hp : 2 < p := by omega
  let _ : Fact p.Prime := ⟨hpP⟩
  let b : ZMod p := B
  let c : ZMod p := C
  let x : QuadraticAlgebra (ZMod p) (-c) b := QuadraticAlgebra.omega
  have hdmod : disc b c = 0 := by
    change (B : ZMod p) ^ 2 - 4 * (C : ZMod p) = 0
    simpa [disc] using congrArg (fun z : ℤ => (z : ZMod p)) hd
  have h2 := intCast_ne_zero (z := 2) (by decide) hp
  push_cast at h2
  have hx : x ^ p = algebraMap (ZMod p) _ (b / 2) := by
    have ⟨hr, hi⟩ := omega_frobenius hp b c
    have he : p / 2 ≠ 0 := by omega
    rw [hdmod, zero_pow he] at hr hi
    ext
    · simpa [x] using hr
    · simpa [x] using hi
  have hxp : x ^ (2 * p) = algebraMap (ZMod p) _ ((b / 2) ^ 2) := by
    rw [mul_comm, pow_mul, hx, map_pow]
  have hm (m : ℕ) (hm : 0 < m) (ha : x ^ (m * p) = algebraMap (ZMod p) _ ((b / 2) ^ m)) :
      (c * (u (m * p - 1) : ZMod p)) = (t : ZMod p) * (b / 2) ^ m := by
    have h := quad_eval (recurrence_cast hu p) (m * p - 1)
    have hmp := Nat.mul_pos hm hpP.pos
    dsimp only at h
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m * p)] at h
    change ((b * (u 0 : ZMod p) - (u 1 : ZMod p)) * (x ^ (m * p)).re +
      c * (u 0 : ZMod p) * (x ^ (m * p)).im = c * (u (m * p - 1) : ZMod p)) at h
    rw [ha] at h
    simpa [t, b, ← map_pow] using h.symm
  have h₀ := hm 1 (by decide) (by simpa using hx)
  have h₁ := hm 2 (by decide) hxp
  have hq₀ := realizable_sq hreal (p := p) (m := 1) (by decide) 1
  have hq₁ := realizable_sq hreal (p := p) (m := 2) (by decide) 1
  simp only [one_mul, pow_one, Nat.reduceSub] at h₀ hq₀ hq₁
  have hz : z = 0 := by
    apply eq_zero_of_large_mod
    refine ⟨p, by omega, ?_⟩
    push_cast [z]
    change (2 * c * (u 0 : ZMod p)) ^ 2 - (b * (t : ZMod p)) ^ 2 = 0
    have hmul : 2 * c * (u (p - 1) : ZMod p) = b * (t : ZMod p) := by
      field_simp at h₀
      linear_combination h₀
    rw [← hmul, show (2 * c * (u (p - 1) : ZMod p)) ^ 2 =
        (2 * c) ^ 2 * (u 0 : ZMod p) ^ 2 from by rw [mul_pow, hq₀], mul_pow, sub_self]
  have hw : w = 0 := by
    apply eq_zero_of_large_mod
    refine ⟨p, by omega, ?_⟩
    push_cast [w]
    change (4 * c * (u 1 : ZMod p)) ^ 2 - (b ^ 2 * (t : ZMod p)) ^ 2 = 0
    have hmul : 4 * c * (u (2 * p - 1) : ZMod p) = b ^ 2 * (t : ZMod p) := by
      field_simp at h₁
      linear_combination h₁
    rw [← hmul, show (4 * c * (u (2 * p - 1) : ZMod p)) ^ 2 =
        (4 * c) ^ 2 * (u 1 : ZMod p) ^ 2 from by rw [mul_pow, hq₁], mul_pow, sub_self]
  have h0' : 2 * C * u 0 = B * t ∨ 2 * C * u 0 = -(B * t) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hz)
  have h1' : 4 * C * u 1 = B ^ 2 * t ∨ 4 * C * u 1 = -(B ^ 2 * t) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hw)
  have ht₀ : B * u 0 = 2 * t ∨ B * u 0 = -(2 * t) := by
    rcases h0' with he | he
    · left
      apply mul_left_cancel₀ hB
      linear_combination 2 * he + u 0 * hD
    · right
      apply mul_left_cancel₀ hB
      linear_combination 2 * he + u 0 * hD
  have ht₁ : u 1 = t ∨ u 1 = -t := by
    have hn : B ^ 2 ≠ 0 := pow_ne_zero _ hB
    rcases h1' with he | he
    · left
      apply mul_left_cancel₀ hn
      linear_combination he + u 1 * hD
    · right
      apply mul_left_cancel₀ hn
      linear_combination he + u 1 * hD
  have ht : t = B * u 0 - u 1 := rfl
  rcases ht₀ with h | h <;> rcases ht₁ with h' | h' <;> omega

private theorem rec_real_cast {u : ℕ → ℤ} {B C : ℤ} (h : Rec B C u) :
    Rec (B : ℝ) (C : ℝ) (fun n => (u n : ℝ)) := by
  intro n
  dsimp
  exact_mod_cast h n

private theorem rec_linearCombination {K : Type*} [CommRing K] {B C : K} {u v : ℕ → K}
    (hu : Rec B C u) (hv : Rec B C v) (a b : K) :
    Rec B C (fun n => a * u n + b * v n) := by
  intro n
  dsimp
  rw [hu, hv]
  ring

private theorem rec_geometric {K : Type*} [CommRing K] {B C r : K}
    (h : r ^ 2 - B * r + C = 0) : Rec B C (fun n => r ^ (n + 1)) := by
  intro n
  change r ^ (n + 2 + 1) = B * r ^ (n + 1 + 1) - C * r ^ (n + 1)
  rw [show n + 2 + 1 = 2 + (n + 1) by omega, pow_add, pow_succ]
  linear_combination r ^ (n + 1) * h

private theorem roots_real {B C : ℤ} (hD : 0 < disc B C) :
    ∃ r s : ℝ, s < r ∧ r + s = B ∧ r * s = C := by
  have hd : (0 : ℝ) < (B : ℝ) ^ 2 - 4 * (C : ℝ) := by exact_mod_cast hD
  let q := Real.sqrt ((B : ℝ) ^ 2 - 4 * (C : ℝ))
  have hq : 0 < q := Real.sqrt_pos_of_pos hd
  have hq2 : q ^ 2 = (B : ℝ) ^ 2 - 4 * (C : ℝ) := Real.sq_sqrt hd.le
  refine ⟨(B + q) / 2, (B - q) / 2, by linarith, by ring, ?_⟩
  nlinarith

private theorem root_sq_sub {K : Type*} [CommRing K] {B C r s : K}
    (hB : r + s = B) (hC : r * s = C) :
    r ^ 2 - B * r + C = 0 ∧ s ^ 2 - B * s + C = 0 := by
  rw [← hB, ← hC]
  constructor <;> ring

private theorem nondeg_real_B_ne_zero {B C : ℤ} (hC : C ≠ 0)
    (hD : 0 < disc B C)
    (hNondeg : ∀ α β : ℂ, α ^ 2 - (B : ℂ) * α + (C : ℂ) = 0 →
      β ^ 2 - (B : ℂ) * β + (C : ℂ) = 0 → α ≠ β →
      ∀ n : ℕ, 0 < n → (α / β) ^ n ≠ 1) : B ≠ 0 := by
  obtain ⟨r, s, hrs, hsum, hprod⟩ := roots_real hD
  have ⟨hr, hs⟩ := root_sq_sub hsum hprod
  intro hz
  have hre : (r : ℂ) ^ 2 - (B : ℂ) * (r : ℂ) + (C : ℂ) = 0 := by exact_mod_cast hr
  have hse : (s : ℂ) ^ 2 - (B : ℂ) * (s : ℂ) + (C : ℂ) = 0 := by exact_mod_cast hs
  have hne : (r : ℂ) ≠ (s : ℂ) := by exact_mod_cast hrs.ne'
  have hsn : (s : ℂ) ≠ 0 := by
    have hsn : s ≠ 0 := by
      intro hz'
      rw [hz', mul_zero, eq_comm] at hprod
      exact hC (by exact_mod_cast hprod)
    exact_mod_cast hsn
  apply hNondeg _ _ hre hse hne 2 (by decide)
  have hneg : r = -s := by simp [hz] at hsum; linarith
  rw [hneg, Complex.ofReal_neg, neg_div, div_self hsn]
  norm_num

private theorem nonsquare_initial {B C : ℤ} {u : ℕ → ℤ} (hC : C ≠ 0)
    (hD : 0 < disc B C) (hDs : ¬ IsSquare (disc B C))
    (hNondeg : ∀ α β : ℂ, α ^ 2 - (B : ℂ) * α + (C : ℂ) = 0 →
      β ^ 2 - (B : ℂ) * β + (C : ℂ) = 0 → α ≠ β →
      ∀ n : ℕ, 0 < n → (α / β) ^ n ≠ 1)
    (hu : Rec B C u) (hReal : Realizable u) :
    B * u 1 = (B ^ 2 - 2 * C) * u 0 := by
  obtain ⟨r, s, hrs, hsum, hprod⟩ := roots_real hD
  have ⟨hr, hs⟩ := root_sq_sub hsum hprod
  have hB := nondeg_real_B_ne_zero hC hD hNondeg
  let t := B * u 0 - u 1
  let z := (B * t - C * u 0) ^ 2 - (C * u 0) ^ 2
  let w := 2 * C * u 0
  let M := max (max z.natAbs w.natAbs) 2
  have hdabs : ((disc B C).natAbs : ℤ) = disc B C := Int.natAbs_of_nonneg hD.le
  have hds : ¬ IsSquare (disc B C).natAbs := by
    intro h
    exact hDs (hdabs ▸ h.map (Nat.castRingHom ℤ))
  obtain ⟨p, hpg, hpP, hns⟩ := exists_large_nonsquare_prime hds M
  have hp : 2 < p := by dsimp [M] at hpg; omega
  let _ : Fact p.Prime := ⟨hpP⟩
  have hns' : ¬ IsSquare (disc (B : ZMod p) (C : ZMod p)) := by
    have hcast : ((disc B C).natAbs : ZMod p) = disc (B : ZMod p) (C : ZMod p) := by
      simpa only [Int.cast_natCast, disc, Int.cast_sub, Int.cast_mul, Int.cast_pow,
        Int.cast_ofNat] using congrArg (fun a : ℤ => (a : ZMod p)) hdabs
    rwa [← hcast]
  have hm := recurrence_mod_inert hu hp hns'
  have hq := realizable_sq hReal (p := p) (m := 1) (by decide) 1
  simp only [one_mul, pow_one, Nat.reduceSub] at hq
  have hz : z = 0 := by
    apply eq_zero_of_large_mod
    refine ⟨p, by dsimp [M] at hpg; omega, ?_⟩
    push_cast [z, t]
    rw [← hm, mul_pow, mul_pow, hq, sub_self]
  have hh : B * t * (B * t - 2 * C * u 0) = 0 := by
    dsimp [z] at hz
    linear_combination hz
  rcases mul_eq_zero.mp hh with ht | h
  · have ht : t = 0 := (mul_eq_zero.mp ht).resolve_left hB
    have h1 : u 1 = B * u 0 := by dsimp [t] at ht; omega
    have hform : ∀ n : ℕ, (u n : ℝ) =
        (u 0 : ℝ) / (r - s) * (r ^ (n + 1) - s ^ (n + 1)) := by
      let a := (u 0 : ℝ) / (r - s)
      have hrec' : Rec (B : ℝ) (C : ℝ) (fun n => a * r ^ (n + 1) + (-a) * s ^ (n + 1)) :=
        rec_linearCombination (rec_geometric hr) (rec_geometric hs) a (-a)
      have hrsub : r - s ≠ 0 := sub_ne_zero.mpr hrs.ne'
      have heq := rec_unique (rec_real_cast hu) hrec'
        (by simp [a]; field_simp; ring)
        (by
          have h1r : (u 1 : ℝ) = (B : ℝ) * (u 0 : ℝ) := by exact_mod_cast h1
          rw [h1r, ← hsum]
          dsimp [a]
          field_simp
          ring)
      intro n
      rw [congrFun heq n]
      dsimp [a]
      ring
    have hpodd : Odd p := hpP.odd_of_ne_two (by omega)
    have hf : 0 < r ^ p - s ^ p := sub_pos.mpr (hpodd.pow_lt_pow.mpr hrs)
    have hopp {v : ℤ} (h : u (p - 1) = v) :
        (0 ≤ v ∧ 0 ≤ u 0) ∨ (v ≤ 0 ∧ u 0 ≤ 0) := by
      have hh' := hform (p - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p), h] at hh'
      rcases le_total (0 : ℤ) (u 0) with h0 | h0
      · left
        refine ⟨?_, h0⟩
        have hp0 : (0 : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast h0
        exact_mod_cast (hh' ▸ mul_nonneg (div_nonneg hp0 (sub_pos.mpr hrs).le) hf.le)
      · right
        refine ⟨?_, h0⟩
        have hp0 : (u 0 : ℝ) ≤ 0 := by exact_mod_cast h0
        exact_mod_cast (hh' ▸ mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg hp0 (sub_pos.mpr hrs).le) hf.le)
    have habs := realizable_modEq hReal (p := p) (m := 1) (by decide) 1
    simp only [one_mul, pow_one, Nat.reduceSub] at habs
    have he : (u (p - 1) : ZMod p) = (u 0 : ZMod p) := by
      have he' := (ZMod.natCast_eq_natCast_iff _ _ _).mpr habs
      have hi : (((u (p - 1)).natAbs : ℤ) : ZMod p) = (((u 0).natAbs : ℤ) : ZMod p) := by
        simpa only [Int.cast_natCast] using he'
      rcases hopp rfl with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · rwa [Int.natAbs_of_nonneg h₀, Int.natAbs_of_nonneg h₁] at hi
      · rw [Int.ofNat_natAbs_of_nonpos h₀, Int.ofNat_natAbs_of_nonpos h₁, Int.cast_neg,
          Int.cast_neg] at hi
        exact neg_injective hi
    have hcast0 : (t : ZMod p) = 0 := by rw [ht, Int.cast_zero]
    push_cast [t] at hcast0
    rw [he, hcast0] at hm
    have hw : w = 0 := by
      apply eq_zero_of_large_mod
      refine ⟨p, by dsimp [M] at hpg; omega, ?_⟩
      push_cast [w]
      linear_combination hm
    have hu0 : u 0 = 0 := (mul_eq_zero.mp hw).resolve_left (mul_ne_zero (by decide) hC)
    simp [hu0, h1]
  · dsimp [t] at h
    linear_combination -h

/-! ## The obstruction for nonreal roots -/

private theorem omega_pow_prime_sq {p : ℕ} [Fact p.Prime] (hp : 2 < p) (b c : ZMod p)
    (hd : disc b c ≠ 0) :
    (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (-c) b) ^ (p ^ 2) =
      QuadraticAlgebra.omega := by
  let K := ZMod p
  let A := QuadraticAlgebra K (-c) b
  let _ : ExpChar A p := expChar_of_injective_ringHom (algebraMap K A).injective p
  let x : A := QuadraticAlgebra.omega
  change x ^ (p ^ 2) = x
  have hodd := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have hs : (disc b c ^ (p / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show p / 2 * 2 = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hd]
  have ⟨hr, hi⟩ := omega_frobenius hp b c
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans (one_pow 2).symm) with h | h
  · have hx : x ^ p = x := by
      rw [h] at hr hi
      ext
      · simpa [x] using hr
      · simpa [x] using hi
    rw [pow_two, pow_mul, hx, hx]
  · have h2 := intCast_ne_zero (z := 2) (by decide) hp
    push_cast at h2
    have hb : (1 - (-1 : ZMod p)) * b / 2 = b := by field_simp; ring
    have hx : x ^ p = algebraMap K A b - x := by
      rw [h, hb] at hr
      rw [h] at hi
      ext
      · simpa [x, A, K] using hr
      · simpa [x, A, K] using hi
    calc
      x ^ (p ^ 2) = (x ^ p) ^ p := by rw [pow_two, pow_mul]
      _ = algebraMap K A b - x ^ p := by
        conv_lhs => rw [hx, sub_pow_expChar, ← map_pow, ZMod.pow_card]
      _ = x := by rw [hx]; ring

private theorem omega_isUnit {p : ℕ} [Fact p.Prime] (b c : ZMod p) (hc : c ≠ 0) :
    IsUnit (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (-c) b) := by
  let x : QuadraticAlgebra (ZMod p) (-c) b := QuadraticAlgebra.omega
  have he : x * (algebraMap (ZMod p) _ b - x) = algebraMap (ZMod p) _ c := by
    ext <;> simp [x, mul_sub]
  exact isUnit_of_mul_isUnit_left (he.symm ▸ (isUnit_iff_ne_zero.mpr hc).map
    (algebraMap (ZMod p) _))

private theorem exists_mod_period {p : ℕ} [Fact p.Prime] {B C : ℤ} {u : ℕ → ℤ}
    (hu : Rec B C u) (hc : (C : ZMod p) ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ Function.Periodic (fun n => (u n : ZMod p)) d := by
  let A := QuadraticAlgebra (ZMod p) (-(C : ZMod p)) (B : ZMod p)
  let _ : Finite A :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (-(C : ZMod p)) (B : ZMod p)).symm
  let x : A := QuadraticAlgebra.omega
  obtain ⟨v, hv⟩ := omega_isUnit (B : ZMod p) (C : ZMod p) hc
  let d := orderOf v
  have hd : 0 < d := orderOf_pos v
  have hx : x ^ d = 1 := by
    change (QuadraticAlgebra.omega : A) ^ d = 1
    rw [← hv, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  refine ⟨d, hd, ?_⟩
  intro n
  have h := quad_eval (recurrence_cast hu p) n
  have h' := quad_eval (recurrence_cast hu p) (n + d)
  dsimp only at h h'
  rw [show n + d + 1 = d + (n + 1) by omega, pow_add, show
    (QuadraticAlgebra.omega : A) ^ d = 1 from hx, one_mul, h] at h'
  exact mul_left_cancel₀ hc h'.symm

private theorem mod_prime_sq {p : ℕ} [Fact p.Prime] (hp : 2 < p) {B C : ℤ} {u : ℕ → ℤ}
    (hu : Rec B C u) (hc : (C : ZMod p) ≠ 0)
    (hd : disc (B : ZMod p) (C : ZMod p) ≠ 0) {m : ℕ} (hm : 0 < m) :
    (u (m * p ^ 2 - 1) : ZMod p) = (u (m - 1) : ZMod p) := by
  have h := quad_eval (recurrence_cast hu p) (m - 1)
  have h' := quad_eval (recurrence_cast hu p) (m * p ^ 2 - 1)
  have hmp := Nat.mul_pos hm (pow_pos (Fact.out : p.Prime).pos 2)
  dsimp only at h h'
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m * p ^ 2), mul_comm m, pow_mul,
    omega_pow_prime_sq hp _ _ hd, h] at h'
  simpa only [mul_comm (p ^ 2) m] using mul_left_cancel₀ hc h'.symm

private theorem circle_dense_powers {z : Circle} (hz : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) :
    DenseRange (z ^ · : ℕ → Circle) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let e := AddCircle.homeomorphCircle (T := 1) one_ne_zero
  let a := e.symm z
  have hea : AddCircle.toCircle a = z := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply z
  have ha : addOrderOf a = 0 := by
    by_contra h
    have he : addOrderOf a • a = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp dvd_rfl
    have he' := congrArg AddCircle.toCircle he
    rw [AddCircle.toCircle_nsmul, hea, AddCircle.toCircle_zero] at he'
    exact hz _ (Nat.pos_of_ne_zero h) he'
  have hd := e.surjective.denseRange.comp (AddCircle.denseRange_zsmul_iff.mpr ha) e.continuous
  apply denseRange_zpow_iff_pow.mp
  convert hd using 1
  funext n
  change z ^ n = AddCircle.homeomorphCircle one_ne_zero (n • a)
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zsmul, hea]

private theorem circle_align (a : ℂ) :
    a * (Circle.exp (-a.arg) : ℂ) = (‖a‖ : ℂ) := by
  let c := Circle.exp a.arg
  have ha : a = (‖a‖ : ℂ) * (c : ℂ) := (Complex.norm_mul_exp_arg_mul_I a).symm
  rw [Circle.exp_neg]
  change a * ((c⁻¹ : Circle) : ℂ) = _
  calc
    a * ((c⁻¹ : Circle) : ℂ) = (‖a‖ : ℂ) * (c : ℂ) * ((c⁻¹ : Circle) : ℂ) := by
      exact congrArg (· * ((c⁻¹ : Circle) : ℂ)) ha
    _ = _ := by rw [mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, mul_one]

private theorem circle_opposite {a : ℂ} (ha : a ≠ 0) {q : ℕ} (hq : 2 < q) :
    ∃ z : Circle, 0 < (a * (z : ℂ)).re ∧ (a * ((z ^ q : Circle) : ℂ)).re < 0 := by
  let c := Circle.exp (-a.arg)
  have hc : a * (c : ℂ) = (‖a‖ : ℂ) := circle_align a
  obtain ⟨t, ht, he⟩ := Circle.surjOn_exp_neg_pi_pi (Set.mem_univ ((c ^ q)⁻¹ * (-c)))
  let z := c * Circle.exp (t / q)
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hz : z ^ q = -c := by
    change (c * Circle.exp (t / q)) ^ q = -c
    rw [mul_pow, ← Circle.exp_nsmul (t / q), nsmul_eq_mul]
    have h : (q : ℝ) * (t / q) = t := by field_simp
    rw [h, he, mul_inv_cancel_left]
  refine ⟨z, ?_, ?_⟩
  · change 0 < (a * ((c * Circle.exp (t / q) : Circle) : ℂ)).re
    rw [Circle.coe_mul, ← mul_assoc, hc, Complex.re_ofReal_mul, Circle.coe_exp,
      Complex.exp_mul_I]
    simp only [Complex.add_re, ← Complex.ofReal_cos, Complex.ofReal_re, Complex.mul_I_re,
      ← Complex.ofReal_sin, Complex.ofReal_im, neg_zero, add_zero]
    have htq : -(Real.pi / 2) < t / q ∧ t / q < Real.pi / 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < q), div_lt_iff₀ (by positivity : (0 : ℝ) < q)]
      constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
    exact mul_pos (norm_pos_iff.mpr ha) (Real.cos_pos_of_mem_Ioo htq)
  · rw [hz, Circle.coe_neg, mul_neg, hc, Complex.neg_re, Complex.ofReal_re]
    exact neg_lt_zero.mpr (norm_pos_iff.mpr ha)

private theorem circle_opposite_progression {a : ℂ} (ha : a ≠ 0) {z : Circle}
    (hz : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) {q d : ℕ} (hq : 2 < q) (hd : 0 < d) (m : ℕ) :
    ∃ k : ℕ, 0 < (a * ((z ^ (m + k * d) : Circle) : ℂ)).re ∧
      (a * ((z ^ ((m + k * d) * q) : Circle) : ℂ)).re < 0 := by
  obtain ⟨v, hv₁, hv₂⟩ := circle_opposite ha hq
  have hp : ∀ n : ℕ, 0 < n → (z ^ d) ^ n ≠ 1 := by
    intro n hn
    rw [← pow_mul]
    exact hz _ (Nat.mul_pos hd hn)
  let f : ℕ → Circle := fun k => z ^ (m + k * d)
  let e := Homeomorph.mulRight (z ^ m)
  have hf : DenseRange f := by
    have he := e.surjective.denseRange.comp (circle_dense_powers hp) e.continuous
    convert he using 1
    funext k
    change f k = (z ^ d) ^ k * z ^ m
    simp [f, pow_add, ← pow_mul, mul_comm]
  let W : Set Circle := {w | 0 < (a * (w : ℂ)).re ∧ (a * ((w ^ q : Circle) : ℂ)).re < 0}
  have hW : IsOpen W := by
    change IsOpen ({w : Circle | 0 < (a * (w : ℂ)).re} ∩
      {w : Circle | (a * ((w ^ q : Circle) : ℂ)).re < 0})
    apply IsOpen.inter
    · exact isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_const.mul continuous_subtype_val))
    · exact isOpen_lt (Complex.continuous_re.comp
        (continuous_const.mul (continuous_subtype_val.comp (continuous_id.pow q)))) continuous_const
  obtain ⟨_, hw, k, rfl⟩ := hf.inter_open_nonempty W hW ⟨v, hv₁, hv₂⟩
  exact ⟨k, by simpa only [W, Set.mem_ofPred_eq, f, ← pow_mul] using hw⟩

open Complex in
private theorem roots_complex {B C : ℤ} (hD : disc B C < 0) :
    ∃ α : ℂ, 0 < α.im ∧ α + conj α = B ∧ α * conj α = C := by
  have hδ : (B : ℝ) ^ 2 - 4 * (C : ℝ) < 0 := by exact_mod_cast hD
  let q := Real.sqrt (4 * (C : ℝ) - (B : ℝ) ^ 2) / 2
  have hq : 0 < q := div_pos (Real.sqrt_pos_of_pos (by linarith)) (by norm_num)
  have hq2 : 4 * q ^ 2 = 4 * (C : ℝ) - (B : ℝ) ^ 2 := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show 0 ≤ 4 * (C : ℝ) - (B : ℝ) ^ 2 by linarith)]
  let α : ℂ := ⟨(B : ℝ) / 2, q⟩
  refine ⟨α, hq, ?_, ?_⟩
  · apply Complex.ext <;> simp [α]
  · rw [Complex.mul_conj]
    apply Complex.ext
    · simp [α, Complex.normSq_apply]
      nlinarith
    · simp

open Complex in
private theorem negative_discriminant_zero {B C : ℤ} {u : ℕ → ℤ} (hC : C ≠ 0)
    (hD : disc B C < 0)
    (hNondeg : ∀ α β : ℂ, α ^ 2 - (B : ℂ) * α + (C : ℂ) = 0 →
      β ^ 2 - (B : ℂ) * β + (C : ℂ) = 0 → α ≠ β →
      ∀ n : ℕ, 0 < n → (α / β) ^ n ≠ 1)
    (hu : Rec B C u) (hReal : Realizable u) :
    u = 0 := by
  by_contra hu0
  push Not at hu0
  have ⟨j, hj⟩ : ∃ j : ℕ, u j ≠ 0 := by
    by_contra! h
    exact hu0 (funext h)
  obtain ⟨p, hpg, hpP⟩ := Nat.exists_infinite_primes
    (max (max C.natAbs (disc B C).natAbs) (max (u j).natAbs 2) + 1)
  let _ : Fact p.Prime := ⟨hpP⟩
  have hp : 2 < p := by omega
  have hc := intCast_ne_zero hC (p := p) (by omega)
  have hj' := intCast_ne_zero hj (p := p) (by omega)
  have hdm : disc (B : ZMod p) (C : ZMod p) ≠ 0 := by
    simpa [disc] using intCast_ne_zero hD.ne (p := p) (by omega)
  obtain ⟨d, hd, hperiod⟩ := exists_mod_period hu hc
  obtain ⟨α, hαim, hsum, hprod⟩ := roots_complex hD
  have ⟨hr, hs⟩ := root_sq_sub hsum hprod
  have hα0 : α ≠ 0 := by
    intro he
    rw [he, zero_mul, eq_comm] at hprod
    exact hC (by exact_mod_cast hprod)
  have hαβ : α ≠ conj α := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith
  let c : ℂ := ((u 0 : ℝ) : ℂ) + (((u 0 : ℝ) * α.re - (u 1 : ℝ)) / α.im : ℝ) * I
  let a : ℂ := c / α
  have hrec : Rec (B : ℝ) (C : ℝ) (fun n => (c * α ^ n).re) := by
    intro n
    have h' : c * α ^ (n + 2) = (B : ℂ) * (c * α ^ (n + 1)) - (C : ℂ) * (c * α ^ n) := by
      rw [pow_succ, pow_succ' α n]
      linear_combination c * α ^ n * hr
    simpa only [Complex.sub_re, ← Complex.ofReal_intCast, Complex.re_ofReal_mul] using
      congrArg Complex.re h'
  have hform := rec_unique (rec_real_cast hu) hrec
    (by simp [c])
    (by simp [c, Complex.mul_re]; field_simp; ring)
  have ha : a ≠ 0 := by
    intro he
    have hc' : c = 0 := (div_eq_zero_iff.mp he).resolve_right hα0
    exact hj (by exact_mod_cast (show (u j : ℝ) = 0 by
      simpa [hc'] using congrFun hform j))
  let z := Circle.exp α.arg
  have hα : α = (‖α‖ : ℂ) * (z : ℂ) := (Complex.norm_mul_exp_arg_mul_I α).symm
  have hβ : conj α = (‖α‖ : ℂ) * ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv_eq_conj]
    simpa only [map_mul, Complex.conj_ofReal] using congrArg conj hα
  have hz : ∀ n : ℕ, 0 < n → z ^ n ≠ 1 := by
    intro n hn he
    apply hNondeg _ _ hr hs hαβ n hn
    have hρ0 : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hα0
    have hzPow : (z : ℂ) ^ n = 1 := by
      simpa using congrArg (fun w : Circle => (w : ℂ)) he
    rw [congrArg₂ (· / ·) hα hβ, mul_div_mul_left _ _ hρ0, div_pow, Circle.coe_inv, inv_pow,
      hzPow, inv_one, div_one]
  have hval (m : ℕ) (hm : 0 < m) :
      (u (m - 1) : ℝ) = ‖α‖ ^ m * (a * ((z ^ m : Circle) : ℂ)).re := by
    have he : a * α ^ m = c * α ^ (m - 1) := by
      rw [show m = (m - 1) + 1 by omega, pow_succ, show m - 1 + 1 - 1 = m - 1 by omega]
      dsimp [a]
      field_simp
    have h' : (a * α ^ m).re = ‖α‖ ^ m * (a * ((z ^ m : Circle) : ℂ)).re := by
      conv_lhs => rw [hα]
      rw [mul_pow, mul_left_comm, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Circle.coe_pow]
    rw [congrFun hform (m - 1), ← he, h']
  have hq : 2 < p ^ 2 := by nlinarith
  obtain ⟨k, hk₀, hk₁⟩ := circle_opposite_progression ha hz hq hd (j + 1)
  let m := j + 1 + k * d
  have hm : 0 < m := by dsimp [m]; omega
  have hmp := Nat.mul_pos hm (pow_pos hpP.pos 2)
  have hsig₀ : 0 < u (m - 1) := by
    exact_mod_cast ((hval m hm).symm ▸ mul_pos (pow_pos (norm_pos_iff.mpr hα0) _) hk₀)
  have hsig₁ : u (m * p ^ 2 - 1) < 0 := by
    exact_mod_cast ((hval _ hmp).symm ▸ mul_neg_of_pos_of_neg
      (pow_pos (norm_pos_iff.mpr hα0) _) hk₁)
  have he := mod_prime_sq hp hu hc hdm hm
  have habs := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (realizable_modEq hReal (p := p) hm 2)
  have ha' : (((u (m * p ^ 2 - 1)).natAbs : ℤ) : ZMod p) =
      (((u (m - 1)).natAbs : ℤ) : ZMod p) := by
    simpa only [Int.cast_natCast] using habs
  rw [Int.ofNat_natAbs_of_nonpos hsig₁.le, Int.natAbs_of_nonneg hsig₀.le, Int.cast_neg, he] at ha'
  have h2 := intCast_ne_zero (p := p) (z := 2) (by decide) hp
  have he' : (u (m - 1) : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (2 : ZMod p) * (u (m - 1) : ZMod p) = 0 by
      linear_combination -ha')).resolve_left
    simpa using h2
  have hper : (u (m - 1) : ZMod p) = (u j : ZMod p) := by
    rw [show m - 1 = j + k * d by dsimp [m]; omega]
    exact hperiod.nat_mul k j
  exact hj' (hper.symm.trans he')


/-! ## Realizations by finite edge shifts -/

private abbrev WalkWord {ι : Type} (A : Matrix ι ι ℕ) (n : ℕ) (i j : ι) :=
  { ve : (Fin (n + 1) → ι) × (Fin n → ℕ) //
    ve.1 0 = i ∧ ve.1 (Fin.last n) = j ∧
    ∀ k, ve.2 k < A (ve.1 k.castSucc) (ve.1 k.succ) }

private def walkWordSucc {ι : Type} (A : Matrix ι ι ℕ) (n : ℕ) (i j : ι) :
    WalkWord A (n + 1) i j ≃ (Σ k : ι, Fin (A i k) × WalkWord A n k j) where
  toFun v := ⟨v.1.1 1, ⟨v.1.2 0, by simpa [v.2.1] using v.2.2.2 0⟩,
    ⟨(Fin.tail v.1.1, Fin.tail v.1.2), rfl, v.2.2.1, fun k => by
      simpa only [Fin.tail_def, Fin.succ_castSucc] using v.2.2.2 k.succ⟩⟩
  invFun w := ⟨(Fin.cons i w.2.2.1.1, Fin.cons w.2.1.val w.2.2.1.2),
    by simp, by simpa using w.2.2.2.2.1, fun k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [w.2.2.2.1]
      · simpa only [Fin.cons_succ, ← Fin.succ_castSucc] using w.2.2.2.2.2 k⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · change Fin.cons i (Fin.tail v.1.1) = v.1.1
      exact (congrArg (fun a => Fin.cons a (Fin.tail v.1.1)) v.2.1.symm).trans
        (Fin.cons_self_tail v.1.1)
    · exact Fin.cons_self_tail v.1.2
  right_inv w := by
    rcases w with ⟨k, e, ⟨⟨v, l⟩, h0, hj, hsteps⟩⟩
    dsimp at h0
    subst k
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Prod.ext
    · exact Fin.ext rfl
    · apply Subtype.ext
      apply Prod.ext
      · change Fin.tail (α := fun _ : Fin (n + 2) => ι) (Fin.cons i v) = v
        exact Fin.tail_cons (α := fun _ : Fin (n + 2) => ι) i v
      · change Fin.tail (α := fun _ : Fin (n + 1) => ℕ) (Fin.cons e.val l) = l
        exact Fin.tail_cons (α := fun _ : Fin (n + 1) => ℕ) e.val l

private def walkWordZero {ι : Type} (A : Matrix ι ι ℕ) (i j : ι) :
    WalkWord A 0 i j ≃ PLift (i = j) where
  toFun v := ⟨v.2.1.symm.trans v.2.2.1⟩
  invFun h := ⟨(fun _ => i, Fin.elim0), rfl, h.down, fun k => Fin.elim0 k⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (funext (fun k => by
      have hk : k = 0 := Fin.ext (by have := k.isLt; omega)
      rw [hk]; exact v.2.1.symm)) (funext fun k => Fin.elim0 k)
  right_inv _ := Subsingleton.elim _ _

private theorem walkWord_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℕ) (n : ℕ) (i j : ι) :
    Finite (WalkWord A n i j) ∧ Nat.card (WalkWord A n i j) = (A ^ n) i j := by
  classical
  induction n generalizing i with
  | zero =>
    let e := walkWordZero A i j
    refine ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans ?_⟩
    by_cases h : i = j
    · subst j
      let _ : Unique (PLift (i = i)) := ⟨⟨⟨rfl⟩⟩, fun _ => Subsingleton.elim _ _⟩
      simp
    · let _ : IsEmpty (PLift (i = j)) := ⟨fun x => h x.down⟩
      simp [h]
  | succ n ih =>
    let _ (k : ι) : Finite (WalkWord A n k j) := (ih k).1
    let e := walkWordSucc A n i j
    refine ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans ?_⟩
    rw [Nat.card_sigma, pow_succ', Matrix.mul_apply]
    simp only [Nat.card_prod, Nat.card_fin, (ih _).2]

private theorem periodic_mod {ι : Type} {f : ℕ → ι} {n : ℕ} (hf : Periodic f n) (k : ℕ) :
    f (k % n) = f k := by
  have h := (hf.nat_mul (k / n)) (k % n)
  rwa [Nat.cast_id, mul_comm (k / n), Nat.mod_add_div, eq_comm] at h

private abbrev EdgePath {ι : Type} (A : Matrix ι ι ℕ) :=
  { ve : (ℕ → ι) × (ℕ → ℕ) // ∀ k, ve.2 k < A (ve.1 k) (ve.1 (k + 1)) }

private def edgeShift {ι : Type} (A : Matrix ι ι ℕ) (w : EdgePath A) : EdgePath A :=
  ⟨(fun k => w.1.1 (k + 1), fun k => w.1.2 (k + 1)), fun k => by
    simpa only [Nat.add_right_comm] using w.2 (k + 1)⟩

private theorem edgeShift_apply {ι : Type} (A : Matrix ι ι ℕ) (w : EdgePath A) (n : ℕ) :
    (edgeShift A)^[n] w =
      ⟨(fun k => w.1.1 (k + n), fun k => w.1.2 (k + n)), fun k => by
        simpa only [Nat.add_right_comm] using w.2 (k + n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    apply Subtype.ext
    apply Prod.ext <;> funext k <;> simp [edgeShift, Nat.add_right_comm, Nat.add_assoc]

private theorem path_fixed {ι : Type} {A : Matrix ι ι ℕ} {w : EdgePath A} {n : ℕ} :
    (edgeShift A)^[n] w = w ↔ Periodic w.1.1 n ∧ Periodic w.1.2 n := by
  rcases w with ⟨⟨v, l⟩, hw⟩
  rw [edgeShift_apply, Subtype.mk_eq_mk, Prod.mk.injEq]
  exact and_congr funext_iff funext_iff

private def pathFixedEquiv {ι : Type} (A : Matrix ι ι ℕ) {n : ℕ} (hn : 0 < n) :
    {w : EdgePath A // (edgeShift A)^[n] w = w} ≃ (Σ i : ι, WalkWord A n i i) := by
  let idx (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩
  have hcast (k : Fin n) : idx k = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  have hstart : (idx 0).castSucc = (0 : Fin (n + 1)) := Fin.ext (Nat.zero_mod _)
  have hlast : (idx n).castSucc = (0 : Fin (n + 1)) := Fin.ext (Nat.mod_self _)
  have hnext (k : ℕ) (w : Σ i : ι, WalkWord A n i i) :
      w.2.1.1 (idx (k + 1)).castSucc = w.2.1.1 (idx k).succ := by
    have h : (k + 1) % n = (k % n + 1) % n := by
      rw [Nat.add_mod k 1, Nat.add_mod (k % n) 1, Nat.mod_mod]
    by_cases he : k % n + 1 = n
    · have hv : (idx k).succ = Fin.last n := Fin.ext he
      have hz : (idx (k + 1)).castSucc = (0 : Fin (n + 1)) := by
        apply Fin.ext
        change (k + 1) % n = 0
        rw [h, he, Nat.mod_self]
      rw [hz, hv, w.2.2.1, w.2.2.2.1]
    · have hn' := Nat.mod_lt k hn
      have he' : (idx (k + 1)).castSucc = (idx k).succ := by
        apply Fin.ext
        exact h.trans (Nat.mod_eq_of_lt (by omega))
      rw [he']
  refine {
    toFun := fun w => ⟨w.1.1.1 0, ⟨(fun k => w.1.1.1 k, fun k => w.1.1.2 k),
      rfl, by simpa using (path_fixed.mp w.2).1 0, fun k => w.1.2 k⟩⟩
    invFun := fun w => ⟨⟨(fun k => w.2.1.1 (idx k).castSucc, fun k => w.2.1.2 (idx k)),
      fun k => by rw [hnext k w]; exact w.2.2.2.2 (idx k)⟩, path_fixed.mpr ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h (k : ℕ) : idx (k + n) = idx k := Fin.ext (Nat.add_mod_right k n)
    exact ⟨fun k => by dsimp; rw [h], fun k => by dsimp; rw [h]⟩
  · intro w
    rcases path_fixed.mp w.2 with ⟨hv, hl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (funext (periodic_mod hv)) (funext (periodic_mod hl))
  · intro w
    have hi : w.2.1.1 (idx 0).castSucc = w.1 := (congrArg w.2.1.1 hstart).trans w.2.2.1
    refine Sigma.ext hi ?_
    rcases w with ⟨i, ⟨⟨v, l⟩, h0, hend, hsteps⟩⟩
    dsimp at h0
    subst i
    have hv : (fun k : Fin (n + 1) => v (idx k).castSucc) = v := by
      funext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · change v (idx n).castSucc = v (Fin.last n)
        rw [hlast]
        exact hend.symm
      · change v (idx (j : ℕ)).castSucc = v j.castSucc
        rw [hcast]
    have hl : (fun k : Fin n => l (idx k)) = l := by funext k; rw [hcast]
    -- The underlying word is unchanged, and the endpoint proofs are irrelevant.
    exact (Subtype.heq_iff_coe_eq (fun _ => Iff.rfl)).mpr (Prod.ext hv hl)

private theorem trace_fixed {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℕ)
    (n : ℕ) (hn : 0 < n) :
    let S : Set (EdgePath A) := {x | (edgeShift A)^[n] x = x}
    S.Finite ∧ S.ncard = (A ^ n).trace := by
  dsimp only
  classical
  let _ (i : ι) : Finite (WalkWord A n i i) := (walkWord_card A n i i).1
  let e := pathFixedEquiv A hn
  constructor
  · exact Set.finite_coe_iff.mp (Finite.of_equiv _ e.symm)
  · rw [← Nat.card_coe_set_eq]
    change Nat.card {x : EdgePath A // (edgeShift A)^[n] x = x} = _
    rw [Nat.card_congr e, Nat.card_sigma, Matrix.trace]
    simp only [(walkWord_card A n _ _).2, Matrix.diag_apply]

private theorem trace_realizable {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℕ)
    {u : ℕ → ℤ} (h : ∀ n : ℕ, (u n).natAbs = (A ^ (n + 1)).trace) : Realizable u := by
  refine ⟨EdgePath A, edgeShift A, ?_⟩
  intro n
  have ⟨hf, hc⟩ := trace_fixed A (n + 1) (by omega)
  exact ⟨_, rfl, hf, hc.trans (h n).symm⟩

private theorem geometric_realizable (r : ℤ) : Realizable (fun n => r ^ (n + 1)) := by
  let A := Matrix.diagonal (fun _ : Fin 1 => r.natAbs)
  apply trace_realizable A
  intro n
  simp [A, Int.natAbs_pow, Matrix.diagonal_pow, Matrix.trace_diagonal]

private theorem trace_recurrence (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Rec M.trace M.det (fun n => (M ^ (n + 1)).trace) := by
  have h := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two] at h
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  have he : M ^ 2 = algebraMap ℤ _ M.trace * M - algebraMap ℤ _ M.det := by
    apply sub_eq_zero.mp
    convert h using 1
    abel
  exact rec_pow he (Matrix.traceLinearMap (R := ℤ) (α := ℤ) (n := Fin 2))

private theorem exists_trace_recurrence {B C : ℤ} (hD : 0 ≤ disc B C) :
    ∃ u : ℕ → ℤ, Rec B C u ∧ Realizable u ∧ u 0 = B := by
  let b : ℤ := B.natAbs
  let k : ℤ := b / 2
  let l : ℤ := b - k
  let j : ℤ := k * l - C
  let e : ℤ := if 0 ≤ B then 1 else -1
  have hb : 0 ≤ b := Int.natCast_nonneg _
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hl : 0 ≤ l := by dsimp [l, k]; omega
  have heb : e * b = B := by
    rcases le_total 0 B with h | h
    · simp [e, h, b, Int.natAbs_of_nonneg h]
    · rcases h.eq_or_lt with h | h
      · simp [e, b, h]
      · simp [e, not_le_of_gt h, b, Int.ofNat_natAbs_of_nonpos h.le]
  have he2 : e ^ 2 = 1 := by by_cases h : 0 ≤ B <;> norm_num [e, h]
  have hea : e.natAbs = 1 := by by_cases h : 0 ≤ B <;> norm_num [e, h]
  have hb2 : b ^ 2 = B ^ 2 := by
    calc
      b ^ 2 = (e * b) ^ 2 := by rw [mul_pow, he2, one_mul]
      _ = B ^ 2 := by rw [heb]
  have hj : 0 ≤ j := by
    have hbd : 4 * C ≤ b ^ 2 := by
      rw [hb2]
      exact sub_nonneg.mp hD
    have hp : b = 2 * k ∨ b = 2 * k + 1 := by dsimp [k]; omega
    dsimp [j, l]
    rcases hp with he | he
    · have hm : 4 * (k * (b - k)) = b ^ 2 := by rw [he]; ring
      omega
    · have hm : 4 * (k * (b - k)) = b ^ 2 - 1 := by rw [he]; ring
      omega
  let A : Matrix (Fin 2) (Fin 2) ℕ := !![k.toNat, 1; j.toNat, l.toNat]
  let A' : Matrix (Fin 2) (Fin 2) ℤ := A.map (Nat.castRingHom ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := e • A'
  have hM : M = !![e * k, e; e * j, e * l] := by
    ext i t
    change e * ((A i t : ℕ) : ℤ) = (!![e * k, e; e * j, e * l] : Matrix (Fin 2) (Fin 2) ℤ) i t
    fin_cases i <;> fin_cases t <;>
      simp [A, Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hl, Int.toNat_of_nonneg hj]
  have htrace : M.trace = B := by
    rw [hM, Matrix.trace_fin_two_of, ← mul_add]
    simpa [l] using heb
  have hdet : M.det = C := by
    rw [hM, Matrix.det_fin_two_of]
    calc
      e * k * (e * l) - e * (e * j) = e ^ 2 * (k * l - j) := by ring
      _ = C := by simp [he2, j]
  have hmp (m : ℕ) : (M ^ m).trace = e ^ m * (((A ^ m).trace : ℕ) : ℤ) := by
    rw [show M ^ m = e ^ m • (A ^ m).map (Nat.castRingHom ℤ) by
      simp only [M, smul_pow, A', Matrix.map_pow], Matrix.trace_smul]
    exact congrArg (e ^ m * ·) ((AddMonoidHom.map_trace (Nat.castRingHom ℤ) (A ^ m)).symm)
  let u : ℕ → ℤ := fun n => (M ^ (n + 1)).trace
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa only [u, htrace, hdet] using trace_recurrence M
  · apply trace_realizable A
    intro n
    simp [u, hmp, Int.natAbs_mul, Int.natAbs_pow, hea]
  · simpa [u] using htrace

/-! ## Dimensions of the spans -/

private def realizableSet (B C : ℤ) : Set (ℕ → ℂ) :=
  {w | ∃ u : ℕ → ℤ, Rec B C u ∧ Realizable u ∧ w = fun n => (u n : ℂ)}

private theorem rec_complex_cast {u : ℕ → ℤ} {B C : ℤ} (h : Rec B C u) :
    Rec (B : ℂ) (C : ℂ) (fun n => (u n : ℂ)) := by
  intro n
  dsimp
  exact_mod_cast h n

private theorem span_eq_singleton_of_initial {B C : ℤ} {a b : ℂ} (ha : a ≠ 0)
    (h : ∀ u ∈ realizableSet B C, a * u 1 = b * u 0)
    {v : ℕ → ℂ} (hv : v ∈ realizableSet B C) (hv0 : v 0 ≠ 0) :
    Submodule.span ℂ (realizableSet B C) = Submodule.span ℂ {v} := by
  have hrec (w : ℕ → ℂ) (hw : w ∈ realizableSet B C) : Rec (B : ℂ) (C : ℂ) w := by
    obtain ⟨u, hu, _, rfl⟩ := hw
    exact rec_complex_cast hu
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro w hw
    let t : ℂ := w 0 / v 0
    have htr : Rec (B : ℂ) (C : ℂ) (t • v) := by
      intro n
      simp only [Pi.smul_apply, smul_eq_mul, hrec v hv n]
      ring
    have h0 : w 0 = (t • v) 0 := by simp [t, div_mul_cancel₀ _ hv0]
    have h1 : w 1 = (t • v) 1 := by
      apply mul_left_cancel₀ ha
      have hw1 := h w hw
      have hv1 := h v hv
      change w 0 = t * v 0 at h0
      change a * w 1 = a * (t * v 1)
      calc
        a * w 1 = b * w 0 := hw1
        _ = b * (t * v 0) := congrArg (b * ·) h0
        _ = t * (b * v 0) := by ring
        _ = t * (a * v 1) := congrArg (t * ·) hv1.symm
        _ = _ := by ring
    exact Submodule.mem_span_singleton.mpr ⟨t, (rec_unique (hrec w hw) htr h0 h1).symm⟩
  · apply Submodule.span_le.mpr
    simpa using Submodule.subset_span hv

private theorem integral_roots {B C : ℤ} (hd : IsSquare (disc B C)) :
    ∃ r s : ℤ, r + s = B ∧ r * s = C ∧ (r - s) ^ 2 = disc B C := by
  obtain ⟨d, hD⟩ := hd
  have hD' : B ^ 2 - 4 * C = d ^ 2 := by simpa [disc, pow_two] using hD
  have hpar : B % 2 = d % 2 := by
    have hh : B ^ 2 % 2 = d ^ 2 % 2 := by omega
    have hm (z : ℤ) : z ^ 2 % 2 = z % 2 := by
      rw [pow_two, Int.mul_emod]
      have h : z % 2 = 0 ∨ z % 2 = 1 := by omega
      rcases h with h | h <;> simp [h]
    rwa [hm, hm] at hh
  let r := (B + d) / 2
  let s := (B - d) / 2
  have hsum : r + s = B := by dsimp [r, s]; omega
  have hdiff : r - s = d := by dsimp [r, s]; omega
  have hprod : r * s = C := by
    have hr : B = r + s := hsum.symm
    have hs : d = r - s := hdiff.symm
    rw [hr, hs] at hD'
    nlinarith
  exact ⟨r, s, hsum, hprod, by rw [hdiff, ← hD']; rfl⟩

private theorem split_finrank {B C : ℤ} (hC : C ≠ 0)
    (hD : 0 < disc B C) (hDs : IsSquare (disc B C)) :
    Module.finrank ℂ ↥(Submodule.span ℂ (realizableSet B C)) = 2 := by
  obtain ⟨r, s, hrsum, hrprod, hrdiff⟩ := integral_roots hDs
  have hne : r ≠ s := by intro h; simp [h] at hrdiff; omega
  have hr0 : r ≠ 0 := (mul_ne_zero_iff.mp (hrprod ▸ hC)).1
  have hs0 : s ≠ 0 := (mul_ne_zero_iff.mp (hrprod ▸ hC)).2
  have ⟨hr, hs⟩ := root_sq_sub hrsum hrprod
  let R : ℂ := r
  let S : ℂ := s
  have hR : R ≠ 0 := by dsimp [R]; exact_mod_cast hr0
  have hS : S ≠ 0 := by dsimp [S]; exact_mod_cast hs0
  have hRS : R - S ≠ 0 := sub_ne_zero.mpr (by dsimp [R, S]; exact_mod_cast hne)
  let f : ℕ → ℂ := fun n => R ^ (n + 1)
  let g : ℕ → ℂ := fun n => S ^ (n + 1)
  let v : Fin 2 → ℕ → ℂ := ![f, g]
  have hf : f ∈ realizableSet B C :=
    ⟨_, rec_geometric hr, geometric_realizable r, by funext n; simp [f, R]⟩
  have hg : g ∈ realizableSet B C :=
    ⟨_, rec_geometric hs, geometric_realizable s, by funext n; simp [g, S]⟩
  have hrecf : Rec (B : ℂ) (C : ℂ) f := rec_geometric (by dsimp [R]; exact_mod_cast hr)
  have hrecg : Rec (B : ℂ) (C : ℂ) g := rec_geometric (by dsimp [S]; exact_mod_cast hs)
  have hv : LinearIndependent ℂ v := by
    rw [linearIndependent_fin2]
    change g ≠ 0 ∧ ∀ a : ℂ, a • g ≠ f
    refine ⟨fun he => hS ?_, ?_⟩
    · simpa [g] using congrFun he 0
    · intro a he
      have h0 : a * S = R := by simpa [f, g] using congrFun he 0
      have h1 : a * S ^ 2 = R ^ 2 := by simpa [f, g] using congrFun he 1
      apply hRS
      apply mul_left_cancel₀ hR
      linear_combination S * h0 - h1
  have heq : Submodule.span ℂ (realizableSet B C) = Submodule.span ℂ (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro w ⟨u, hu, _, rfl⟩
      let w : ℕ → ℂ := fun n => (u n : ℂ)
      let a := (w 1 - S * w 0) / (R * (R - S))
      let b := (R * w 0 - w 1) / (S * (R - S))
      have he := rec_unique (rec_complex_cast hu) (rec_linearCombination hrecf hrecg a b)
        (by change w 0 = a * R ^ (0 + 1) + b * S ^ (0 + 1)
            dsimp [a, b]; field_simp; ring)
        (by change w 1 = a * R ^ (1 + 1) + b * S ^ (1 + 1)
            dsimp [a, b]; field_simp; ring)
      change w ∈ _
      rw [show w = a • f + b • g from he]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hf
      · exact hg
  rw [heq, finrank_span_eq_card hv, Fintype.card_fin]

end MetaMathlibExt.binaryrec_realizable_subspace_dim

namespace MetaMathlibExt

open binaryrec_realizable_subspace_dim in
/--
**Realizable span of a nondegenerate binary recurrence.** Let $B$ and $C$ be integers with
$C \neq 0$, and suppose the recurrence is nondegenerate: whenever $\alpha \neq \beta$ are
complex roots of $x^2 - Bx + C$, we have $(\alpha/\beta)^n \neq 1$ for every integer $n \geq 1$.
Put $\Delta = B^2 - 4C$. Let $R$ be the set of complex sequences $(u_n)_{n \geq 0}$ coming from
integer sequences $u$ that satisfy $u_{n+2} = B u_{n+1} - C u_n$ for all $n \geq 0$ and for
which there are a set $X$ and a map $T \colon X \to X$ such that, for every $n \geq 0$, the set
of points $x \in X$ with $T^{n+1}(x) = x$ is finite and has exactly $|u_n|$ elements. Then the
complex linear span of $R$ has dimension $0$ if $\Delta < 0$, dimension $1$ if $\Delta = 0$ or
$\Delta > 0$ is not the square of an integer, and dimension $2$ if $\Delta > 0$ is the square
of an integer.

Source: G. Everest, A. J. van der Poorten, Y. Puri, and T. Ward, "Integer
Sequences and Periodic Points," Journal of Integer Sequences 5 (2002),
Article 02.2.3, Theorem (label binaryrec), lines 243–254,
https://cs.uwaterloo.ca/journals/JIS/VOL5/Ward/ward2.tex
-/
public theorem binaryrec_realizable_subspace_dim (B C : ℤ) (hC : C ≠ 0)
    (hNondeg : ∀ α β : ℂ, α ^ 2 - (B : ℂ) * α + (C : ℂ) = 0 →
      β ^ 2 - (B : ℂ) * β + (C : ℂ) = 0 → α ≠ β →
      ∀ n : ℕ, 0 < n → (α / β) ^ n ≠ 1) :
    let Δ : ℤ := B ^ 2 - 4 * C;
    let R : Set (ℕ → ℂ) :=
      {w | ∃ u : ℕ → ℤ, (∀ n : ℕ, u (n + 2) = B * u (n + 1) - C * u n) ∧
        (∃ (X : Type) (T : X → X),
          ∀ n : ℕ, ∃ S : Set X, S = {x | T^[n + 1] x = x} ∧ S.Finite ∧
            S.ncard = (u n).natAbs) ∧
        w = fun n => (u n : ℂ)};
    (Δ < 0 → Module.finrank ℂ ↥(Submodule.span ℂ R) = 0) ∧
      ((Δ = 0 ∨ (0 < Δ ∧ ¬ IsSquare Δ)) →
        Module.finrank ℂ ↥(Submodule.span ℂ R) = 1) ∧
      ((0 < Δ ∧ IsSquare Δ) → Module.finrank ℂ ↥(Submodule.span ℂ R) = 2) := by
  let P := Submodule.span ℂ (realizableSet B C)
  change (disc B C < 0 → Module.finrank ℂ P = 0) ∧
    ((disc B C = 0 ∨ (0 < disc B C ∧ ¬ IsSquare (disc B C))) → Module.finrank ℂ P = 1) ∧
    ((0 < disc B C ∧ IsSquare (disc B C)) → Module.finrank ℂ P = 2)
  refine ⟨?_, ?_, fun ⟨hd, hs⟩ => split_finrank hC hd hs⟩
  · intro hd
    have he : P = ⊥ := by
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨u, hu, hreal, rfl⟩
      rw [negative_discriminant_zero hC hd hNondeg hu hreal]
      funext n
      simp
    rw [he]
    exact finrank_bot _ _
  · intro hd
    have hD : 0 ≤ disc B C := hd.elim (fun h => h.symm.le) (fun h => h.1.le)
    have hB : B ≠ 0 := by
      rcases hd with h | h
      · rintro rfl
        change (0 : ℤ) ^ 2 - 4 * C = 0 at h
        exact hC (by omega)
      · exact nondeg_real_B_ne_zero hC h.1 hNondeg
    obtain ⟨u, hu, hur, h0⟩ := exists_trace_recurrence hD
    let v : ℕ → ℂ := fun n => (u n : ℂ)
    have hv : v ∈ realizableSet B C := ⟨u, hu, hur, rfl⟩
    have hv0 : v 0 ≠ 0 := by
      change (u 0 : ℂ) ≠ 0
      rw [h0]
      exact_mod_cast hB
    have hvne : v ≠ 0 := fun h => hv0 (congrFun h 0)
    rcases hd with hd | ⟨hd, hds⟩
    · have h : ∀ w ∈ realizableSet B C, (2 : ℂ) * w 1 = (B : ℂ) * w 0 := by
        rintro _ ⟨w, hw, hwr, rfl⟩
        dsimp
        exact_mod_cast repeated_initial hC hd hw hwr
      change Module.finrank ℂ ↥(Submodule.span ℂ (realizableSet B C)) = 1
      rw [span_eq_singleton_of_initial (by norm_num) h hv hv0, finrank_span_singleton hvne]
    · have h : ∀ w ∈ realizableSet B C,
          (B : ℂ) * w 1 = ((B : ℂ) ^ 2 - 2 * (C : ℂ)) * w 0 := by
        rintro _ ⟨w, hw, hwr, rfl⟩
        dsimp
        exact_mod_cast nonsquare_initial hC hd hds hNondeg hw hwr
      have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB
      change Module.finrank ℂ ↥(Submodule.span ℂ (realizableSet B C)) = 1
      rw [span_eq_singleton_of_initial hB' h hv hv0, finrank_span_singleton hvne]

end MetaMathlibExt
