/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Padics.FibonacciFiveAdicValuation
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility

@[expose] public section

namespace MetaMathlibExt

section
-- Helper infrastructure (Steps 1-3 of the proof sketch).
-- `PisanoRet n t` is the `R_n(t)` predicate from the sketch.
/-- Return predicate: the Fibonacci pair has returned to (0,1) mod n at time t. -/
private def PisanoRet (n t : ℕ) : Prop :=
  Nat.ModEq n (Nat.fib t) 0 ∧ Nat.ModEq n (Nat.fib (t + 1)) 1

private theorem pisanoRet_add (n a b : ℕ) (ha : PisanoRet n a) (hb : PisanoRet n b) :
    PisanoRet n (a + b) := by
  unfold PisanoRet at *
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hfib_succ : Nat.fib (a + b + 1)
      = Nat.fib a * Nat.fib b + Nat.fib (a + 1) * Nat.fib (b + 1) :=
    Nat.fib_add a b
  by_cases hbpos : b = 0
  · subst hbpos; simpa using ⟨ha0, ha1⟩
  · have hbb : b - 1 + 1 = b := by omega
    have hfib : Nat.fib (a + b)
        = Nat.fib a * Nat.fib (b - 1) + Nat.fib (a + 1) * Nat.fib b := by
      conv_lhs => rw [show a + b = a + (b - 1) + 1 by omega]
      rw [Nat.fib_add a (b - 1), hbb]
    have e1 : Nat.ModEq n (Nat.fib a * Nat.fib (b - 1)) 0 := by
      have h := ha0.mul_right (Nat.fib (b - 1))
      simpa using h
    have e2 : Nat.ModEq n (Nat.fib (a + 1) * Nat.fib b) 0 := by
      have h2 : Nat.ModEq n (Nat.fib (a + 1) * Nat.fib b) (Nat.fib (a + 1) * 0) :=
        hb0.mul_left (Nat.fib (a + 1))
      simpa using h2
    have e3 : Nat.ModEq n (Nat.fib a * Nat.fib b) 0 := by
      have h := ha0.mul_right (Nat.fib b)
      simpa using h
    have e4 : Nat.ModEq n (Nat.fib (a + 1) * Nat.fib (b + 1)) 1 := by
      have h := ha1.mul hb1
      simpa using h
    constructor
    · have hsum := e1.add e2
      simp only [Nat.add_zero] at hsum
      rwa [← hfib] at hsum
    · have hsum := e3.add e4
      simp only [Nat.zero_add] at hsum
      rwa [← hfib_succ] at hsum

private theorem pisanoRet_zero (n : ℕ) : PisanoRet n 0 :=
  ⟨Nat.ModEq.refl _, Nat.ModEq.refl _⟩

private theorem pisanoRet_mul (n a : ℕ) (k : ℕ) (ha : PisanoRet n a) :
    PisanoRet n (k * a) := by
  induction k with
  | zero =>
    have h0 : 0 * a = 0 := Nat.zero_mul a
    rw [h0]
    exact pisanoRet_zero n
  | succ k ih =>
    have hka : (k + 1) * a = k * a + a := by ring
    rw [hka]
    exact pisanoRet_add n _ _ ih ha

private theorem pisanoRet_of_dvd (d n t : ℕ) (h : d ∣ n) (hrt : PisanoRet n t) :
    PisanoRet d t :=
  ⟨hrt.1.of_dvd h, hrt.2.of_dvd h⟩

private theorem pisanoRet_2_3 : PisanoRet 2 3 := by unfold PisanoRet; decide
private theorem pisanoRet_3_8 : PisanoRet 3 8 := by unfold PisanoRet; decide
private theorem pisanoRet_5_20 : PisanoRet 5 20 := by unfold PisanoRet; decide
private theorem pisanoRet_8_12 : PisanoRet 8 12 := by unfold PisanoRet; decide

/-- Returns subtract: R(a) and R(a+b) give R(b). -/
private theorem pisanoRet_sub_add (n a b : ℕ) (ha : PisanoRet n a)
    (hab : PisanoRet n (a + b)) : PisanoRet n b := by
  by_cases hbpos : b = 0
  · subst hbpos
    exact pisanoRet_zero n
  · unfold PisanoRet at *
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hab0, hab1⟩ := hab
    have hfib_succ : Nat.fib (a + b + 1)
        = Nat.fib a * Nat.fib b + Nat.fib (a + 1) * Nat.fib (b + 1) :=
      Nat.fib_add a b
    have hbb : b - 1 + 1 = b := by omega
    have hfib : Nat.fib (a + b)
        = Nat.fib a * Nat.fib (b - 1) + Nat.fib (a + 1) * Nat.fib b := by
      conv_lhs => rw [show a + b = a + (b - 1) + 1 by omega]
      rw [Nat.fib_add a (b - 1), hbb]
    have e1 : Nat.ModEq n (Nat.fib a * Nat.fib (b - 1)) 0 := by
      have h := ha0.mul_right (Nat.fib (b - 1))
      simpa using h
    have e2 : Nat.ModEq n (Nat.fib (a + 1) * Nat.fib b) (Nat.fib b) := by
      have h := ha1.mul_right (Nat.fib b)
      simpa using h
    have e3 : Nat.ModEq n (Nat.fib a * Nat.fib b) 0 := by
      have h := ha0.mul_right (Nat.fib b)
      simpa using h
    have e4 : Nat.ModEq n (Nat.fib (a + 1) * Nat.fib (b + 1)) (Nat.fib (b + 1)) := by
      have h := ha1.mul_right (Nat.fib (b + 1))
      simpa using h
    constructor
    · have hsum := e1.add e2
      rw [← hfib] at hsum
      have hfin := hsum.symm.trans hab0
      simpa using hfin
    · have hsum := e3.add e4
      rw [← hfib_succ] at hsum
      have hfin := hsum.symm.trans hab1
      simpa using hfin

/-- Minimality characterization: least return P gives R(t) iff P divides t. -/
private theorem pisanoRet_iff_dvd (n P : ℕ) (hP : 0 < P) (hret : PisanoRet n P)
    (hleast : ∀ t : ℕ, 0 < t → PisanoRet n t → P ≤ t) (t : ℕ) :
    PisanoRet n t ↔ P ∣ t := by
  constructor
  · intro ht
    have hdiv : P * (t / P) + t % P = t := Nat.div_add_mod t P
    have hmul : PisanoRet n (P * (t / P)) := by
      have h := pisanoRet_mul n P (t / P) hret
      rwa [mul_comm (t / P) P] at h
    have hplus : PisanoRet n (P * (t / P) + t % P) := by
      rwa [hdiv]
    have hmod := pisanoRet_sub_add n _ _ hmul hplus
    by_cases hz : t % P = 0
    · exact Nat.dvd_of_mod_eq_zero hz
    · have hpos : 0 < t % P := Nat.pos_of_ne_zero hz
      have hlt : t % P < P := Nat.mod_lt t hP
      have hle := hleast (t % P) hpos hmod
      omega
  · rintro ⟨k, rfl⟩
    simpa [mul_comm] using pisanoRet_mul n P k hret

/-- Return mod 1 always holds. -/
private theorem pisanoRet_one (t : ℕ) : PisanoRet 1 t := by
  unfold PisanoRet
  constructor <;> simp [Nat.ModEq, Nat.mod_one]

/-- CRT for returns at coprime moduli. -/
private theorem pisanoRet_coprime_mul (u v t : ℕ) (h : Nat.Coprime u v) :
    PisanoRet (u * v) t ↔ PisanoRet u t ∧ PisanoRet v t := by
  unfold PisanoRet
  rw [← Nat.modEq_and_modEq_iff_modEq_mul h,
    ← Nat.modEq_and_modEq_iff_modEq_mul h]
  exact and_and_and_comm

/-- Bounded non-returns below each explicit period, closed by decide. -/
private theorem pisanoRet_min_2_3 : ∀ j < 3, 0 < j → ¬ PisanoRet 2 j := by
  unfold PisanoRet
  decide
private theorem pisanoRet_min_3_8 : ∀ j < 8, 0 < j → ¬ PisanoRet 3 j := by
  unfold PisanoRet
  decide
private theorem pisanoRet_min_5_20 : ∀ j < 20, 0 < j → ¬ PisanoRet 5 j := by
  unfold PisanoRet
  decide
private theorem pisanoRet_min_8_12 : ∀ j < 12, 0 < j → ¬ PisanoRet 8 j := by
  unfold PisanoRet
  decide

/-- Least-return facts from the bounded non-returns. -/
private theorem pisanoRet_least_2_3 : ∀ t : ℕ, 0 < t → PisanoRet 2 t → 3 ≤ t := by
  intro t hpos ht
  by_cases hlt : t < 3
  · exact absurd ht (pisanoRet_min_2_3 t hlt hpos)
  · omega
private theorem pisanoRet_least_3_8 : ∀ t : ℕ, 0 < t → PisanoRet 3 t → 8 ≤ t := by
  intro t hpos ht
  by_cases hlt : t < 8
  · exact absurd ht (pisanoRet_min_3_8 t hlt hpos)
  · omega
private theorem pisanoRet_least_5_20 : ∀ t : ℕ, 0 < t → PisanoRet 5 t → 20 ≤ t := by
  intro t hpos ht
  by_cases hlt : t < 20
  · exact absurd ht (pisanoRet_min_5_20 t hlt hpos)
  · omega
private theorem pisanoRet_least_8_12 : ∀ t : ℕ, 0 < t → PisanoRet 8 t → 12 ≤ t := by
  intro t hpos ht
  by_cases hlt : t < 12
  · exact absurd ht (pisanoRet_min_8_12 t hlt hpos)
  · omega

/-- Return-iff-divisibility at the explicit pairs. -/
private theorem pisanoRet_iff_dvd_2 (t : ℕ) : PisanoRet 2 t ↔ 3 ∣ t :=
  pisanoRet_iff_dvd 2 3 (by norm_num) pisanoRet_2_3 pisanoRet_least_2_3 t
private theorem pisanoRet_iff_dvd_3 (t : ℕ) : PisanoRet 3 t ↔ 8 ∣ t :=
  pisanoRet_iff_dvd 3 8 (by norm_num) pisanoRet_3_8 pisanoRet_least_3_8 t
private theorem pisanoRet_iff_dvd_5 (t : ℕ) : PisanoRet 5 t ↔ 20 ∣ t :=
  pisanoRet_iff_dvd 5 20 (by norm_num) pisanoRet_5_20 pisanoRet_least_5_20 t
private theorem pisanoRet_iff_dvd_8 (t : ℕ) : PisanoRet 8 t ↔ 12 ∣ t :=
  pisanoRet_iff_dvd 8 12 (by norm_num) pisanoRet_8_12 pisanoRet_least_8_12 t

private theorem pisanoRet_lift_step (N t q : ℕ) (ht : 1 ≤ t) (hret : PisanoRet N t)
    (hq : q ∣ N) : PisanoRet (q * N) (q * t) := by
  unfold PisanoRet at hret ⊢
  obtain ⟨ha0, ha1⟩ := hret
  have hNa : N ∣ Nat.fib t := Nat.modEq_zero_iff_dvd.mp ha0
  have h1le : 1 ≤ Nat.fib (t + 1) := by
    rcases Nat.eq_zero_or_pos (Nat.fib (t + 1)) with h | h
    · exfalso
      have hteq : t + 1 = 0 := Nat.fib_eq_zero.mp h
      omega
    · exact h
  have hNb : N ∣ Nat.fib (t + 1) - 1 :=
    (Nat.modEq_iff_dvd' h1le).mp ha1.symm
  obtain ⟨c1, hc1⟩ := hNa
  obtain ⟨c2, hc2⟩ := hNb
  have htt1 : t - 1 + 1 = t := by omega
  have hdiv : q * N ∣ N ^ 2 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by ring⟩
  have hNN : ((N ^ 2 : ℕ) : ZMod (N ^ 2)) = 0 := by
    simp
  have hNsq : (N : ZMod (N ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]
    exact hNN
  have ea : ((Nat.fib t : ℕ) : ZMod (N ^ 2))
      = (N : ZMod (N ^ 2)) * (c1 : ZMod (N ^ 2)) := by
    rw [hc1, Nat.cast_mul]
  have eb : ((Nat.fib (t + 1) - 1 : ℕ) : ZMod (N ^ 2))
      = (N : ZMod (N ^ 2)) * (c2 : ZMod (N ^ 2)) := by
    rw [hc2, Nat.cast_mul]
  have eb' : ((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - 1
      = (N : ZMod (N ^ 2)) * (c2 : ZMod (N ^ 2)) := by
    have ecast : ((Nat.fib (t + 1) - 1 : ℕ) : ZMod (N ^ 2))
        = ((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - 1 := by
      rw [Nat.cast_sub h1le, Nat.cast_one]
    rw [← ecast]
    exact eb
  have ha2 : ((Nat.fib t : ℕ) : ZMod (N ^ 2)) * (Nat.fib t : ZMod (N ^ 2)) = 0 := by
    rw [ea]
    linear_combination (c1 : ZMod (N ^ 2)) * (c1 : ZMod (N ^ 2)) * hNsq
  have hab : ((Nat.fib t : ℕ) : ZMod (N ^ 2))
      * (((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - 1) = 0 := by
    rw [ea, eb']
    linear_combination (c1 : ZMod (N ^ 2)) * (c2 : ZMod (N ^ 2)) * hNsq
  have hb2 : (((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - 1)
      * (((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - 1) = 0 := by
    rw [eb']
    linear_combination (c2 : ZMod (N ^ 2)) * (c2 : ZMod (N ^ 2)) * hNsq
  have hF1 : ∀ s : ℕ, ((Nat.fib (s * t + t + 1) : ℕ) : ZMod (N ^ 2))
      = ((Nat.fib (s * t) : ℕ) : ZMod (N ^ 2)) * (Nat.fib t : ZMod (N ^ 2))
        + ((Nat.fib (s * t + 1) : ℕ) : ZMod (N ^ 2))
          * (Nat.fib (t + 1) : ZMod (N ^ 2)) := by
    intro s
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg _ (Nat.fib_add (s * t) t)
  have hF0 : ∀ s : ℕ, ((Nat.fib (s * t + t) : ℕ) : ZMod (N ^ 2))
      = ((Nat.fib (s * t) : ℕ) : ZMod (N ^ 2))
          * ((Nat.fib (t - 1) : ℕ) : ZMod (N ^ 2))
        + ((Nat.fib (s * t + 1) : ℕ) : ZMod (N ^ 2))
          * (Nat.fib t : ZMod (N ^ 2)) := by
    intro s
    have h := Nat.fib_add (s * t) (t - 1)
    have hst : s * t + (t - 1) + 1 = s * t + t := by omega
    rw [hst, htt1] at h
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg _ h
  have hsub : ((Nat.fib (t - 1) : ℕ) : ZMod (N ^ 2))
      = ((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - (Nat.fib t : ZMod (N ^ 2)) := by
    have h := Nat.fib_add_two (n := t - 1)
    have htt : t - 1 + 2 = t + 1 := by omega
    rw [htt, htt1] at h
    have hc : ((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2))
        = ((Nat.fib (t - 1) : ℕ) : ZMod (N ^ 2)) + (Nat.fib t : ZMod (N ^ 2)) := by
      simp only [← Nat.cast_add]
      exact congrArg _ h
    rw [hc]
    ring
  have key : ∀ s : ℕ, ((Nat.fib (s * t) : ℕ) : ZMod (N ^ 2))
        = (s : ZMod (N ^ 2)) * (Nat.fib t : ZMod (N ^ 2))
      ∧ ((Nat.fib (s * t + 1) : ℕ) : ZMod (N ^ 2))
        = 1 + (s : ZMod (N ^ 2))
          * (((Nat.fib (t + 1) : ℕ) : ZMod (N ^ 2)) - 1) := by
    intro s
    induction s with
    | zero =>
      constructor <;> simp
    | succ s ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have hst : (s + 1) * t = s * t + t := by ring
      have hst1 : (s + 1) * t + 1 = s * t + t + 1 := by ring
      have cst : (((s + 1 : ℕ)) : ZMod (N ^ 2)) = (s : ZMod (N ^ 2)) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      constructor
      · rw [hst, hF0 s, ih0, ih1, hsub, cst]
        linear_combination 2 * (s : ZMod (N ^ 2)) * hab - (s : ZMod (N ^ 2)) * ha2
      · rw [hst1, hF1 s, ih0, ih1, cst]
        linear_combination (s : ZMod (N ^ 2)) * ha2 + (s : ZMod (N ^ 2)) * hb2
  obtain ⟨hq0, hq1⟩ := key q
  have g0 : ((Nat.fib (q * t) : ℕ) : ZMod (N ^ 2))
      = ((((q * N) * c1 : ℕ)) : ZMod (N ^ 2)) := by
    rw [hq0, ea]
    push_cast
    ring
  have m0 : Nat.ModEq (N ^ 2) (Nat.fib (q * t)) ((q * N) * c1) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp g0
  have m0' : Nat.ModEq (q * N) (Nat.fib (q * t)) ((q * N) * c1) := m0.of_dvd hdiv
  have z0 : Nat.ModEq (q * N) ((q * N) * c1) 0 :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
  have f0 : Nat.ModEq (q * N) (Nat.fib (q * t)) 0 := m0'.trans z0
  have g1 : ((Nat.fib (q * t + 1) : ℕ) : ZMod (N ^ 2))
      = ((((q * N) * c2 + 1 : ℕ)) : ZMod (N ^ 2)) := by
    rw [hq1, eb']
    push_cast
    ring
  have m1 : Nat.ModEq (N ^ 2) (Nat.fib (q * t + 1)) ((q * N) * c2 + 1) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp g1
  have m1' : Nat.ModEq (q * N) (Nat.fib (q * t + 1)) ((q * N) * c2 + 1) :=
    m1.of_dvd hdiv
  have z1 : Nat.ModEq (q * N) ((q * N) * c2 + 1) 1 := by
    have hdz : Nat.ModEq (q * N) ((q * N) * c2) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
    have hadd : Nat.ModEq (q * N) (1 + (q * N) * c2) (1 + 0) :=
      (Nat.ModEq.refl 1).add hdz
    rw [add_zero] at hadd
    rw [add_comm ((q * N) * c2) 1]
    exact hadd
  have f1 : Nat.ModEq (q * N) (Nat.fib (q * t + 1)) 1 := m1'.trans z1
  exact ⟨f0, f1⟩

-- Iterated lifting: prime-power return chains for 2, 3, 5.
private theorem pisanoRet_pow_two_aux : ∀ a : ℕ, PisanoRet (2 ^ (a + 1)) (3 * 2 ^ a) := by
  intro a
  induction a with
  | zero => simpa using pisanoRet_2_3
  | succ a ih =>
    have ht : 1 ≤ 3 * 2 ^ a :=
      Nat.mul_pos (by norm_num) (pow_pos (by norm_num) a)
    have hq : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
    have h := pisanoRet_lift_step (2 ^ (a + 1)) (3 * 2 ^ a) 2 ht ih hq
    have e1 : 2 * 2 ^ (a + 1) = 2 ^ (a + 1 + 1) := by ring
    have e2 : 2 * (3 * 2 ^ a) = 3 * 2 ^ (a + 1) := by ring
    rwa [e1, e2] at h

private theorem pisanoRet_pow_three_aux : ∀ b : ℕ, PisanoRet (3 ^ (b + 1)) (8 * 3 ^ b) := by
  intro b
  induction b with
  | zero => simpa using pisanoRet_3_8
  | succ b ih =>
    have ht : 1 ≤ 8 * 3 ^ b :=
      Nat.mul_pos (by norm_num) (pow_pos (by norm_num) b)
    have hq : 3 ∣ 3 ^ (b + 1) := dvd_pow_self 3 (by omega)
    have h := pisanoRet_lift_step (3 ^ (b + 1)) (8 * 3 ^ b) 3 ht ih hq
    have e1 : 3 * 3 ^ (b + 1) = 3 ^ (b + 1 + 1) := by ring
    have e2 : 3 * (8 * 3 ^ b) = 8 * 3 ^ (b + 1) := by ring
    rwa [e1, e2] at h

private theorem pisanoRet_pow_five_aux : ∀ c : ℕ, PisanoRet (5 ^ (c + 1)) (4 * 5 ^ (c + 1)) := by
  intro c
  induction c with
  | zero => simpa using pisanoRet_5_20
  | succ c ih =>
    have ht : 1 ≤ 4 * 5 ^ (c + 1) :=
      Nat.mul_pos (by norm_num) (pow_pos (by norm_num) (c + 1))
    have hq : 5 ∣ 5 ^ (c + 1) := dvd_pow_self 5 (by omega)
    have h := pisanoRet_lift_step (5 ^ (c + 1)) (4 * 5 ^ (c + 1)) 5 ht ih hq
    have e1 : 5 * 5 ^ (c + 1) = 5 ^ (c + 1 + 1) := by ring
    have e2 : 5 * (4 * 5 ^ (c + 1)) = 4 * 5 ^ (c + 1 + 1) := by ring
    rwa [e1, e2] at h

/-- Prime return for odd `q ≠ 5` via Legendre-symbol divisor and Fermat. -/
private theorem pisanoRet_prime_odd {q : ℕ} (hq : q.Prime) (hq5 : q ≠ 5)
    (hq2 : 2 < q) : PisanoRet q ((q - 1) ^ 2 * (q + 1)) := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  set k : ℕ := (if legendreSym q 5 = 1 then q - 1 else q + 1) with hk_def
  have hdiv : q ∣ Nat.fib k := by
    rw [hk_def]
    exact fib_prime_dvd_fib_of_legendre_sub q hq5 hq2
  have hk_pos : 0 < k := by
    rw [hk_def]
    by_cases hleg : legendreSym q 5 = 1
    · simp only [hleg, reduceIte]
      omega
    · simp only [hleg, reduceIte]
      omega
  have hk_one : 1 ≤ k := hk_pos
  have hcop : Nat.Coprime (Nat.fib k) (Nat.fib (k + 1)) :=
    Nat.fib_coprime_fib_succ k
  have hq_not_dvd_succ : ¬ q ∣ Nat.fib (k + 1) := by
    intro hdvd
    have hq_gcd : q ∣ Nat.gcd (Nat.fib k) (Nat.fib (k + 1)) :=
      Nat.dvd_gcd hdiv hdvd
    have hq1 : q ∣ 1 := hcop ▸ hq_gcd
    have hq_eq1 : q = 1 := Nat.dvd_one.mp hq1
    have hlt : 1 < q := hq.one_lt
    omega
  have hz0 : ((Nat.fib k : ℕ) : ZMod q) = 0 := by
    have hmod0 : Nat.ModEq q (Nat.fib k) 0 := Nat.modEq_zero_iff_dvd.mpr hdiv
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod0
    simpa using h
  have hz_succ_ne : ((Nat.fib (k + 1) : ℕ) : ZMod q) ≠ 0 := by
    intro hcon
    have hcast : ((Nat.fib (k + 1) : ℕ) : ZMod q) = ((0 : ℕ) : ZMod q) := by
      simpa using hcon
    have hmod : Nat.ModEq q (Nat.fib (k + 1)) 0 :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hdvd : q ∣ Nat.fib (k + 1) := Nat.modEq_zero_iff_dvd.mp hmod
    exact hq_not_dvd_succ hdvd
  have hkm1 : k - 1 + 1 = k := Nat.sub_add_cancel hk_one
  have hF1 : ∀ s : ℕ, ((Nat.fib (s * k + k + 1) : ℕ) : ZMod q)
      = ((Nat.fib (s * k) : ℕ) : ZMod q) * ((Nat.fib k : ℕ) : ZMod q)
        + ((Nat.fib (s * k + 1) : ℕ) : ZMod q)
          * ((Nat.fib (k + 1) : ℕ) : ZMod q) := by
    intro s
    have h := Nat.fib_add (s * k) k
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg _ h
  have hF0 : ∀ s : ℕ, ((Nat.fib (s * k + k) : ℕ) : ZMod q)
      = ((Nat.fib (s * k) : ℕ) : ZMod q) * ((Nat.fib (k - 1) : ℕ) : ZMod q)
        + ((Nat.fib (s * k + 1) : ℕ) : ZMod q)
          * ((Nat.fib k : ℕ) : ZMod q) := by
    intro s
    have h := Nat.fib_add (s * k) (k - 1)
    have hst : s * k + (k - 1) + 1 = s * k + k := by
      rw [add_assoc, hkm1]
    rw [hst, hkm1] at h
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg _ h
  have key : ∀ j : ℕ, ((Nat.fib (j * k) : ℕ) : ZMod q) = 0
      ∧ ((Nat.fib (j * k + 1) : ℕ) : ZMod q)
        = ((Nat.fib (k + 1) : ℕ) : ZMod q) ^ j := by
    intro j
    induction j with
    | zero =>
      constructor <;> simp
    | succ j ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have hst : (j + 1) * k = j * k + k := by ring
      have hst1 : (j + 1) * k + 1 = j * k + k + 1 := by ring
      constructor
      · rw [hst, hF0 j, ih0, hz0]
        ring
      · rw [hst1, hF1 j, ih0, ih1, hz0, pow_succ]
        ring
  obtain ⟨hq0, hq1⟩ := key (q - 1)
  have hferm : ((Nat.fib (k + 1) : ℕ) : ZMod q) ^ (q - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hz_succ_ne
  rw [hferm] at hq1
  have hR : PisanoRet q ((q - 1) * k) := by
    constructor
    · have hcast : ((Nat.fib ((q - 1) * k) : ℕ) : ZMod q)
          = ((0 : ℕ) : ZMod q) := by
        simpa using hq0
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    · have hcast : ((Nat.fib ((q - 1) * k + 1) : ℕ) : ZMod q)
          = ((1 : ℕ) : ZMod q) := by
        simpa using hq1
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  by_cases hleg : legendreSym q 5 = 1
  · have hk_eq : k = q - 1 := by
      simp [hk_def, hleg]
    have heq : (q + 1) * ((q - 1) * k) = (q - 1) ^ 2 * (q + 1) := by
      rw [hk_eq]
      ring
    have hR' : PisanoRet q ((q + 1) * ((q - 1) * k)) :=
      pisanoRet_mul q ((q - 1) * k) (q + 1) hR
    rwa [heq] at hR'
  · have hk_eq : k = q + 1 := by
      simp [hk_def, hleg]
    have heq : (q - 1) * ((q - 1) * k) = (q - 1) ^ 2 * (q + 1) := by
      rw [hk_eq]
      ring
    have hR' : PisanoRet q ((q - 1) * ((q - 1) * k)) :=
      pisanoRet_mul q ((q - 1) * k) (q - 1) hR
    rwa [heq] at hR'

/-- Prime-power returns for 2, 3, 5 in `e - 1` form. -/
private theorem pisanoRet_pow_two (e : ℕ) (he : 1 ≤ e) :
    PisanoRet (2 ^ e) (3 * 2 ^ (e - 1)) := by
  have he_eq : e = (e - 1) + 1 := by omega
  rw [he_eq]
  exact pisanoRet_pow_two_aux (e - 1)

private theorem pisanoRet_pow_three (e : ℕ) (he : 1 ≤ e) :
    PisanoRet (3 ^ e) (8 * 3 ^ (e - 1)) := by
  have he_eq : e = (e - 1) + 1 := by omega
  rw [he_eq]
  exact pisanoRet_pow_three_aux (e - 1)

private theorem pisanoRet_pow_five (e : ℕ) :
    PisanoRet (5 ^ e) (4 * 5 ^ e) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simpa using pisanoRet_one 4
  · have he_eq : e = (e - 1) + 1 := by omega
    rw [he_eq]
    exact pisanoRet_pow_five_aux (e - 1)

/-- Lifted prime-power return for odd `q ≠ 5`. -/
private theorem pisanoRet_prime_pow_odd {q : ℕ} (hq : q.Prime) (hq5 : q ≠ 5)
    (hq2 : 2 < q) (e : ℕ) (he : 1 ≤ e) :
    PisanoRet (q ^ e) (q ^ (e - 1) * ((q - 1) ^ 2 * (q + 1))) := by
  have hW0_pos : 0 < (q - 1) ^ 2 * (q + 1) := by
    apply Nat.mul_pos
    · exact pow_pos (by omega) 2
    · omega
  have aux : ∀ d : ℕ, PisanoRet (q ^ (d + 1)) (q ^ d * ((q - 1) ^ 2 * (q + 1))) := by
    intro d
    induction d with
    | zero =>
      simpa using pisanoRet_prime_odd hq hq5 hq2
    | succ d ih =>
      have ht : 1 ≤ q ^ d * ((q - 1) ^ 2 * (q + 1)) :=
        Nat.mul_pos (pow_pos hq.pos d) hW0_pos
      have hqdvd : q ∣ q ^ (d + 1) := dvd_pow_self q (by omega)
      have h := pisanoRet_lift_step (q ^ (d + 1)) (q ^ d * ((q - 1) ^ 2 * (q + 1)))
        q ht ih hqdvd
      have e1 : q * q ^ (d + 1) = q ^ (d + 1 + 1) := by ring
      have e2 : q * (q ^ d * ((q - 1) ^ 2 * (q + 1)))
          = q ^ (d + 1) * ((q - 1) ^ 2 * (q + 1)) := by ring
      rwa [e1, e2] at h
  have he_eq : e = (e - 1) + 1 := by omega
  rw [he_eq]
  exact aux (e - 1)

/-- Non-divisibility of the 2-power witness by a large prime. -/
private theorem not_dvd_W_two {r k : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) :
    ¬ r ∣ 3 * 2 ^ k := by
  intro hdvd
  rcases (hr.dvd_mul).mp hdvd with h3 | h2
  · have hEq : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    omega
  · have h2dvd : r ∣ 2 := hr.dvd_of_dvd_pow h2
    have hEq : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2dvd
    omega

/-- Non-divisibility of the 3-power witness by a large prime. -/
private theorem not_dvd_W_three {r k : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) :
    ¬ r ∣ 8 * 3 ^ k := by
  intro hdvd
  rcases (hr.dvd_mul).mp hdvd with h8 | h3
  · have h8' : r ∣ 2 ^ 3 := by
      have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
      rwa [h8eq] at h8
    have h2dvd : r ∣ 2 := hr.dvd_of_dvd_pow h8'
    have hEq : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2dvd
    omega
  · have h3dvd : r ∣ 3 := hr.dvd_of_dvd_pow h3
    have hEq : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3dvd
    omega

/-- Non-divisibility of the 5-power witness by a large prime. -/
private theorem not_dvd_W_five {r e : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) :
    ¬ r ∣ 4 * 5 ^ e := by
  intro hdvd
  rcases (hr.dvd_mul).mp hdvd with h4 | h5
  · have h4' : r ∣ 2 ^ 2 := by
      have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
      rwa [h4eq] at h4
    have h2dvd : r ∣ 2 := hr.dvd_of_dvd_pow h4'
    have hEq : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2dvd
    omega
  · have h5dvd : r ∣ 5 := hr.dvd_of_dvd_pow h5
    have hEq : r = 5 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h5dvd
    omega

/-- `r = q + 1` is impossible for primes with `7 ≤ r`. -/
private theorem prime_succ_ne_of_ge7 {r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hr7 : 7 ≤ r) (heq : r = q + 1) : False := by
  rcases hq.eq_two_or_odd' with hq2 | hqodd
  · omega
  · have heven : Even (q + 1) := hqodd.add_one
    have heven_r : Even r := heq ▸ heven
    have hr2 : r = 2 := (hr.even_iff).mp heven_r
    omega

/-- Non-divisibility of the odd-prime witness by a larger prime. -/
private theorem not_dvd_W_odd {r q e : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hr7 : 7 ≤ r) (hlt : q < r) :
    ¬ r ∣ q ^ (e - 1) * ((q - 1) ^ 2 * (q + 1)) := by
  intro hdvd
  rcases (hr.dvd_mul).mp hdvd with hpow | hrest
  · have hqdvd : r ∣ q := hr.dvd_of_dvd_pow hpow
    have hEq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hqdvd
    omega
  · rcases (hr.dvd_mul).mp hrest with hsub | hsucc
    · have hqm1 : r ∣ q - 1 := hr.dvd_of_dvd_pow hsub
      have hpos : 0 < q - 1 := by
        have h2 : 2 ≤ q := hq.two_le
        omega
      have hle : r ≤ q - 1 := Nat.le_of_dvd hpos hqm1
      omega
    · have hpos : 0 < q + 1 := Nat.succ_pos q
      have hle : r ≤ q + 1 := Nat.le_of_dvd hpos hsucc
      have hge : q + 1 ≤ r := by omega
      have heq : r = q + 1 := le_antisymm hle hge
      exact prime_succ_ne_of_ge7 hr hq hr7 heq

/-- `8` never divides `12 * 5 ^ k`. -/
private theorem not_8_dvd_12_mul_pow5 (k : ℕ) : ¬ 8 ∣ 12 * 5 ^ k := by
  intro hdvd
  have h8eq : (8 : ℕ) = 4 * 2 := by norm_num
  have h12eq : 12 * 5 ^ k = 4 * (3 * 5 ^ k) := by ring
  rw [h8eq, h12eq] at hdvd
  have h2dvd : 2 ∣ 3 * 5 ^ k :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd with h3 | h5
  · have h23 : ¬ (2 ∣ 3) := by decide
    exact h23 h3
  · have h25 : (2 : ℕ) ∣ 5 := Nat.prime_two.dvd_of_dvd_pow h5
    have h25' : ¬ (2 ∣ 5) := by decide
    exact h25' h25

/-- `12` never divides `8 * 5 ^ k`. -/
private theorem not_12_dvd_8_mul_pow5 (k : ℕ) : ¬ 12 ∣ 8 * 5 ^ k := by
  intro hdvd
  have h12eq : (12 : ℕ) = 4 * 3 := by norm_num
  have h8eq : 8 * 5 ^ k = 4 * (2 * 5 ^ k) := by ring
  rw [h12eq, h8eq] at hdvd
  have h3dvd : 3 ∣ 2 * 5 ^ k :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3dvd with h2 | h5
  · have h32 : ¬ (3 ∣ 2) := by decide
    exact h32 h2
  · have h35 : (3 : ℕ) ∣ 5 := Nat.prime_three.dvd_of_dvd_pow h5
    have h35' : ¬ (3 ∣ 5) := by decide
    exact h35' h35

/-- Prime divisors of `24 * 5 ^ k` are 2, 3, or 5. -/
private theorem prime_dvd_24_mul_pow5 {r k : ℕ} (hr : r.Prime)
    (hdvd : r ∣ 24 * 5 ^ k) : r = 2 ∨ r = 3 ∨ r = 5 := by
  rcases (hr.dvd_mul).mp hdvd with h24 | h5
  · have h24eq : (24 : ℕ) = 8 * 3 := by norm_num
    rw [h24eq] at h24
    rcases (hr.dvd_mul).mp h24 with h8 | h3
    · have h8' : r ∣ 2 ^ 3 := by
        have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
        rwa [h8eq] at h8
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h8'
      have hEq : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
      exact Or.inl hEq
    · have hEq : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
      exact Or.inr (Or.inl hEq)
  · have h5dvd : r ∣ 5 := hr.dvd_of_dvd_pow h5
    have hEq : r = 5 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h5dvd
    exact Or.inr (Or.inr hEq)

/-- Five-adic obstruction: `5 ^ k` never divides `fib (24 * 5 ^ (k - 1))` for `1 ≤ k`. -/
private theorem not_pow5_dvd_fib_24_mul (k : ℕ) (hk1 : 1 ≤ k)
    (hdvd : 5 ^ k ∣ Nat.fib (24 * 5 ^ (k - 1))) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn_pos : 0 < 24 * 5 ^ (k - 1) :=
    Nat.mul_pos (by norm_num) (pow_pos (by norm_num) (k - 1))
  have hn1 : 1 ≤ 24 * 5 ^ (k - 1) := hn_pos
  have hn_ne0 : 24 * 5 ^ (k - 1) ≠ 0 := by omega
  have hf_ne0 : Nat.fib (24 * 5 ^ (k - 1)) ≠ 0 := fun h =>
    hn_ne0 ((Nat.fib_eq_zero).mp h)
  have hval := lengyel_fibonacci_five_adic (24 * 5 ^ (k - 1)) hn1
  have hval_mul : padicValNat 5 (24 * 5 ^ (k - 1))
      = padicValNat 5 24 + padicValNat 5 (5 ^ (k - 1)) :=
    padicValNat.mul (by norm_num) (pow_ne_zero _ (by norm_num))
  have hval24 : padicValNat 5 24 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 24)
  have hval5 : padicValNat 5 (5 ^ (k - 1)) = k - 1 := padicValNat.prime_pow (k - 1)
  have hval_n : padicValNat 5 (24 * 5 ^ (k - 1)) = k - 1 := by
    rw [hval_mul, hval24, hval5, zero_add]
  have hle : k ≤ padicValNat 5 (Nat.fib (24 * 5 ^ (k - 1))) :=
    (padicValNat_dvd_iff_le hf_ne0).mp hdvd
  rw [hval, hval_n] at hle
  omega

/-- Direction `<=`: `m = 24 * 5 ^ k` forces `period = m`. -/
private theorem period_eq_of_form (m period k : ℕ) (hm : 1 < m)
    (hperiod : 0 < period) (hreturn : PisanoRet m period)
    (hleast : ∀ t : ℕ, 0 < t → PisanoRet m t → period ≤ t)
    (hm_eq : m = 24 * 5 ^ k) : period = m := by
  have h12m : 12 ∣ m := ⟨2 * 5 ^ k, by rw [hm_eq]; ring⟩
  have h8m : 8 ∣ m := ⟨3 * 5 ^ k, by rw [hm_eq]; ring⟩
  have hR8 : PisanoRet 8 m := (pisanoRet_iff_dvd_8 m).mpr h12m
  have hR3 : PisanoRet 3 m := (pisanoRet_iff_dvd_3 m).mpr h8m
  have hR5 : PisanoRet (5 ^ k) m := by
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simpa using pisanoRet_one m
    · have hR0 := pisanoRet_pow_five k
      have heq : m = 6 * (4 * 5 ^ k) := by rw [hm_eq]; ring
      rw [heq]
      exact pisanoRet_mul (5 ^ k) (4 * 5 ^ k) 6 hR0
  have hcop83 : Nat.Coprime 8 3 := by decide
  have hR83 : PisanoRet (8 * 3) m :=
    (pisanoRet_coprime_mul 8 3 m hcop83).mpr ⟨hR8, hR3⟩
  have h85 : Nat.Coprime 8 5 := by decide
  have h35 : Nat.Coprime 3 5 := by decide
  have hcop : Nat.Coprime (8 * 3) (5 ^ k) :=
    Nat.Coprime.mul_left (h85.pow_right k) (h35.pow_right k)
  have hR : PisanoRet ((8 * 3) * 5 ^ k) m :=
    (pisanoRet_coprime_mul (8 * 3) (5 ^ k) m hcop).mpr ⟨hR83, hR5⟩
  have heqM : (8 * 3) * 5 ^ k = m := by rw [hm_eq]
  have hRm : PisanoRet m m := heqM ▸ hR
  have hiff := pisanoRet_iff_dvd m period hperiod hreturn hleast
  have hdiv : period ∣ m := (hiff m).mp hRm
  have hm_pos : 0 < m := by omega
  have hle : period ≤ m := Nat.le_of_dvd hm_pos hdiv
  by_cases heq : period = m
  · exact heq
  · have hlt : period < m := lt_of_le_of_ne hle heq
    obtain ⟨d, hd_eq⟩ := hdiv
    have hd_pos : 0 < d := by
      by_contra h
      have hd0 : d = 0 := by omega
      rw [hd0, mul_zero] at hd_eq
      omega
    have hd_gt1 : 1 < d := by
      by_contra h
      have hd1 : d = 1 := by omega
      rw [hd1, mul_one] at hd_eq
      omega
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
    have hd_dvd_m : d ∣ m := ⟨period, by rw [hd_eq]; ring⟩
    have hr_m : r ∣ m := hr_dvd.trans hd_dvd_m
    have hr_form : r ∣ 24 * 5 ^ k := hm_eq ▸ hr_m
    rcases prime_dvd_24_mul_pow5 hr_prime hr_form with h2 | h3 | h5
    · subst h2
      obtain ⟨d', hd'⟩ := hr_dvd
      have hm_eq2 : m = (period * d') * 2 := by rw [hd_eq, hd']; ring
      have hmr_eq : m / 2 = period * d' := by
        rw [hm_eq2]
        exact Nat.mul_div_cancel _ (by norm_num)
      have hRmr : PisanoRet m (m / 2) := by
        rw [hmr_eq, mul_comm period d']
        exact pisanoRet_mul m period d' hreturn
      have h3m : 3 ∣ m := ⟨8 * 5 ^ k, by rw [hm_eq]; ring⟩
      have hR3mr : PisanoRet 3 (m / 2) := pisanoRet_of_dvd 3 m (m / 2) h3m hRmr
      have h8dvd : 8 ∣ m / 2 := (pisanoRet_iff_dvd_3 (m / 2)).mp hR3mr
      have hmr2_eq : m / 2 = 12 * 5 ^ k := by
        have h24eq : 24 * 5 ^ k = (12 * 5 ^ k) * 2 := by ring
        rw [hm_eq, h24eq]
        exact Nat.mul_div_cancel _ (by norm_num)
      rw [hmr2_eq] at h8dvd
      exact False.elim (not_8_dvd_12_mul_pow5 k h8dvd)
    · subst h3
      obtain ⟨d', hd'⟩ := hr_dvd
      have hm_eq3 : m = (period * d') * 3 := by rw [hd_eq, hd']; ring
      have hmr_eq : m / 3 = period * d' := by
        rw [hm_eq3]
        exact Nat.mul_div_cancel _ (by norm_num)
      have hRmr : PisanoRet m (m / 3) := by
        rw [hmr_eq, mul_comm period d']
        exact pisanoRet_mul m period d' hreturn
      have h8m' : 8 ∣ m := ⟨3 * 5 ^ k, by rw [hm_eq]; ring⟩
      have hR8mr : PisanoRet 8 (m / 3) := pisanoRet_of_dvd 8 m (m / 3) h8m' hRmr
      have h12dvd : 12 ∣ m / 3 := (pisanoRet_iff_dvd_8 (m / 3)).mp hR8mr
      have hmr3_eq : m / 3 = 8 * 5 ^ k := by
        have h24eq : 24 * 5 ^ k = (8 * 5 ^ k) * 3 := by ring
        rw [hm_eq, h24eq]
        exact Nat.mul_div_cancel _ (by norm_num)
      rw [hmr3_eq] at h12dvd
      exact False.elim (not_12_dvd_8_mul_pow5 k h12dvd)
    · subst h5
      have hk_pos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simp at hr_form
        · exact hpos
      obtain ⟨d', hd'⟩ := hr_dvd
      have hm_eq5 : m = (period * d') * 5 := by rw [hd_eq, hd']; ring
      have hmr_eq : m / 5 = period * d' := by
        rw [hm_eq5]
        exact Nat.mul_div_cancel _ (by norm_num)
      have hRmr : PisanoRet m (m / 5) := by
        rw [hmr_eq, mul_comm period d']
        exact pisanoRet_mul m period d' hreturn
      have h5k_m : 5 ^ k ∣ m := ⟨24, by rw [hm_eq]; ring⟩
      have hR5mr : PisanoRet (5 ^ k) (m / 5) :=
        pisanoRet_of_dvd (5 ^ k) m (m / 5) h5k_m hRmr
      have h5dvd : 5 ^ k ∣ Nat.fib (m / 5) :=
        Nat.modEq_zero_iff_dvd.mp hR5mr.1
      have hk_eq : k = (k - 1) + 1 := by omega
      have hmr5_eq : m / 5 = 24 * 5 ^ (k - 1) := by
        have hpow : 5 ^ k = 5 ^ (k - 1) * 5 := by conv_lhs => rw [hk_eq, pow_succ]
        have hmeq : 24 * 5 ^ k = (24 * 5 ^ (k - 1)) * 5 := by rw [hpow]; ring
        rw [hm_eq, hmeq]
        exact Nat.mul_div_cancel _ (by norm_num)
      rw [hmr5_eq] at h5dvd
      exact False.elim (not_pow5_dvd_fib_24_mul k hk_pos h5dvd)

/-- Fixed points are multiples of 24. -/
private theorem dvd_24_of_fixed (m : ℕ) (hm : 1 < m)
    (hno_large : ∀ r : ℕ, r.Prime → r ∣ m → r < 7)
    (hRm : PisanoRet m m) : 24 ∣ m := by
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hp_lt7 : p < 7 := hno_large p hp_prime hp_dvd
  have hp235 : p = 2 ∨ p = 3 ∨ p = 5 := by
    have h2le := hp_prime.two_le
    interval_cases p
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp_prime (by decide)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hp_prime (by decide)
  have h5_imp_2 : 5 ∣ m → 2 ∣ m := by
    intro h5m
    have hR5m : PisanoRet 5 m := pisanoRet_of_dvd 5 m m h5m hRm
    have h20m : 20 ∣ m := (pisanoRet_iff_dvd_5 m).mp hR5m
    exact (by norm_num : 2 ∣ 20).trans h20m
  have h2_imp_3 : 2 ∣ m → 3 ∣ m := by
    intro h2m
    have hR2m : PisanoRet 2 m := pisanoRet_of_dvd 2 m m h2m hRm
    exact (pisanoRet_iff_dvd_2 m).mp hR2m
  have h3_imp_8 : 3 ∣ m → 8 ∣ m := by
    intro h3m
    have hR3m : PisanoRet 3 m := pisanoRet_of_dvd 3 m m h3m hRm
    exact (pisanoRet_iff_dvd_3 m).mp hR3m
  have h8m : 8 ∣ m := by
    rcases hp235 with h2 | h3 | h5
    · subst h2
      exact h3_imp_8 (h2_imp_3 hp_dvd)
    · subst h3
      exact h3_imp_8 hp_dvd
    · subst h5
      exact h3_imp_8 (h2_imp_3 (h5_imp_2 hp_dvd))
  have h3m : 3 ∣ m := by
    rcases hp235 with h2 | h3 | h5
    · subst h2
      exact h2_imp_3 hp_dvd
    · subst h3
      exact hp_dvd
    · subst h5
      exact h2_imp_3 (h5_imp_2 hp_dvd)
  have hcop83 : Nat.Coprime 8 3 := by decide
  have h24 : 8 * 3 ∣ m := hcop83.mul_dvd_of_dvd_of_dvd h8m h3m
  have heq : (8 * 3 : ℕ) = 24 := by norm_num
  rwa [heq] at h24

/-- Witness return time coprime to a large prime, by prime-power induction. -/
private theorem exists_W_of_lt {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (u : ℕ)
    (hu_pos : 0 < u) (hlt : ∀ q : ℕ, q.Prime → q ∣ u → q < r) :
    ∃ W : ℕ, PisanoRet u W ∧ ¬ r ∣ W := by
  have h :=
    Nat.recOnPrimeCoprime
      (motive := fun u =>
        0 < u → (∀ q : ℕ, q.Prime → q ∣ u → q < r) →
          ∃ W : ℕ, PisanoRet u W ∧ ¬ r ∣ W)
      (fun h0 _ => absurd h0 (lt_irrefl 0))
      (fun p n hp _ hlt' => by
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · have hr1 : ¬ r ∣ 1 := by
            intro hdvd
            have hEq : r = 1 := Nat.dvd_one.mp hdvd
            omega
          have hR : PisanoRet (p ^ 0) 1 := by
            rw [pow_zero]
            exact pisanoRet_one 1
          exact ⟨1, hR, hr1⟩
        · by_cases hp2 : p = 2
          · subst hp2
            exact ⟨_, pisanoRet_pow_two n hn_pos, not_dvd_W_two hr hr7⟩
          · by_cases hp3 : p = 3
            · subst hp3
              exact ⟨_, pisanoRet_pow_three n hn_pos, not_dvd_W_three hr hr7⟩
            · by_cases hp5 : p = 5
              · subst hp5
                exact ⟨_, pisanoRet_pow_five n, not_dvd_W_five hr hr7⟩
              · have hp2' : 2 < p := by
                  have h2le := hp.two_le
                  omega
                have hpdvd : p ∣ p ^ n := dvd_pow_self p (by omega)
                have hlt_p : p < r := hlt' p hp hpdvd
                exact ⟨_, pisanoRet_prime_pow_odd hp hp5 hp2' n hn_pos,
                  not_dvd_W_odd hr hp hr7 hlt_p⟩)
      (fun a b ha1 hb1 hcop iha ihb _ hlt' => by
        have hlt_a : ∀ q : ℕ, q.Prime → q ∣ a → q < r := by
          intro q hq hqdvd
          exact hlt' q hq (hqdvd.trans (dvd_mul_right a b))
        have hlt_b : ∀ q : ℕ, q.Prime → q ∣ b → q < r := by
          intro q hq hqdvd
          exact hlt' q hq (hqdvd.trans (dvd_mul_left b a))
        obtain ⟨Wa, hRa, hrWa⟩ := iha (by omega) hlt_a
        obtain ⟨Wb, hRb, hrWb⟩ := ihb (by omega) hlt_b
        have hRaW : PisanoRet a (Wa * Wb) := by
          rw [mul_comm Wa Wb]
          exact pisanoRet_mul a Wa Wb hRa
        have hRbW : PisanoRet b (Wa * Wb) := pisanoRet_mul b Wb Wa hRb
        have hR : PisanoRet (a * b) (Wa * Wb) :=
          (pisanoRet_coprime_mul a b (Wa * Wb) hcop).mpr ⟨hRaW, hRbW⟩
        have hrW : ¬ r ∣ Wa * Wb := by
          intro hdvd
          rcases (hr.dvd_mul).mp hdvd with h | h
          · exact hrWa h
          · exact hrWb h
        exact ⟨Wa * Wb, hR, hrW⟩)
      u
  exact h hu_pos hlt

/-- Prime `≠ 2, 3, 5` is `≥ 7`. -/
private theorem seven_le_of_prime_ne_235 {q : ℕ} (hq : q.Prime)
    (h2 : q ≠ 2) (h3 : q ≠ 3) (h5 : q ≠ 5) : 7 ≤ q := by
  by_contra hlt
  have hlt7 : q < 7 := by omega
  have h2le := hq.two_le
  interval_cases q
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact absurd hq (by decide)
  · exact absurd rfl h5
  · exact absurd hq (by decide)

/-- Fixed points have the form `24 * 5 ^ c`. -/
private theorem exists_lambda_of_fixed (m : ℕ) (hm : 1 < m)
    (hiff : ∀ t : ℕ, PisanoRet m t ↔ m ∣ t)
    (hno_large : ∀ r : ℕ, r.Prime → r ∣ m → r < 7)
    (_hRm : PisanoRet m m) (h24m : 24 ∣ m) :
    ∃ lambda : ℕ, 0 < lambda ∧ m = 24 * 5 ^ (lambda - 1) := by
  have hm_ne0 : m ≠ 0 := by omega
  have hm_pos : 0 < m := by omega
  obtain ⟨a, m1, h2m1, hm_eq1⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm_ne0 2 (by norm_num : 2 ≠ 1)
  have hm1_ne0 : m1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm_eq1
    exact hm_ne0 hm_eq1
  have hm1_pos : 0 < m1 := by omega
  obtain ⟨b, m2, h3m2, hm_eq2⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm1_ne0 3 (by norm_num : 3 ≠ 1)
  have hm2_ne0 : m2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm_eq2
    exact hm1_ne0 hm_eq2
  have hm2_pos : 0 < m2 := by omega
  obtain ⟨c, w, h5w, hm_eq3⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm2_ne0 5 (by norm_num : 5 ≠ 1)
  have hw_ne0 : w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm_eq3
    exact hm2_ne0 hm_eq3
  have hw_pos : 0 < w := by omega
  have hm_eq_all : m = 2 ^ a * 3 ^ b * 5 ^ c * w := by
    rw [hm_eq1, hm_eq2, hm_eq3]
    ring
  have hw_dvd_m2 : w ∣ m2 := ⟨5 ^ c, by rw [hm_eq3]; ring⟩
  have hm2_dvd_m1 : m2 ∣ m1 := ⟨3 ^ b, by rw [hm_eq2]; ring⟩
  have hm1_dvd_m : m1 ∣ m := ⟨2 ^ a, by rw [hm_eq1]; ring⟩
  have hw_dvd_m : w ∣ m := hw_dvd_m2.trans (hm2_dvd_m1.trans hm1_dvd_m)
  have h2w : ¬ 2 ∣ w := by
    intro h2w'
    have h2m2' : 2 ∣ m2 := h2w'.trans hw_dvd_m2
    have h2m1' : 2 ∣ m1 := h2m2'.trans hm2_dvd_m1
    exact h2m1 h2m1'
  have h3w : ¬ 3 ∣ w := by
    intro h3w'
    have h3m2' : 3 ∣ m2 := h3w'.trans hw_dvd_m2
    exact h3m2 h3m2'
  have hw_eq1 : w = 1 := by
    by_contra hw_ne1
    have hw_gt1 : 1 < w := by omega
    obtain ⟨q, hq, hq_w⟩ := Nat.exists_prime_and_dvd hw_ne1
    have hq_m : q ∣ m := hq_w.trans hw_dvd_m
    have hq2 : q ≠ 2 := fun heq => h2w (heq ▸ hq_w)
    have hq3 : q ≠ 3 := fun heq => h3w (heq ▸ hq_w)
    have hq5 : q ≠ 5 := fun heq => h5w (heq ▸ hq_w)
    have hq7 : 7 ≤ q := seven_le_of_prime_ne_235 hq hq2 hq3 hq5
    have hq_lt7 : q < 7 := hno_large q hq hq_m
    omega
  have hm_eq_235 : m = 2 ^ a * 3 ^ b * 5 ^ c := by
    rw [hm_eq_all, hw_eq1, mul_one]
  have h8m : 8 ∣ m := by
    have h8_24 : 8 ∣ 24 := by norm_num
    exact h8_24.trans h24m
  have h3m : 3 ∣ m := by
    have h3_24 : 3 ∣ 24 := by norm_num
    exact h3_24.trans h24m
  have ha3 : 3 ≤ a := by
    have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8eq] at h8m
    have hcop23 : Nat.Coprime (2 ^ 3) m1 :=
      (Nat.prime_two.coprime_pow_of_not_dvd h2m1).symm
    have h23_dvd_pow : 2 ^ 3 ∣ 2 ^ a := by
      have h := hcop23.dvd_of_dvd_mul_right (by rwa [hm_eq1] at h8m)
      exact h
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h23_dvd_pow
  have hb1 : 1 ≤ b := by
    have hcop32a : Nat.Coprime 3 (2 ^ a) := (by decide : Nat.Coprime 3 2).pow_right a
    have h3m1 : 3 ∣ m1 := hcop32a.dvd_of_dvd_mul_left (by rwa [hm_eq1] at h3m)
    have hcop3m2 : Nat.Coprime 3 m2 :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr h3m2
    have h3_dvd_pow : 3 ∣ 3 ^ b := hcop3m2.dvd_of_dvd_mul_right
      (by rwa [hm_eq2] at h3m1)
    have h3eq : (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
    rw [h3eq] at h3_dvd_pow
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h3_dvd_pow
  have ha_eq3 : a = 3 := by
    by_contra hne
    have ha4 : 4 ≤ a := by omega
    have ha_eq : a = (a - 1) + 1 := by omega
    have hpow2a : 2 ^ a = 2 ^ (a - 1) * 2 := by conv_lhs => rw [ha_eq, pow_succ]
    have hmr_eq : m / 2 = 2 ^ (a - 1) * 3 ^ b * 5 ^ c := by
      have hmeq : 2 ^ a * 3 ^ b * 5 ^ c = (2 ^ (a - 1) * 3 ^ b * 5 ^ c) * 2 := by
        rw [hpow2a]
        ring
      rw [hm_eq_235, hmeq]
      exact Nat.mul_div_cancel _ (by norm_num)
    have hR2 : PisanoRet (2 ^ a) (m / 2) := by
      have hW2 := pisanoRet_pow_two a (by omega : 1 ≤ a)
      have hb_eq : b = (b - 1) + 1 := by omega
      have hpow3b : 3 ^ b = 3 ^ (b - 1) * 3 := by conv_lhs => rw [hb_eq, pow_succ]
      have hdvd2 : 3 * 2 ^ (a - 1) ∣ m / 2 := by
        rw [hmr_eq, hpow3b]
        exact ⟨3 ^ (b - 1) * 5 ^ c, by ring⟩
      obtain ⟨k2, hk2⟩ := hdvd2
      have heq2 : m / 2 = k2 * (3 * 2 ^ (a - 1)) := by rw [hk2, mul_comm]
      rw [heq2]
      exact pisanoRet_mul (2 ^ a) _ k2 hW2
    have hR3 : PisanoRet (3 ^ b) (m / 2) := by
      have hW3 := pisanoRet_pow_three b hb1
      have h8dvd : 8 ∣ 2 ^ (a - 1) := by
        have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
        rw [h8eq]
        exact Nat.pow_dvd_pow 2 (by omega : 3 ≤ a - 1)
      have h3dvd : 3 ^ (b - 1) ∣ 3 ^ b := Nat.pow_dvd_pow 3 (Nat.sub_le b 1)
      have hdvd3 : 8 * 3 ^ (b - 1) ∣ 2 ^ (a - 1) * 3 ^ b :=
        Nat.mul_dvd_mul h8dvd h3dvd
      have hmid : 2 ^ (a - 1) * 3 ^ b ∣ m / 2 := by
        rw [hmr_eq]
        exact dvd_mul_right _ _
      have hdvd3' : 8 * 3 ^ (b - 1) ∣ m / 2 := hdvd3.trans hmid
      obtain ⟨k3, hk3⟩ := hdvd3'
      have heq3 : m / 2 = k3 * (8 * 3 ^ (b - 1)) := by rw [hk3, mul_comm]
      rw [heq3]
      exact pisanoRet_mul (3 ^ b) _ k3 hW3
    have hR5 : PisanoRet (5 ^ c) (m / 2) := by
      rcases Nat.eq_zero_or_pos c with rfl | hc_pos
      · simpa using pisanoRet_one (m / 2)
      · have hW5 := pisanoRet_pow_five c
        have h4dvd : 4 ∣ 2 ^ (a - 1) := by
          have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [h4eq]
          exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ a - 1)
        have hdvd5 : 4 * 5 ^ c ∣ 2 ^ (a - 1) * 5 ^ c :=
          Nat.mul_dvd_mul h4dvd (dvd_refl _)
        have hmid5 : 2 ^ (a - 1) * 5 ^ c ∣ m / 2 := by
          rw [hmr_eq]
          exact ⟨3 ^ b, by ring⟩
        have hdvd5' : 4 * 5 ^ c ∣ m / 2 := hdvd5.trans hmid5
        obtain ⟨k5, hk5⟩ := hdvd5'
        have heq5 : m / 2 = k5 * (4 * 5 ^ c) := by rw [hk5, mul_comm]
        rw [heq5]
        exact pisanoRet_mul (5 ^ c) _ k5 hW5
    have hcop23 : Nat.Coprime (2 ^ a) (3 ^ b) :=
      (by decide : Nat.Coprime 2 3).pow a b
    have hcop25 : Nat.Coprime (2 ^ a) (5 ^ c) :=
      (by decide : Nat.Coprime 2 5).pow a c
    have hcop35 : Nat.Coprime (3 ^ b) (5 ^ c) :=
      (by decide : Nat.Coprime 3 5).pow b c
    have hcop23_5 : Nat.Coprime (2 ^ a * 3 ^ b) (5 ^ c) :=
      Nat.Coprime.mul_left hcop25 hcop35
    have hR23 : PisanoRet (2 ^ a * 3 ^ b) (m / 2) :=
      (pisanoRet_coprime_mul (2 ^ a) (3 ^ b) (m / 2) hcop23).mpr ⟨hR2, hR3⟩
    have hRall : PisanoRet ((2 ^ a * 3 ^ b) * 5 ^ c) (m / 2) :=
      (pisanoRet_coprime_mul (2 ^ a * 3 ^ b) (5 ^ c) (m / 2) hcop23_5).mpr
        ⟨hR23, hR5⟩
    have heqM : (2 ^ a * 3 ^ b) * 5 ^ c = m := by rw [hm_eq_235]
    have hRm2 : PisanoRet m (m / 2) := heqM ▸ hRall
    have hm_dvd : m ∣ m / 2 := (hiff (m / 2)).mp hRm2
    have hmr_pos : 0 < m / 2 := by
      rw [hmr_eq]
      exact Nat.mul_pos (Nat.mul_pos (pow_pos (by norm_num) _)
        (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
    have hle : m ≤ m / 2 := Nat.le_of_dvd hmr_pos hm_dvd
    have hlt : m / 2 < m := Nat.div_lt_self hm_pos (by norm_num : 1 < 2)
    omega
  have hb_eq1 : b = 1 := by
    by_contra hne
    have hb2 : 2 ≤ b := by omega
    have hb_eq : b = (b - 1) + 1 := by omega
    have hpow3b : 3 ^ b = 3 ^ (b - 1) * 3 := by conv_lhs => rw [hb_eq, pow_succ]
    have hmr_eq : m / 3 = 2 ^ a * 3 ^ (b - 1) * 5 ^ c := by
      have hmeq : 2 ^ a * 3 ^ b * 5 ^ c = (2 ^ a * 3 ^ (b - 1) * 5 ^ c) * 3 := by
        rw [hpow3b]
        ring
      rw [hm_eq_235, hmeq]
      exact Nat.mul_div_cancel _ (by norm_num)
    have hR2 : PisanoRet (2 ^ a) (m / 3) := by
      have hW2 := pisanoRet_pow_two a (by omega : 1 ≤ a)
      have ha_eq : a = (a - 1) + 1 := by omega
      have hpow2a : 2 ^ a = 2 ^ (a - 1) * 2 := by
        conv_lhs => rw [ha_eq, pow_succ]
      have h3dvd : 3 ∣ 3 ^ (b - 1) := by
        have hb1' : 1 ≤ b - 1 := by omega
        have h3eq : (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
        rw [h3eq]
        exact Nat.pow_dvd_pow 3 hb1'
      have h2dvd : 2 ^ (a - 1) ∣ 2 ^ a := Nat.pow_dvd_pow 2 (Nat.sub_le a 1)
      have hdvd2 : 3 * 2 ^ (a - 1) ∣ 3 ^ (b - 1) * 2 ^ a :=
        Nat.mul_dvd_mul h3dvd h2dvd
      have hmid : 3 ^ (b - 1) * 2 ^ a ∣ m / 3 := by
        rw [hmr_eq]
        exact ⟨5 ^ c, by ring⟩
      have hdvd2' : 3 * 2 ^ (a - 1) ∣ m / 3 := hdvd2.trans hmid
      obtain ⟨k2, hk2⟩ := hdvd2'
      have heq2 : m / 3 = k2 * (3 * 2 ^ (a - 1)) := by rw [hk2, mul_comm]
      rw [heq2]
      exact pisanoRet_mul (2 ^ a) _ k2 hW2
    have hR3 : PisanoRet (3 ^ b) (m / 3) := by
      have hW3 := pisanoRet_pow_three b hb1
      have h8dvd : 8 ∣ 2 ^ a := by
        have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
        rw [h8eq]
        exact Nat.pow_dvd_pow 2 ha3
      have hdvd3 : 8 * 3 ^ (b - 1) ∣ 2 ^ a * 3 ^ (b - 1) :=
        Nat.mul_dvd_mul h8dvd (dvd_refl _)
      have hmid : 2 ^ a * 3 ^ (b - 1) ∣ m / 3 := by
        rw [hmr_eq]
        exact ⟨5 ^ c, by ring⟩
      have hdvd3' : 8 * 3 ^ (b - 1) ∣ m / 3 := hdvd3.trans hmid
      obtain ⟨k3, hk3⟩ := hdvd3'
      have heq3 : m / 3 = k3 * (8 * 3 ^ (b - 1)) := by rw [hk3, mul_comm]
      rw [heq3]
      exact pisanoRet_mul (3 ^ b) _ k3 hW3
    have hR5 : PisanoRet (5 ^ c) (m / 3) := by
      rcases Nat.eq_zero_or_pos c with rfl | hc_pos
      · simpa using pisanoRet_one (m / 3)
      · have hW5 := pisanoRet_pow_five c
        have h4dvd : 4 ∣ 2 ^ a := by
          have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [h4eq]
          exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ a)
        have hdvd5 : 4 * 5 ^ c ∣ 2 ^ a * 5 ^ c :=
          Nat.mul_dvd_mul h4dvd (dvd_refl _)
        have hmid5 : 2 ^ a * 5 ^ c ∣ m / 3 := by
          rw [hmr_eq]
          exact ⟨3 ^ (b - 1), by ring⟩
        have hdvd5' : 4 * 5 ^ c ∣ m / 3 := hdvd5.trans hmid5
        obtain ⟨k5, hk5⟩ := hdvd5'
        have heq5 : m / 3 = k5 * (4 * 5 ^ c) := by rw [hk5, mul_comm]
        rw [heq5]
        exact pisanoRet_mul (5 ^ c) _ k5 hW5
    have hcop23 : Nat.Coprime (2 ^ a) (3 ^ b) :=
      (by decide : Nat.Coprime 2 3).pow a b
    have hcop25 : Nat.Coprime (2 ^ a) (5 ^ c) :=
      (by decide : Nat.Coprime 2 5).pow a c
    have hcop35 : Nat.Coprime (3 ^ b) (5 ^ c) :=
      (by decide : Nat.Coprime 3 5).pow b c
    have hcop23_5 : Nat.Coprime (2 ^ a * 3 ^ b) (5 ^ c) :=
      Nat.Coprime.mul_left hcop25 hcop35
    have hR23 : PisanoRet (2 ^ a * 3 ^ b) (m / 3) :=
      (pisanoRet_coprime_mul (2 ^ a) (3 ^ b) (m / 3) hcop23).mpr ⟨hR2, hR3⟩
    have hRall : PisanoRet ((2 ^ a * 3 ^ b) * 5 ^ c) (m / 3) :=
      (pisanoRet_coprime_mul (2 ^ a * 3 ^ b) (5 ^ c) (m / 3) hcop23_5).mpr
        ⟨hR23, hR5⟩
    have heqM : (2 ^ a * 3 ^ b) * 5 ^ c = m := by rw [hm_eq_235]
    have hRm3 : PisanoRet m (m / 3) := heqM ▸ hRall
    have hm_dvd : m ∣ m / 3 := (hiff (m / 3)).mp hRm3
    have hmr_pos : 0 < m / 3 := by
      rw [hmr_eq]
      exact Nat.mul_pos (Nat.mul_pos (pow_pos (by norm_num) _)
        (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
    have hle : m ≤ m / 3 := Nat.le_of_dvd hmr_pos hm_dvd
    have hlt : m / 3 < m := Nat.div_lt_self hm_pos (by norm_num : 1 < 3)
    omega
  have hm_final : m = 24 * 5 ^ c := by
    rw [hm_eq_all, ha_eq3, hb_eq1, hw_eq1]
    ring
  exact ⟨c + 1, Nat.succ_pos c, by rw [Nat.add_sub_cancel]; exact hm_final⟩

/-- No prime `≥ 7` divides a fixed point. -/
private theorem no_large_prime_of_fixed (m : ℕ) (hm : 1 < m)
    (hiff : ∀ t : ℕ, PisanoRet m t ↔ m ∣ t) (r : ℕ) (hr : r.Prime)
    (hrm : r ∣ m) : r < 7 := by
  by_contra hlt
  have hr7_0 : 7 ≤ r := by omega
  have hm_ne0 : m ≠ 0 := by omega
  have hnonempty : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hm
  set R := m.primeFactors.max' hnonempty with hR_def
  have hR_mem : R ∈ m.primeFactors := Finset.max'_mem _ _
  have hR_prime : R.Prime := Nat.prime_of_mem_primeFactors hR_mem
  have hR_dvd : R ∣ m := Nat.dvd_of_mem_primeFactors hR_mem
  have hr_mem : r ∈ m.primeFactors := hr.mem_primeFactors hrm hm_ne0
  have hle_R : r ≤ R := Finset.le_max' _ _ hr_mem
  have hR7 : 7 ≤ R := by omega
  obtain ⟨e, u, hr_u, hm_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm_ne0 R (by omega : R ≠ 1)
  have he_pos : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · have hmu : m = u := by simpa using hm_eq
      have hR_u : R ∣ u := hmu ▸ hR_dvd
      exact absurd hR_u hr_u
    · exact hpos
  have hu_pos : 0 < u := by
    by_contra h
    have hu0 : u = 0 := by omega
    rw [hu0, mul_zero] at hm_eq
    omega
  have hu_lt : ∀ q : ℕ, q.Prime → q ∣ u → q < R := by
    intro q hq hqdvd
    have hu_dvd_m : u ∣ m := ⟨R ^ e, by rw [hm_eq]; ring⟩
    have hq_m : q ∣ m := hqdvd.trans hu_dvd_m
    have hq_mem : q ∈ m.primeFactors := hq.mem_primeFactors hq_m hm_ne0
    have hle_q : q ≤ R := Finset.le_max' _ _ hq_mem
    have hne : q ≠ R := fun heq => hr_u (heq ▸ hqdvd)
    omega
  have hcop : Nat.Coprime (R ^ e) u :=
    (hR_prime.coprime_pow_of_not_dvd hr_u).symm
  obtain ⟨W, hR_W, hr_W⟩ := exists_W_of_lt hR_prime hR7 u hu_pos hu_lt
  have hR0 := pisanoRet_prime_pow_odd hR_prime (by omega) (by omega) e he_pos
  have hR_r : PisanoRet (R ^ e) ((R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W) := by
    have heq : (R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W
        = W * (R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) := mul_comm _ _
    rw [heq]
    exact pisanoRet_mul (R ^ e) _ W hR0
  have hR_u : PisanoRet u ((R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W) :=
    pisanoRet_mul u W (R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) hR_W
  have hR_N : PisanoRet (R ^ e * u)
      ((R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W) :=
    (pisanoRet_coprime_mul (R ^ e) u _ hcop).mpr ⟨hR_r, hR_u⟩
  have hR_m_N : PisanoRet m ((R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W) :=
    hm_eq.symm ▸ hR_N
  have hm_dvd_N : m ∣ (R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W :=
    (hiff _).mp hR_m_N
  have hr_pow_dvd_m : R ^ e ∣ m := ⟨u, hm_eq⟩
  have hr_pow_dvd_N : R ^ e ∣ (R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W :=
    hr_pow_dvd_m.trans hm_dvd_N
  have he_eq : e = (e - 1) + 1 := by omega
  have hr_e_eq : R ^ e = R ^ (e - 1) * R := by conv_lhs => rw [he_eq, pow_succ]
  have hN_eq : (R ^ (e - 1) * ((R - 1) ^ 2 * (R + 1))) * W
      = R ^ (e - 1) * (((R - 1) ^ 2 * (R + 1)) * W) := by ring
  rw [hr_e_eq, hN_eq] at hr_pow_dvd_N
  have hR_dvd : R ∣ ((R - 1) ^ 2 * (R + 1)) * W :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hR_prime.pos (e - 1)) hr_pow_dvd_N
  rcases (hR_prime.dvd_mul).mp hR_dvd with h | hW
  · rcases (hR_prime.dvd_mul).mp h with hsub | hsucc
    · have hRm1 : R ∣ R - 1 := hR_prime.dvd_of_dvd_pow hsub
      have hpos : 0 < R - 1 := by
        have h2 : 2 ≤ R := hR_prime.two_le
        omega
      have hle : R ≤ R - 1 := Nat.le_of_dvd hpos hRm1
      omega
    · have hRr : R ∣ R := dvd_refl R
      have hR1 : R ∣ (R + 1) - R := Nat.dvd_sub hsucc hRr
      have heq1 : (R + 1) - R = 1 := by omega
      rw [heq1] at hR1
      have hEq : R = 1 := Nat.dvd_one.mp hR1
      omega
  · exact absurd hW hr_W

/-- **Fulton–Morris theorem on Pisano periods equal to the modulus.** Write $F_t$ for the $t$-th
Fibonacci number. Let $m > 1$ be a natural number and let $\pi$ be a positive integer with
$F_\pi \equiv 0 \pmod{m}$ and $F_{\pi+1} \equiv 1 \pmod{m}$ such that $\pi \le t$ for every
positive integer $t$ with $F_t \equiv 0 \pmod{m}$ and $F_{t+1} \equiv 1 \pmod{m}$; that is, $\pi$
is the Pisano period of $m$. Then $\pi = m$ if and only if $m = 24 \cdot 5^{\lambda - 1}$ for some
integer $\lambda \ge 1$.

Proves `Wanted` entry `fulton_morris_pisano_fixed_point`.

Source: Amirali Fatehizadeh and Daniel Yaqubi, "Average of the Fibonacci
Numbers," Journal of Integer Sequences 25 (2022), Article 22.2.6, live TeX at
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Yaqubi/yaq6.tex`, file SHA-256
`460e70d342c78a6138fb5662d3463e293a93f52e776e0bef4489d30066b10f79`; exact
definition-and-theorem span lines 177–189, SHA-256
`f59a3e5fc68d0b7b406d75db1e7b38743d1a7392825ac9ec60242c199024da9a`. The theorem is
attributed there to John Fulton and William Morris, "On arithmetical functions related
to the Fibonacci numbers," Acta Arithmetica 16 (1969), 105–110,
DOI 10.4064/aa-16-2-105-110.
-/
theorem fulton_morris_pisano_fixed_point
    (m period : ℕ) (hm : 1 < m) (hperiod : 0 < period)
    (hreturn : Nat.ModEq m (Nat.fib period) 0 ∧
      Nat.ModEq m (Nat.fib (period + 1)) 1)
    (hleast : ∀ t : ℕ, 0 < t →
      Nat.ModEq m (Nat.fib t) 0 → Nat.ModEq m (Nat.fib (t + 1)) 1 →
      period ≤ t) :
    period = m ↔ ∃ lambda : ℕ, 0 < lambda ∧ m = 24 * 5 ^ (lambda - 1) := by
  have hreturn' : PisanoRet m period := hreturn
  have hleast' : ∀ t : ℕ, 0 < t → PisanoRet m t → period ≤ t := by
    intro t hpos hRt
    exact hleast t hpos hRt.1 hRt.2
  constructor
  · intro hper_eq
    have hsymm := hper_eq.symm
    subst hsymm
    have hiff : ∀ t : ℕ, PisanoRet m t ↔ m ∣ t :=
      pisanoRet_iff_dvd m m hperiod hreturn' hleast'
    have hno_large : ∀ r : ℕ, r.Prime → r ∣ m → r < 7 := by
      intro r hr hrm
      exact no_large_prime_of_fixed m hm hiff r hr hrm
    have h24m : 24 ∣ m := dvd_24_of_fixed m hm hno_large hreturn'
    exact exists_lambda_of_fixed m hm hiff hno_large hreturn' h24m
  · rintro ⟨lambda, hlam_pos, hm_eq⟩
    exact period_eq_of_form m period (lambda - 1) hm hperiod hreturn' hleast' hm_eq

end
end MetaMathlibExt
