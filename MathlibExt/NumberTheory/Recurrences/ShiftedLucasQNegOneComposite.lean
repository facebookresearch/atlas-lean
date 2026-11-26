/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Insert
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Composite shifts of the Lucas sequence with $Q = -1$

The proof uses finite covers of the indices by congruences. For the fixed parameters, a
modular recurrence checks the published shifts over one common period. For the remaining
parameters, polynomial congruences certify the cycles and the Chinese remainder theorem
combines the shifts prescribed by the cover.
-/

namespace MetaMathlibExt

namespace ShiftedLucasQNegOneComposite

private abbrev u (P : ℤ) := lucasU ⟨P, -1, by decide⟩

private theorem u_add_two (P : ℤ) (n : ℕ) : u P (n + 2) = P * u P (n + 1) + u P n := by
  simp only [u, lucasU_add_two, neg_mul, one_mul, sub_neg_eq_add]

private theorem u_nonneg {P : ℤ} (hP : 1 ≤ P) (n : ℕ) : 0 ≤ u P n := by
  induction n using Nat.twoStepInduction with
  | zero => exact le_refl 0
  | one => exact zero_le_one
  | more n ha hb =>
    rw [u_add_two]
    exact add_nonneg (mul_nonneg (by omega) hb) ha

private theorem periodic_of_return {P q : ℤ} {t : ℕ}
    (h₀ : u P t ≡ 0 [ZMOD q]) (h₁ : u P (t + 1) ≡ 1 [ZMOD q]) :
    Function.Periodic (fun n => u P n % q) t := by
  intro n
  change u P (n + t) ≡ u P n [ZMOD q]
  induction n using Nat.twoStepInduction with
  | zero => simpa only [Nat.zero_add, u, lucasU] using h₀
  | one =>
    rw [Nat.add_comm 1 t]
    exact h₁
  | more n ih₀ ih₁ =>
    rw [Nat.add_right_comm n 2 t, u_add_two, u_add_two, Nat.add_right_comm n t 1]
    exact (ih₁.mul_left P).add ih₀

private def offset (d : Fin 3) : ℤ := (d.val : ℤ) - 1

private theorem offset_surj {d : ℤ} (hd : d ∈ ({-1, 0, 1} : Set ℤ)) :
    ∃ i : Fin 3, offset i = d := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

private def GoodShift (P K : ℤ) : Prop :=
  ∀ n : ℕ, ∀ d : Fin 3, ∃ q : ℤ, 1 < q ∧ q < K - 1 ∧ q ∣ u P n + K + offset d

private theorem goodShift_composite {P K : ℤ} (hP : 1 ≤ P) (h : GoodShift P K) :
    0 < K ∧ ∀ n : ℕ, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
      1 < u P n + K + d ∧ ¬ (u P n + K + d).natAbs.Prime := by
  obtain ⟨q, hq, hqK, _⟩ := h 0 0
  refine ⟨by omega, fun n d hd => ?_⟩
  obtain ⟨i, rfl⟩ := offset_surj hd
  obtain ⟨m, hm, hmK, hdiv⟩ := h n i
  have hlo : (-1 : ℤ) ≤ offset i := by simp [offset]
  have hlt : m < u P n + K + offset i := by linarith [u_nonneg hP n]
  exact ⟨by omega, Nat.not_prime_of_dvd_of_lt (Int.natAbs_dvd_natAbs.mpr hdiv)
    (by omega) (by omega)⟩

section FixedParameters

private def nextPair (P m : ℤ) (ab : ℤ × ℤ) : ℤ × ℤ :=
  (ab.2, (P * ab.2 + ab.1) % m)

private def residuePair (P m : ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => nextPair P m (residuePair P m n)

private theorem residuePair_correct (P m : ℤ) (n : ℕ) :
    (residuePair P m n).1 ≡ u P n [ZMOD m] ∧
      (residuePair P m n).2 ≡ u P (n + 1) [ZMOD m] := by
  induction n with
  | zero => exact ⟨Int.ModEq.rfl, Int.ModEq.rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [u_add_two]
    exact (Int.mod_modEq _ _).trans ((ih.2.mul_left P).add ih.1)

private def coveredAt (K : ℤ) (qs : List ℤ) (a : ℤ) : Bool :=
  (List.finRange 3).all fun d =>
    qs.any fun q => decide (1 < q ∧ q < K - 1) && ((a + K + offset d) % q == 0)

private def checkCover (P K : ℤ) (qs : List ℤ) : ℕ → ℤ × ℤ → Bool
  | 0, _ => true
  | t + 1, ab => coveredAt K qs ab.1 && checkCover P K qs t (nextPair P qs.prod ab)

private theorem checkCover_at {P K : ℤ} {qs : List ℤ} {t n : ℕ}
    (h : checkCover P K qs t (residuePair P qs.prod n) = true) {r : ℕ} (hr : r < t) :
    coveredAt K qs (residuePair P qs.prod (n + r)).1 = true := by
  induction t generalizing n r with
  | zero => omega
  | succ t ih =>
    rw [checkCover, Bool.and_eq_true] at h
    cases r with
    | zero => simpa only [Nat.add_zero] using h.1
    | succ r =>
      simpa only [Nat.succ_add, Nat.add_succ] using ih (n := n + 1) h.2 (by omega : r < t)

private theorem fixed_cover {P K : ℤ} {qs : List ℤ} {t : ℕ} (ht : 0 < t)
    (hperiod : residuePair P qs.prod t = (0, 1))
    (hcover : checkCover P K qs t (0, 1) = true) : GoodShift P K := by
  have hres := residuePair_correct P qs.prod t
  rw [hperiod] at hres
  have hper := periodic_of_return hres.1.symm hres.2.symm
  intro n d
  have hr := checkCover_at (n := 0) hcover (Nat.mod_lt n ht)
  rw [Nat.zero_add, coveredAt, List.all_eq_true] at hr
  have hh := hr d (by simp)
  rw [List.any_eq_true] at hh
  obtain ⟨q, hq, hh⟩ := hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
  refine ⟨q, hh.1.1, hh.1.2, ?_⟩
  have hc := ((residuePair_correct P qs.prod (n % t)).1.trans (hper.map_mod_nat n)).of_dvd
    (List.dvd_prod hq)
  have hm := (hc.add_right K).add_right (offset d)
  exact Int.modEq_zero_iff_dvd.mp (hm.symm.trans (by simpa [Int.ModEq] using hh.2))

-- Tables 7–11: each list is checked at its common period, not at arbitrary indices.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The Fibonacci certificate checks all 1440 indices using kernel reduction.
private theorem fixed_one : GoodShift 1 305634298839076198110201000141426680099130790997545994766 :=
  fixed_cover (qs := [2, 3, 5, 7, 11, 17, 19, 23, 31, 41, 47, 61, 107, 181, 241, 541,
    1103, 1601, 2161, 2521, 3041, 8641, 20641, 103681, 109441]) (t := 1440)
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem fixed_two : GoodShift 2 100784662201557 :=
  fixed_cover (qs := [2, 3, 5, 7, 11, 19, 29, 31, 41, 59, 269, 601]) (t := 120)
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem fixed_three : GoodShift 3 353531805205404 :=
  fixed_cover (qs := [2, 3, 5, 11, 19, 59, 61, 109, 131, 211, 739]) (t := 120)
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem fixed_four : GoodShift 4 69411071167563 :=
  fixed_cover (qs := [2, 3, 5, 11, 17, 19, 31, 41, 61, 107, 181]) (t := 120)
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem fixed_twentyTwo : GoodShift 22 142395 :=
  fixed_cover (qs := [2, 3, 5, 11, 97, 131]) (t := 24)
    (by decide) (by decide +kernel) (by decide +kernel)

end FixedParameters

section SymbolicCycles

/-- Coefficients of the residue polynomials, in increasing degree. The cycles in Section 3
of the source have degree at most three. -/
private structure Coeff where
  c₀ : ℤ
  c₁ : ℤ := 0
  c₂ : ℤ := 0
  c₃ : ℤ := 0
  deriving DecidableEq, Inhabited

private def Coeff.const (a : ℤ) : Coeff := { c₀ := a }
private def Coeff.x : Coeff := { c₀ := 0, c₁ := 1 }
private def Coeff.xSq : Coeff := { c₀ := 0, c₂ := 1 }
private def Coeff.add (a b : Coeff) : Coeff :=
  ⟨a.c₀ + b.c₀, a.c₁ + b.c₁, a.c₂ + b.c₂, a.c₃ + b.c₃⟩
private def Coeff.neg (a : Coeff) : Coeff := ⟨-a.c₀, -a.c₁, -a.c₂, -a.c₃⟩

private def Coeff.eval (P : ℤ) (a : Coeff) : ℤ :=
  a.c₀ + P * (a.c₁ + P * (a.c₂ + P * a.c₃))

private theorem Coeff.eval_add (P : ℤ) (a b : Coeff) :
    (a.add b).eval P = a.eval P + b.eval P := by
  simp only [Coeff.add, Coeff.eval]
  ring

private theorem Coeff.eval_neg (P : ℤ) (a : Coeff) : (a.neg).eval P = -a.eval P := by
  simp only [Coeff.neg, Coeff.eval]
  ring

private def residueAt (xs : List Coeff) (t n : ℕ) : Coeff := xs[n % t]?.getD (Coeff.const 0)

/-- The degree-four term of `X * b + a - c` is kept separately. -/
private def stepDifference (a b c : Coeff) : Coeff × ℤ :=
  (((⟨0, b.c₀, b.c₁, b.c₂⟩ : Coeff).add a).add c.neg, b.c₃)

private def evalWithLeading (P : ℤ) (g : Coeff × ℤ) : ℤ := g.1.eval P + P ^ 4 * g.2

private theorem eval_stepDifference (P : ℤ) (a b c : Coeff) :
    evalWithLeading P (stepDifference a b c) = P * b.eval P + a.eval P - c.eval P := by
  simp only [evalWithLeading, stepDifference, Coeff.add, Coeff.neg, Coeff.eval]
  ring

private def negative (g : Coeff × ℤ) : Coeff × ℤ := (g.1.neg, -g.2)

private theorem eval_negative (P : ℤ) (g : Coeff × ℤ) :
    evalWithLeading P (negative g) = -evalWithLeading P g := by
  simp only [evalWithLeading, negative, Coeff.eval_neg, mul_neg, neg_add]

/-- A symbolic cycle is certified by checking its start and each cyclic recurrence step.
The step differences in these cycles are zero or plus/minus the parent modulus. -/
private theorem symbolic_cycle (P q : ℤ) (xs : List Coeff) (t : ℕ) (ht : 0 < t)
    (g : Coeff × ℤ) (hq : q ∣ evalWithLeading P g)
    (h₀ : residueAt xs t 0 = Coeff.const 0) (h₁ : residueAt xs t 1 = Coeff.const 1)
    (hstep : ∀ i : Fin t, stepDifference (residueAt xs t i) (residueAt xs t (i + 1))
      (residueAt xs t (i + 2)) ∈ [(Coeff.const 0, 0), g, negative g]) (n : ℕ) :
    u P n ≡ (residueAt xs t n).eval P [ZMOD q] := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [h₀, Coeff.eval, Coeff.const, mul_zero, add_zero]; exact Int.ModEq.rfl
  | one => simp only [h₁, Coeff.eval, Coeff.const, mul_zero, add_zero]; exact Int.ModEq.rfl
  | more n ih₀ ih₁ =>
    have hh : stepDifference (residueAt xs t n) (residueAt xs t (n + 1))
        (residueAt xs t (n + 2)) ∈ [(Coeff.const 0, 0), g, negative g] := by
      simpa only [residueAt, Nat.mod_mod, Nat.mod_add_mod] using
        hstep ⟨n % t, Nat.mod_lt n ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    have hd : q ∣ evalWithLeading P (stepDifference (residueAt xs t n)
        (residueAt xs t (n + 1)) (residueAt xs t (n + 2))) := by
      rcases hh with h | h | h
      · simp [h, evalWithLeading, Coeff.eval, Coeff.const]
      · rwa [h]
      · simpa only [h, eval_negative, dvd_neg] using hq
    rw [u_add_two]
    refine ((ih₁.mul_left P).add ih₀).trans ?_
    exact Int.modEq_iff_dvd.mpr (by simpa only [eval_stepDifference, dvd_sub_comm] using hd)

private theorem u_modEq_param {P R q : ℤ} (h : P ≡ R [ZMOD q]) (n : ℕ) :
    u P n ≡ u R n [ZMOD q] := by
  induction n using Nat.twoStepInduction with
  | zero => exact Int.ModEq.rfl
  | one => exact Int.ModEq.rfl
  | more n ih₀ ih₁ => simpa only [u_add_two] using (h.mul ih₁).add ih₀

private def numericCycle (R q : ℤ) (t : ℕ) : List Coeff :=
  (List.range t).map fun i => Coeff.const (residuePair R q i).1

private theorem numeric_cycle {P R q : ℤ} {t : ℕ} (ht : 0 < t) (hP : P ≡ R [ZMOD q])
    (hturn : residuePair R q t = (0, 1)) (n : ℕ) :
    u P n ≡ (residueAt (numericCycle R q t) t n).eval P [ZMOD q] := by
  have h := residuePair_correct R q t
  rw [hturn] at h
  have per := periodic_of_return h.1.symm h.2.symm
  have hm := (residuePair_correct R q (n % t)).1.trans (per.map_mod_nat n)
  have hget : residueAt (numericCycle R q t) t n = Coeff.const (residuePair R q (n % t)).1 := by
    simp [residueAt, numericCycle, Nat.mod_lt _ ht]
  simp only [hget, Coeff.eval, Coeff.const, mul_zero, add_zero]
  exact (u_modEq_param hP n).trans hm.symm

/-- The seven types of modulus used in the symbolic tables. A parent integer may be replaced
by any of its positive divisors in the corresponding cycle. -/
private inductive Kind
  | two | three | linear | quadOne | quadTwo | quadThree | quartic
  deriving DecidableEq

private def Kind.period : Kind → ℕ
  | .two => 6
  | .three => 8
  | .linear => 2
  | .quadOne => 12
  | .quadTwo => 8
  | .quadThree => 6
  | .quartic => 24

private def Kind.parentCoeff : Kind → Coeff × ℤ
  | .two => (Coeff.const 2, 0)
  | .three => (Coeff.const 3, 0)
  | .linear => (Coeff.x, 0)
  | .quadOne => (⟨1, 0, 1, 0⟩, 0)
  | .quadTwo => (⟨2, 0, 1, 0⟩, 0)
  | .quadThree => (⟨3, 0, 1, 0⟩, 0)
  | .quartic => (⟨1, 0, 4, 0⟩, 1)

private def Kind.parent (b : Kind) (P : ℤ) : ℤ := evalWithLeading P b.parentCoeff

private theorem parent_two (P : ℤ) : Kind.two.parent P = 2 := by simp [Kind.parent,
  Kind.parentCoeff, evalWithLeading, Coeff.eval, Coeff.const]
private theorem parent_three (P : ℤ) : Kind.three.parent P = 3 := by simp [Kind.parent,
  Kind.parentCoeff, evalWithLeading, Coeff.eval, Coeff.const]
private theorem parent_linear (P : ℤ) : Kind.linear.parent P = P := by simp [Kind.parent,
  Kind.parentCoeff, evalWithLeading, Coeff.eval, Coeff.x]
private theorem parent_quadOne (P : ℤ) : Kind.quadOne.parent P = P ^ 2 + 1 := by
  simp only [Kind.parent, Kind.parentCoeff, evalWithLeading, Coeff.eval]; ring
private theorem parent_quadTwo (P : ℤ) : Kind.quadTwo.parent P = P ^ 2 + 2 := by
  simp only [Kind.parent, Kind.parentCoeff, evalWithLeading, Coeff.eval]; ring
private theorem parent_quadThree (P : ℤ) : Kind.quadThree.parent P = P ^ 2 + 3 := by
  simp only [Kind.parent, Kind.parentCoeff, evalWithLeading, Coeff.eval]; ring
private theorem parent_quartic (P : ℤ) : Kind.quartic.parent P = P ^ 4 + 4 * P ^ 2 + 1 := by
  simp only [Kind.parent, Kind.parentCoeff, evalWithLeading, Coeff.eval]; ring

open Coeff (const x xSq) in
private def Kind.cycle (r : Fin 6) : Kind → List Coeff
  | .two => numericCycle r.val 2 6
  | .three => numericCycle r.val 3 8
  | .linear => [const 0, const 1]
  | .quadOne => [const 0, const 1, x, const 0, x, const (-1), const 0, const (-1),
    x.neg, const 0, x.neg, const 1]
  | .quadTwo => [const 0, const 1, x, const (-1), const 0, const (-1), x.neg, const 1]
  | .quadThree => [const 0, const 1, x, const (-2), x.neg, const 1]
  | .quartic =>
    let a : Coeff := ⟨1, 0, 1, 0⟩
    let b : Coeff := ⟨0, 2, 0, 1⟩
    let c : Coeff := ⟨0, 2, 0, 0⟩
    [const 0, const 1, x, a, b, xSq.neg, c, xSq, b, a.neg, x, const (-1),
      const 0, const (-1), x.neg, a.neg, b.neg, xSq, c.neg, xSq.neg, b.neg, a, x.neg, const 1]

private theorem Kind.period_dvd (b : Kind) : b.period ∣ 24 := by cases b <;> decide

private theorem two_returns (r : Fin 6) : residuePair r.val 2 6 = (0, 1) := by
  have h : ∀ i : Fin 6, residuePair i.val 2 6 = (0, 1) := by decide +kernel
  exact h r

private theorem three_returns (r : Fin 6) : residuePair r.val 3 8 = (0, 1) := by
  have h : ∀ i : Fin 6, residuePair i.val 3 8 = (0, 1) := by decide +kernel
  exact h r

private theorem Kind.cycle_correct (b : Kind) {P q : ℤ} {r : Fin 6} (hP : P ≡ ↑r.val [ZMOD 6])
    (hq : q ∣ b.parent P) (n : ℕ) :
    u P n ≡ (residueAt (b.cycle r) b.period n).eval P [ZMOD q] := by
  cases b with
  | two =>
    rw [parent_two] at hq
    exact (numeric_cycle (by decide) (hP.of_dvd (by decide)) (two_returns r) n).of_dvd hq
  | three =>
    rw [parent_three] at hq
    exact (numeric_cycle (by decide) (hP.of_dvd (by decide)) (three_returns r) n).of_dvd hq
  | linear | quadOne | quadTwo | quadThree | quartic =>
    refine symbolic_cycle P q _ _ (by decide) _ hq rfl rfl ?_ n
    simp only [Kind.cycle, Kind.period, Kind.parentCoeff]
    decide +kernel

end SymbolicCycles

section SymbolicCovers

private def Kind.rank : Kind → ℕ
  | .two => 0
  | .three => 1
  | .linear => 2
  | .quadOne => 3
  | .quadTwo => 4
  | .quadThree => 5
  | .quartic => 6

private theorem Kind.rank_injective : Function.Injective Kind.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [Kind.rank]

private theorem no_shared_large_divisor {P q : ℤ} {a b : Kind} (hne : a ≠ b) (hq : 3 < q)
    (ha : q ∣ a.parent P) (hb : q ∣ b.parent P) : False := by
  wlog hab : a.rank < b.rank generalizing a b
  · have hnr : a.rank ≠ b.rank := fun h => hne (Kind.rank_injective h)
    exact this hne.symm hb ha (by omega)
  have noSmall (c : ℤ) (hc₀ : 0 < c) (hc₁ : c ≤ 3) (hd : q ∣ c) : False :=
    (not_le_of_gt (lt_of_le_of_lt hc₁ hq)) (Int.le_of_dvd hc₀ hd)
  have combination {x y c : ℤ} (hx : q ∣ x) (hy : q ∣ y) (a b : ℤ)
      (h : a * x + b * y = c) : q ∣ c :=
    h ▸ dvd_add (dvd_mul_of_dvd_right hx a) (dvd_mul_of_dvd_right hy b)
  cases a <;> cases b <;> norm_num [Kind.rank] at hab <;>
    simp only [parent_two, parent_three, parent_linear, parent_quadOne, parent_quadTwo,
      parent_quadThree, parent_quartic] at ha hb
  all_goals try exact noSmall 2 (by decide) (by decide) ha
  all_goals try exact noSmall 3 (by decide) (by decide) ha
  · exact noSmall 1 (by decide) (by decide) (combination ha hb (-P) 1 (by ring))
  · exact noSmall 2 (by decide) (by decide) (combination ha hb (-P) 1 (by ring))
  · exact noSmall 3 (by decide) (by decide) (combination ha hb (-P) 1 (by ring))
  · exact noSmall 1 (by decide) (by decide) (combination ha hb (-(P ^ 3 + 4 * P)) 1 (by ring))
  · exact noSmall 1 (by decide) (by decide) (combination ha hb (-1) 1 (by ring))
  · exact noSmall 2 (by decide) (by decide) (combination ha hb (-1) 1 (by ring))
  · exact noSmall 2 (by decide) (by decide) (combination ha hb (P ^ 2 + 3) (-1) (by ring))
  · exact noSmall 1 (by decide) (by decide) (combination ha hb (-1) 1 (by ring))
  · exact noSmall 3 (by decide) (by decide) (combination ha hb (P ^ 2 + 2) (-1) (by ring))
  · exact noSmall 2 (by decide) (by decide) (combination ha hb (P ^ 2 + 1) (-1) (by ring))

private def Kind.checkModulus : Kind → ℤ
  | .two => 2
  | .three => 3
  | _ => 0

private def Kind.modulusSize (b : Kind) (q : ℕ) : Prop :=
  match b with
  | .two => q = 2
  | .three => q = 3
  | _ => 3 < q

private def Kind.Suitable (b : Kind) (P : ℤ) (q : ℕ) : Prop :=
  q.Prime ∧ (q : ℤ) ∣ b.parent P ∧ b.modulusSize q

private theorem Kind.Suitable.dvd_checkModulus {b : Kind} {P : ℤ} {q : ℕ}
    (h : b.Suitable P q) : (q : ℤ) ∣ b.checkModulus := by
  have hs := h.2.2
  cases b <;> simp_all [Kind.modulusSize, Kind.checkModulus]

private theorem Kind.suitable_coprime {P : ℤ} {a b : Kind} {p q : ℕ}
    (ha : a.Suitable P p) (hb : b.Suitable P q) (hne : a ≠ b) : p.Coprime q := by
  refine (Nat.coprime_primes ha.1 hb.1).2 (fun h => ?_)
  subst q
  have hp : 3 < p := by
    have h₁ := ha.2.2
    have h₂ := hb.2.2
    cases a <;> cases b <;> simp_all [Kind.modulusSize]
  exact no_shared_large_divisor hne (by exact_mod_cast hp) ha.2.1 hb.2.1

/-- One row of the cover: a cycle and the residue prescribed for the shift. -/
private structure CoverRow where
  kind : Kind
  shift : Coeff
  deriving DecidableEq

private def Coeff.divisible (a : Coeff) (m : ℤ) : Bool :=
  a.c₀ % m == 0 && a.c₁ % m == 0 && a.c₂ % m == 0 && a.c₃ % m == 0

private theorem Coeff.dvd_eval {a : Coeff} {m : ℤ} (h : a.divisible m = true) (P : ℤ) :
    m ∣ a.eval P := by
  simp only [Coeff.divisible, Bool.and_eq_true, beq_iff_eq, ← Int.dvd_iff_emod_eq_zero] at h
  exact dvd_add h.1.1.1 (dvd_mul_of_dvd_right (dvd_add h.1.1.2
    (dvd_mul_of_dvd_right (dvd_add h.1.2 (dvd_mul_of_dvd_right h.2 P)) P)) P)

-- Modulus zero means that the sum is identically zero as a polynomial.
private def CoverRow.covers (row : CoverRow) (r : Fin 6) (n : ℕ) (d : Fin 3) : Bool :=
  let c := residueAt (row.kind.cycle r) row.kind.period n
  ((c.add row.shift).add (Coeff.const (offset d))).divisible row.kind.checkModulus

private theorem CoverRow.covers_correct {row : CoverRow} {P K : ℤ} {r : Fin 6} {n : ℕ}
    {d : Fin 3} {q : ℕ} (hP : P ≡ ↑r.val [ZMOD 6]) (hq : row.kind.Suitable P q)
    (hK : K ≡ row.shift.eval P [ZMOD q]) (hc : row.covers r (n % 24) d = true) :
    (q : ℤ) ∣ u P n + K + offset d := by
  have he := Coeff.dvd_eval hc P
  simp only [Coeff.eval_add] at he
  have ho : (Coeff.const (offset d)).eval P = offset d := by simp [Coeff.eval, Coeff.const]
  rw [ho] at he
  have hr : residueAt (row.kind.cycle r) row.kind.period (n % 24) =
      residueAt (row.kind.cycle r) row.kind.period n := by
    simp only [residueAt, Nat.mod_mod_of_dvd _ row.kind.period_dvd]
  rw [hr] at he
  exact Int.modEq_zero_iff_dvd.mp
    (((row.kind.cycle_correct hP hq.2.1 n).add hK).add_right (offset d) |>.trans
      (dvd_trans hq.dvd_checkModulus he).modEq_zero_int)

private theorem goodShift_of_symbolic_cover {P : ℤ} {r : Fin 6} (hP : P ≡ ↑r.val [ZMOD 6])
    (rows : List CoverRow) (hn : rows.Pairwise fun a b => a.kind ≠ b.kind)
    (hs : ∀ row ∈ rows, ∃ q, row.kind.Suitable P q)
    (hcover : ∀ (n : Fin 24) (d : Fin 3), rows.any (fun row => row.covers r n d) = true) :
    ∃ K, GoodShift P K := by
  let q (row : CoverRow) : ℕ := if h : row ∈ rows then Classical.choose (hs row h) else 1
  have hq : ∀ row ∈ rows, row.kind.Suitable P (q row) := by
    intro row hr
    simpa only [q, dite_eq_left hr] using Classical.choose_spec (hs row hr)
  have hpw : rows.Pairwise (fun a b => (q a).Coprime (q b)) :=
    hn.imp_of_mem fun ha hb hab => Kind.suitable_coprime (hq _ ha) (hq _ hb) hab
  let v (row : CoverRow) := (row.shift.eval P % q row).toNat
  let sol := Nat.chineseRemainderOfList v q rows hpw
  let M := (rows.map q).prod
  have hM : 0 < M := List.prod_pos (by simpa only [List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] using fun row hr => (hq row hr).1.pos)
  refine ⟨(sol.val : ℤ) + 3 * (M : ℤ), fun n d => ?_⟩
  obtain ⟨row, hr, hc⟩ := List.any_eq_true.mp (hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩ d)
  have hqM : q row ∣ M := List.dvd_prod (List.mem_map_of_mem hr)
  have hqle := Nat.le_of_dvd hM hqM
  have hqgt := (hq row hr).1.two_le
  refine ⟨q row, by omega, by omega, row.covers_correct hP (hq row hr) ?_ hc⟩
  have hcast : (v row : ℤ) = row.shift.eval P % q row :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hsol := Int.natCast_modEq_iff.mpr (sol.property row hr)
  rw [hcast] at hsol
  have hM0 : 3 * (M : ℤ) ≡ 0 [ZMOD q row] :=
    (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hqM) 3).modEq_zero_int
  simpa only [add_zero] using
    (hsol.trans (Int.mod_modEq _ _)).add hM0

open Coeff (const x xSq) in
/-- The shift residues from Tables 1–6, in the order of the seven modulus types. -/
private def publishedRows (r : Fin 6) : List CoverRow :=
  match r.val with
  | 0 => [⟨.two, const (-1)⟩, ⟨.three, const 0⟩, ⟨.quadOne, const (-1)⟩,
          ⟨.quadThree, const (-2)⟩]
  | 1 | 5 => [⟨.two, const 0⟩, ⟨.three, const 0⟩, ⟨.linear, const 0⟩,
              ⟨.quadOne, const 1⟩, ⟨.quadThree, const (-1)⟩, ⟨.quartic, xSq⟩]
  | 3 => [⟨.two, const 0⟩, ⟨.three, const 0⟩, ⟨.quadOne, const 1⟩, ⟨.quadTwo, const 0⟩,
          ⟨.quadThree, const (-1)⟩, ⟨.quartic, xSq⟩]
  | _ => [⟨.two, const 1⟩, ⟨.three, const 1⟩, ⟨.quadOne, const 1⟩, ⟨.quadTwo, const 0⟩,
          ⟨.quadThree, const 0⟩, ⟨.quartic, if r.val = 2 then x else x.neg⟩]

private theorem publishedRows_distinct (r : Fin 6) :
    (publishedRows r).Pairwise (fun a b => a.kind ≠ b.kind) := by
  have h : ∀ i : Fin 6, (publishedRows i).Pairwise (fun a b => a.kind ≠ b.kind) := by decide +kernel
  exact h r

private theorem publishedRows_cover (r : Fin 6) (n : Fin 24) (d : Fin 3) :
    (publishedRows r).any (fun row => row.covers r n d) = true := by
  have h : ∀ (i : Fin 6) (j : Fin 24) (k : Fin 3),
      (publishedRows i).any (fun row => row.covers i j k) = true := by decide +kernel
  exact h r n d

open Coeff (const xSq) in
/-- A replacement for Tables 5 and 6 when the linear modulus has a prime factor above three;
this cover does not need a divisor of `P^2 + 2` coprime with six. -/
private def evenRows : List CoverRow :=
  [⟨.two, const 1⟩, ⟨.three, const 0⟩, ⟨.linear, const 0⟩, ⟨.quadOne, const (-2)⟩,
    ⟨.quadThree, const (-2)⟩, ⟨.quartic, xSq⟩]

private theorem evenRows_cover {r : Fin 6} (hr : r = 2 ∨ r = 4) (n : Fin 24) (d : Fin 3) :
    evenRows.any (fun row => row.covers r n d) = true := by
  rcases hr with rfl | rfl
  · exact (by decide +kernel : ∀ (i : Fin 24) (j : Fin 3),
      evenRows.any (fun row => row.covers 2 i j) = true) n d
  · exact (by decide +kernel : ∀ (i : Fin 24) (j : Fin 3),
      evenRows.any (fun row => row.covers 4 i j) = true) n d

end SymbolicCovers

section ModulusSelection

private def LargePrimeFactor (m : ℕ) : Prop := ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ m

private theorem two_or_three_of_small_prime {q : ℕ} (hq : q.Prime) (h : q ≤ 3) :
    q = 2 ∨ q = 3 := by
  have := hq.two_le
  omega

private theorem largePrime_of_not_two_three {m : ℕ} (hm : 1 < m) (h₂ : ¬ 2 ∣ m) (h₃ : ¬ 3 ∣ m) :
    LargePrimeFactor m := by
  obtain ⟨q, hp, hq⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨q, hp, ?_, hq⟩
  by_contra! hs
  rcases two_or_three_of_small_prime hp hs with rfl | rfl
  · exact h₂ hq
  · exact h₃ hq

private theorem largePrime_of_remainder {m k : ℕ} (hm : k < m)
    (hr : m % (6 * k) = k ∨ m % (6 * k) = 5 * k) : LargePrimeFactor m := by
  let e := m / (6 * k)
  have lift (a : ℕ) (ha : a % 6 = 1 ∨ a % 6 = 5) (h : m = k * a) : LargePrimeFactor m := by
    have ha₁ : 1 < a := by
      by_contra! hle
      have hEq : a = 1 := by omega
      subst a
      simp_all
    obtain ⟨q, hq, hq₃, hdiv⟩ := largePrime_of_not_two_three ha₁ (by omega) (by omega)
    exact ⟨q, hq, hq₃, h ▸ dvd_mul_of_dvd_right hdiv k⟩
  have he : m % (6 * k) + (6 * k) * e = m := Nat.mod_add_div _ _
  rcases hr with h | h
  · apply lift (6 * e + 1) (by omega)
    rw [h] at he
    rw [← he]
    ring
  · apply lift (6 * e + 5) (by omega)
    rw [h] at he
    rw [← he]
    ring

private def Kind.parentNat (b : Kind) (p : ℕ) : ℕ :=
  match b with
  | .two => 2
  | .three => 3
  | .linear => p
  | .quadOne => p ^ 2 + 1
  | .quadTwo => p ^ 2 + 2
  | .quadThree => p ^ 2 + 3
  | .quartic => p ^ 4 + 4 * p ^ 2 + 1

private theorem Kind.cast_parentNat (b : Kind) (p : ℕ) : (b.parentNat p : ℤ) = b.parent p := by
  cases b <;> simp [Kind.parentNat, parent_two, parent_three, parent_linear, parent_quadOne,
    parent_quadTwo, parent_quadThree, parent_quartic]

private theorem Kind.parentNat_modEq {n a b : ℕ} (h : a ≡ b [MOD n]) (i : Kind) :
    i.parentNat a ≡ i.parentNat b [MOD n] := by
  cases i with
  | two | three => exact Nat.ModEq.rfl
  | linear => exact h
  | quadOne | quadTwo | quadThree => exact (h.pow 2).add (Nat.ModEq.refl _)
  | quartic => exact ((h.pow 4).add ((h.pow 2).mul_left 4)).add (Nat.ModEq.refl _)

/-- Factors of two and three removed from the parent moduli in Tables 1–6.
A zero means that the corresponding entry is not handled by a fixed normalization. -/
private def Kind.normalizer (b : Kind) (r : ℕ) : ℕ :=
  match b with
  | .two | .three => 0
  | .linear => if r = 1 ∨ r = 5 then 1 else 0
  | .quadOne => if r % 2 = 0 then 1 else 2
  | .quadTwo => if r = 3 then 1 else 0
  | .quadThree => (if r % 2 = 0 then 1 else 4) * (if r % 3 = 0 then 3 else 1)
  | .quartic => (if r % 2 = 0 then 1 else 2) * (if r % 3 = 0 then 1 else 3)

/-- Knowing the parameter modulo 72 determines all fixed normalizations. For every nonzero
normalizer `k`, the parent modulus is `k` times a unit modulo six. -/
private theorem normalization_table (b : Kind) (i : Fin 72) :
    let k := b.normalizer (i.val % 6)
    k ≠ 0 → 6 * k ∣ 72 ∧ (b.parentNat i.val % (6 * k) = k ∨
      b.parentNat i.val % (6 * k) = 5 * k) := by
  revert i
  cases b <;> decide +kernel

private theorem Kind.largePrime_of_normalizer (b : Kind) {p : ℕ} (hp : 4 < p)
    (hn : b.normalizer (p % 6) ≠ 0) : LargePrimeFactor (b.parentNat p) := by
  let k := b.normalizer (p % 6)
  have hr : p % 72 % 6 = p % 6 := Nat.mod_mod_of_dvd _ (by decide)
  have hrem := normalization_table b ⟨p % 72, Nat.mod_lt _ (by decide)⟩
  change (let k := b.normalizer (p % 72 % 6); k ≠ 0 → _) at hrem
  rw [hr] at hrem
  obtain ⟨hdiv, hmod⟩ := hrem hn
  have hc := (Kind.parentNat_modEq ((Nat.mod_modEq p 72).of_dvd hdiv) b).symm
  change b.parentNat p % (6 * k) = b.parentNat (p % 72) % (6 * k) at hc
  apply largePrime_of_remainder (k := k)
  swap
  · rw [hc]
    exact hmod
  have hsq : 25 ≤ p ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : 5 ≤ p) (by omega : 5 ≤ p)
  have hk : k ≤ 12 := by
    cases b <;> simp [k, Kind.normalizer] <;> split_ifs <;> omega
  cases b with
  | two | three => exact (hn rfl).elim
  | linear =>
    simp only [k, Kind.normalizer, Kind.parentNat] at hn ⊢
    split_ifs at * <;> omega
  | quadOne | quadTwo | quadThree | quartic => simp only [Kind.parentNat]; omega

private theorem prime_power_of_unique_factor {m q : ℕ} (hm : m ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ m → p = q) : m = q ^ m.factorization q := by
  apply Nat.eq_pow_of_factorization_eq_single hm
  ext p
  by_cases he : p = q
  · subst p
    simp
  · rw [Finsupp.single_eq_of_ne he]
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl fun hd => he (h p hp hd))
    · exact Or.inl hp

/-- If a power of three is one modulo 16, its exponent is a multiple of four,
so it is one modulo five as well. -/
private theorem three_pow_mod_five_of_mod_sixteen {e : ℕ} (h : 3 ^ e % 16 = 1) :
    3 ^ e % 5 = 1 := by
  have per (m : ℕ) (hm : (3 : ℕ) ^ 4 ≡ 1 [MOD m]) :
      Function.Periodic (fun k : ℕ => 3 ^ k % m) 4 := by
    intro k
    change (3 : ℕ) ^ (k + 4) ≡ 3 ^ k [MOD m]
    simpa only [pow_add, mul_one] using hm.mul_left (3 ^ k)
  have h₁ := (per 16 (by decide)).map_mod_nat e
  change 3 ^ (e % 4) % 16 = 3 ^ e % 16 at h₁
  rw [h] at h₁
  have hcheck : ∀ i : Fin 4, 3 ^ i.val % 16 = 1 → i.val = 0 := by decide +kernel
  have he : e % 4 = 0 := hcheck ⟨e % 4, Nat.mod_lt _ (by decide)⟩ h₁
  have h₂ := (per 5 (by decide)).map_mod_nat e
  change 3 ^ (e % 4) % 5 = 3 ^ e % 5 at h₂
  rw [he] at h₂
  exact h₂.symm

/-- The two even nonzero classes modulo six can use either the `P² + 2` row from the paper
or the replacement with a linear row. If both lack a prime above three, `P` is a power of
two and `(P² + 2)/2` is a power of three. Modulo 16 and five these are incompatible. -/
private theorem even_linear_factor {p : ℕ} (hp : 4 < p) (h₂ : p % 2 = 0) (h₃ : p % 3 ≠ 0)
    (hbL : ¬ LargePrimeFactor (p ^ 2 + 2)) : LargePrimeFactor p := by
  by_contra hpL
  let a := p.factorization 2
  have hpa : p = 2 ^ a := prime_power_of_unique_factor (by omega) fun q hq hdiv => by
    have hqsmall : q ≤ 3 := by_contra fun h => hpL ⟨q, hq, by omega, hdiv⟩
    rcases two_or_three_of_small_prime hq hqsmall with rfl | rfl
    · rfl
    · exact (h₃ (Nat.dvd_iff_mod_eq_zero.mp hdiv)).elim
  have ha : 3 ≤ a := by
    by_contra! hal
    have hpa' : p ≤ 2 ^ 2 := hpa ▸ pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by omega : a ≤ 2)
    omega
  let v := p / 2
  let m := 2 * v ^ 2 + 1
  have hv : p = 2 * v := by dsimp [v]; omega
  have hm : p ^ 2 + 2 = 2 * m := by
    change p ^ 2 + 2 = 2 * (2 * v ^ 2 + 1)
    rw [congrArg (fun x : ℕ => x ^ 2) hv]
    ring
  let e := m.factorization 3
  have hme : m = 3 ^ e := prime_power_of_unique_factor (by dsimp [m]; omega) fun q hq hdiv => by
    have hqsmall : q ≤ 3 := by_contra fun h => hbL ⟨q, hq, by omega,
      hm ▸ dvd_mul_of_dvd_right hdiv 2⟩
    rcases two_or_three_of_small_prime hq hqsmall with rfl | rfl
    · have : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
      dsimp [m] at this
      omega
    · rfl
  have h8 : 8 ∣ p := hpa ▸ pow_dvd_pow 2 ha
  obtain ⟨w, hw⟩ := h8
  have hvw : v = 4 * w := by omega
  have hm16 : m % 16 = 1 := by
    dsimp [m]
    rw [hvw, show 2 * (4 * w) ^ 2 + 1 = 16 * (2 * w ^ 2) + 1 by ring]
    omega
  have hm5 : m % 5 = 1 := hme ▸ three_pow_mod_five_of_mod_sixteen (hme ▸ hm16)
  have hd : 5 ∣ p ^ 2 := by omega
  have hp5 : 5 ∣ p := (by decide : Nat.Prime 5).dvd_of_dvd_pow hd
  rw [hpa] at hp5
  exact (by decide : ¬ 5 ∣ (2 : ℕ)) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hp5)

private theorem suitable_of_large {p : ℕ} {b : Kind} (h₂ : b ≠ .two) (h₃ : b ≠ .three)
    (h : LargePrimeFactor (b.parentNat p)) : ∃ q, b.Suitable p q := by
  obtain ⟨q, hp, hq, hd⟩ := h
  refine ⟨q, hp, ?_, ?_⟩
  · rw [← b.cast_parentNat]
    exact Int.natCast_dvd_natCast.mpr hd
  · cases b <;> simp_all [Kind.modulusSize]

private theorem suitable_two (P : ℤ) : ∃ q, Kind.two.Suitable P q :=
  ⟨2, by decide, by rw [parent_two]; exact dvd_refl _, rfl⟩

private theorem suitable_three (P : ℤ) : ∃ q, Kind.three.Suitable P q :=
  ⟨3, by decide, by rw [parent_three]; exact dvd_refl _, rfl⟩

private theorem published_supported (r : Fin 6) (row : CoverRow) (hr : row ∈ publishedRows r) :
    row.kind = .two ∨ row.kind = .three ∨ row.kind.normalizer r.val ≠ 0 ∨
      ((r = 2 ∨ r = 4) ∧ row.kind = .quadTwo) := by
  have h : ∀ i : Fin 6, (publishedRows i).all (fun b => decide
      (b.kind = .two ∨ b.kind = .three ∨ b.kind.normalizer i.val ≠ 0 ∨
        ((i = 2 ∨ i = 4) ∧ b.kind = .quadTwo))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (h r) row hr)

private theorem even_supported (row : CoverRow) (hr : row ∈ evenRows) :
    row.kind = .two ∨ row.kind = .three ∨ row.kind = .linear ∨
      row.kind = .quadOne ∨ row.kind = .quadThree ∨ row.kind = .quartic := by
  have h : evenRows.all (fun b => decide (b.kind = .two ∨ b.kind = .three ∨ b.kind = .linear ∨
      b.kind = .quadOne ∨ b.kind = .quadThree ∨ b.kind = .quartic)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)

private theorem large_case (p : ℕ) (hp : 4 < p) : ∃ K, GoodShift (p : ℤ) K := by
  let r : Fin 6 := ⟨p % 6, Nat.mod_lt _ (by decide)⟩
  have hP : (p : ℤ) ≡ ↑r.val [ZMOD 6] := Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _).symm
  have normal (b : Kind) (hn : b.normalizer r.val ≠ 0) : ∃ q, b.Suitable p q := by
    apply suitable_of_large (fun he => by subst b; exact hn rfl)
      (fun he => by subst b; exact hn rfl)
    exact b.largePrime_of_normalizer hp hn
  have usePublished (hb : r = 2 ∨ r = 4 → LargePrimeFactor (p ^ 2 + 2)) :
      ∃ K, GoodShift (p : ℤ) K := by
    apply goodShift_of_symbolic_cover hP (publishedRows r) (publishedRows_distinct r) ?_
      (publishedRows_cover r)
    intro row hr
    rcases published_supported r row hr with h₂ | h₃ | hn | ⟨he, hq⟩
    · rw [h₂]
      exact suitable_two p
    · rw [h₃]
      exact suitable_three p
    · exact normal row.kind hn
    · rw [hq]
      exact suitable_of_large (by decide) (by decide) (hb he)
  by_cases he : r = 2 ∨ r = 4
  · by_cases hquad : LargePrimeFactor (p ^ 2 + 2)
    · exact usePublished (fun _ => hquad)
    · have hr : p % 6 = 2 ∨ p % 6 = 4 :=
        he.imp (congrArg Fin.val) (congrArg Fin.val)
      have hlin := even_linear_factor hp (by omega) (by omega) hquad
      apply goodShift_of_symbolic_cover hP evenRows (by decide) ?_ (evenRows_cover he)
      intro row hrow
      rcases even_supported row hrow with h₂ | h₃ | hl | h₁ | hq | h₄
      · rw [h₂]
        exact suitable_two p
      · rw [h₃]
        exact suitable_three p
      · rw [hl]
        exact suitable_of_large (by decide) (by decide) hlin
      · rw [h₁]
        exact normal .quadOne (by rcases he with h | h <;> rw [h] <;> decide)
      · rw [hq]
        exact normal .quadThree (by rcases he with h | h <;> rw [h] <;> decide)
      · rw [h₄]
        exact normal .quartic (by rcases he with h | h <;> rw [h] <;> decide)
  · exact usePublished (fun h => (he h).elim)

end ModulusSelection

end ShiftedLucasQNegOneComposite

open ShiftedLucasQNegOneComposite

set_option backward.proofsInPublic true in
/-- **A shift of $U_n(P, -1)$ away from primes.** Let $P \ge 1$ be an integer and let
$U_n = U_n(P, -1)$ be the Lucas sequence with $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = PU_{n+1} + U_n$. Then there is an integer $K > 0$ such that for every natural
number $n$ the three integers $U_n + K - 1$, $U_n + K$ and $U_n + K + 1$ are all composite,
that is, each is greater than $1$ and not prime.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 3
(`integers-2025-A42-thm-3`). -/
public theorem exists_shift_lucasU_q_neg_one_composite {P : ℤ} (hP : 1 ≤ P) :
    ∃ K : ℤ, 0 < K ∧ ∀ n : ℕ, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
      1 < lucasU ⟨P, -1, by decide⟩ n + K + d ∧
        ¬ (lucasU ⟨P, -1, by decide⟩ n + K + d).natAbs.Prime := by
  suffices h : ∃ K, GoodShift P K by
    obtain ⟨K, hK⟩ := h
    exact ⟨K, goodShift_composite hP hK⟩
  by_cases h : P ≤ 4
  · have hsmall : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl
    · exact ⟨_, fixed_one⟩
    · exact ⟨_, fixed_two⟩
    · exact ⟨_, fixed_three⟩
    · exact ⟨_, fixed_four⟩
  by_cases he : P = 22
  · subst P
    exact ⟨_, fixed_twentyTwo⟩
  lift P to ℕ using (by omega : 0 ≤ P)
  exact large_case P (by omega)

end MetaMathlibExt
