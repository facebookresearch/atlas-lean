/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

open scoped BigOperators Topology

/-! # Multivariable Wintner mean-value theorem
-/

private noncomputable def wG (k : ℕ) (f : (Fin k → ℕ) → ℂ) (n : (Fin k → ℕ)) : ℂ :=
  ∑ d : (i : Fin k) → Fin (n i),
    if ∀ i, (d i : ℕ) + 1 ∣ n i then
      (∏ i, (ArithmeticFunction.moebius ((d i : ℕ) + 1) : ℂ)) *
        f (fun i => n i / ((d i : ℕ) + 1))
    else 0

/-- Factor `wG` at `k+1` through the head coordinate. -/
private lemma wG_succ (k : ℕ) (f : (Fin (k + 1) → ℕ) → ℂ) (n : Fin (k + 1) → ℕ) :
    wG (k + 1) f n
    = ∑ d0 : Fin (n 0), if ((d0 : ℕ) + 1 ∣ n 0) then
        (ArithmeticFunction.moebius ((d0 : ℕ) + 1) : ℂ) *
          wG k (fun t => f (Fin.cons (n 0 / ((d0 : ℕ) + 1)) t)) (fun i => n i.succ)
      else 0 := by
  have hwG : wG (k + 1) f n = (∑ d : (i : Fin (k + 1)) → Fin (n i),
      (if ∀ i, ((d i : ℕ) + 1 ∣ n i) then
        (∏ i, (ArithmeticFunction.moebius (((d i) : ℕ) + 1) : ℂ)) *
          f (fun i => n i / (((d i) : ℕ) + 1))
      else 0)) := rfl
  have hsplit : (∑ d : (i : Fin (k + 1)) → Fin (n i),
      (if ∀ i, ((d i : ℕ) + 1 ∣ n i) then
        (∏ i, (ArithmeticFunction.moebius (((d i) : ℕ) + 1) : ℂ)) *
          f (fun i => n i / (((d i) : ℕ) + 1))
      else 0))
      = ∑ d0 : Fin (n 0), ∑ dt : (i : Fin k) → Fin (n i.succ),
        (if ∀ i, (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i) then
          (∏ i, (ArithmeticFunction.moebius
              ((((Fin.cons (α := fun i => Fin (n i)) d0 dt i)) : ℕ) + 1) : ℂ)) *
            f (fun i => n i / ((((Fin.cons (α := fun i => Fin (n i)) d0 dt i)) : ℕ) + 1))
        else 0) := by
    have h1 := Fintype.sum_equiv (Fin.consEquiv (fun i => Fin (n i)))
      (fun p : Fin (n 0) × ((i : Fin k) → Fin (n i.succ)) =>
        (if ∀ i, (((Fin.cons (α := fun i => Fin (n i)) p.1 p.2 i) : ℕ) + 1 ∣ n i) then
          (∏ i, (ArithmeticFunction.moebius
              ((((Fin.cons (α := fun i => Fin (n i)) p.1 p.2 i)) : ℕ) + 1) : ℂ)) *
            f (fun i => n i / ((((Fin.cons (α := fun i => Fin (n i)) p.1 p.2 i)) : ℕ) + 1))
        else 0))
      (fun d : (i : Fin (k + 1)) → Fin (n i) =>
        (if ∀ i, ((d i : ℕ) + 1 ∣ n i) then
          (∏ i, (ArithmeticFunction.moebius (((d i) : ℕ) + 1) : ℂ)) *
            f (fun i => n i / (((d i) : ℕ) + 1))
        else 0))
      (fun p => rfl)
    rw [← h1, Fintype.sum_prod_type]
  rw [hwG, hsplit]
  apply Finset.sum_congr rfl
  intro d0 _
  have hwGk : wG k (fun t => f (Fin.cons (n 0 / ((d0 : ℕ) + 1)) t)) (fun i => n i.succ)
      = ∑ dt : (i : Fin k) → Fin (n i.succ),
        (if ∀ i, (((dt i) : ℕ) + 1 ∣ n i.succ) then
          (∏ i, (ArithmeticFunction.moebius ((((dt i)) : ℕ) + 1) : ℂ)) *
            (fun t => f (Fin.cons (n 0 / ((d0 : ℕ) + 1)) t))
              (fun i => n i.succ / ((((dt i)) : ℕ) + 1))
        else 0) := rfl
  have hcond : ∀ dt : (i : Fin k) → Fin (n i.succ),
      (∀ i : Fin (k + 1), (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i))
      ↔ ((((d0 : ℕ) + 1 ∣ n 0) ∧ ∀ i : Fin k, ((((dt i) : ℕ) + 1) ∣ n i.succ))) := by
    intro dt
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hprod : ∀ dt : (i : Fin k) → Fin (n i.succ),
      (∏ i, (ArithmeticFunction.moebius ((((Fin.cons (α := fun i => Fin (n i)) d0 dt i)) : ℕ) + 1) :
          ℂ))
      = (ArithmeticFunction.moebius ((d0 : ℕ) + 1) : ℂ) *
        ∏ i, (ArithmeticFunction.moebius ((((dt i)) : ℕ) + 1) : ℂ) := by
    intro dt
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hq : ∀ dt : (i : Fin k) → Fin (n i.succ),
      (fun i => n i / ((((Fin.cons (α := fun i => Fin (n i)) d0 dt i)) : ℕ) + 1))
      = Fin.cons (n 0 / ((d0 : ℕ) + 1))
        (fun i : Fin k => n i.succ / ((((dt i)) : ℕ) + 1)) := by
    intro dt
    have h0 : n 0 / ((((Fin.cons (α := fun i => Fin (n i)) d0 dt 0)) : ℕ) + 1)
        = n 0 / ((d0 : ℕ) + 1) := by
      rw [Fin.cons_zero]
    have ht : Fin.tail (fun i : Fin (k + 1) => n i /
        ((((Fin.cons (α := fun i => Fin (n i)) d0 dt i)) : ℕ) + 1))
        = (fun i : Fin k => n i.succ / ((((dt i)) : ℕ) + 1)) := by
      funext i
      change n i.succ / ((((Fin.cons (α := fun i => Fin (n i)) d0 dt i.succ)) : ℕ) + 1) = _
      rw [Fin.cons_succ]
    exact (Fin.cons_self_tail _).symm.trans (by rw [h0, ht])
  by_cases h0 : ((d0 : ℕ) + 1 ∣ n 0)
  · rw [ite_eq_left h0, hwGk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro dt _
    by_cases ht : ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ)
    · rw [ite_eq_left ((hcond dt).mpr ⟨h0, ht⟩), ite_eq_left ht]
      simp only []
      rw [hprod dt, hq dt]
      ring
    · rw [ite_eq_right (fun h => ht ((hcond dt).mp h).2), ite_eq_right ht, mul_zero]
  · rw [ite_eq_right h0]
    apply Finset.sum_eq_zero
    intro dt _
    exact ite_eq_right (fun h => h0 ((hcond dt).mp h).1)

/-- Sum of `μ` over divisors: `∑ d ∈ n.divisors, μ d = [n = 1]`. -/
private lemma sum_moebius_divisors (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have hiff := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℂ) (f := fun m => if m = 1 then (1 : ℂ) else 0) (g := fun _ => 1)
  have hhyp : ∀ m > 0, ∑ i ∈ m.divisors, (if i = 1 then (1 : ℂ) else 0) = 1 := by
    intro m hm
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hne
      simp [hne]
    · intro hcon
      exact absurd (Nat.mem_divisors.mpr ⟨one_dvd m, ne_of_gt hm⟩) hcon
  have hcon := (hiff.mp hhyp) n hn
  simp only [mul_one] at hcon
  have hstep : (∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℂ))
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) := by
    have hsd := Nat.sum_divisorsAntidiagonal
      (M := ℂ) (fun a _ => (ArithmeticFunction.moebius a : ℂ)) (n := n)
    beta_reduce at hsd
    exact hsd
  rw [hstep] at hcon
  exact hcon

/-- A `Fin`-indexed sum with a divisibility test equals the divisor sum. -/
private lemma sum_fin_divisors (N : ℕ) (H : ℕ → ℂ) :
    (∑ d : Fin N, (if (d : ℕ) + 1 ∣ N then H ((d : ℕ) + 1) else 0))
    = ∑ e ∈ N.divisors, H e := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun (d : Fin N) _ => ((d : ℕ) + 1)) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Nat.mem_divisors]
    refine ⟨hd.2, ?_⟩
    intro hN
    have hd0 := d.2
    subst hN
    omega
  · intro a _ b _ hab
    have hval : (a : ℕ) = (b : ℕ) := Nat.succ.inj hab
    exact Fin.ext hval
  · intro e he
    rw [Nat.mem_divisors] at he
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1 (Nat.pos_of_ne_zero he.2)
    have heN : e ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero he.2) he.1
    refine ⟨⟨e - 1, by omega⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change (e - 1 + 1 ∣ N)
      rw [Nat.sub_add_cancel hepos]
      exact he.1
    · change (e - 1 + 1) = e
      exact Nat.sub_add_cancel hepos
  · intro d _
    rfl

/-- 1D Möbius inversion in double-sum form:
    `∑_{d | N} ∑_{c | d} μ(c) Q(d/c) = Q(N)`. -/
private lemma moebius_inv_1d (N : ℕ) (hN : 0 < N) (Q : ℕ → ℂ) :
    ∑ d ∈ N.divisors, ∑ c ∈ d.divisors, (ArithmeticFunction.moebius c : ℂ) * Q (d / c)
    = Q N := by
  have hNne : N ≠ 0 := ne_of_gt hN
  set S : Finset (Sigma fun _ : ℕ => ℕ) := N.divisors.sigma (fun d => d.divisors) with hSdef
  set T : Finset (Sigma fun _ : ℕ => ℕ) := N.divisors.sigma (fun e => (N / e).divisors) with hTdef
  have collapse : (∑ d ∈ N.divisors, ∑ c ∈ d.divisors,
        (ArithmeticFunction.moebius c : ℂ) * Q (d / c))
      = ∑ x ∈ S,
        (ArithmeticFunction.moebius x.2 : ℂ) * Q (x.1 / x.2) := by
    rw [hSdef, Finset.sum_sigma]
  have expand : (∑ e ∈ N.divisors, Q e * ∑ c ∈ (N / e).divisors, (ArithmeticFunction.moebius c : ℂ))
      = ∑ y ∈ T,
        Q y.1 * (ArithmeticFunction.moebius y.2 : ℂ) := by
    rw [hTdef, Finset.sum_sigma]
    simp only [Finset.mul_sum]
  have hbij : (∑ x ∈ S,
        (ArithmeticFunction.moebius x.2 : ℂ) * Q (x.1 / x.2))
      = ∑ y ∈ T,
        Q y.1 * (ArithmeticFunction.moebius y.2 : ℂ) := by
    refine Finset.sum_bij ?i ?_ ?_ ?_ ?_
    · intro a _
      exact Sigma.mk (a.1 / a.2) a.2
    · intro a ha
      have ha' := Finset.mem_sigma.mp ha
      obtain ⟨hdN, hcd⟩ := ha'
      rw [Nat.mem_divisors] at hdN hcd
      have hc_pos : 0 < a.2 := Nat.pos_of_dvd_of_pos hcd.1 (Nat.pos_of_ne_zero hcd.2)
      have hd_pos : 0 < a.1 := Nat.pos_of_ne_zero hcd.2
      have he_pos : 0 < a.1 / a.2 := Nat.div_pos (Nat.le_of_dvd hd_pos hcd.1) hc_pos
      have he_dvd : a.1 / a.2 ∣ N := dvd_trans (Nat.div_dvd_of_dvd hcd.1) hdN.1
      have hNe_pos : 0 < N / (a.1 / a.2) := Nat.div_pos (Nat.le_of_dvd hN he_dvd) he_pos
      obtain ⟨j, hj⟩ := hdN.1
      have hde : (a.1 / a.2) * a.2 = a.1 := Nat.div_mul_cancel hcd.1
      have hN_eq : N = (a.1 / a.2) * (a.2 * j) := by
        calc N = a.1 * j := hj
          _ = ((a.1 / a.2) * a.2) * j := by rw [hde]
          _ = (a.1 / a.2) * (a.2 * j) := by ring
      have hNe : N / (a.1 / a.2) = a.2 * j := by
        rw [hN_eq]; exact Nat.mul_div_cancel_left _ he_pos
      rw [hTdef, Finset.mem_sigma]
      exact ⟨Nat.mem_divisors.mpr ⟨he_dvd, hNne⟩,
        Nat.mem_divisors.mpr ⟨⟨j, hNe⟩, ne_of_gt hNe_pos⟩⟩
    · intro a1 ha1 a2 ha2 h
      rw [hSdef] at ha1 ha2
      have ha1' := Finset.mem_sigma.mp ha1
      have ha2' := Finset.mem_sigma.mp ha2
      obtain ⟨d1, c1⟩ := a1
      obtain ⟨d2, c2⟩ := a2
      simp only [Nat.mem_divisors] at ha1' ha2'
      have h1 : d1 / c1 = d2 / c2 := congrArg Sigma.fst h
      have h2 : c1 = c2 := congrArg Sigma.snd h
      subst h2
      have hc : c1 ∣ d1 := ha1'.2.1
      have hc2 : c1 ∣ d2 := ha2'.2.1
      have hd : d1 = d2 := by
        have e1 := Nat.div_mul_cancel hc
        have e2 := Nat.div_mul_cancel hc2
        rw [h1] at e1
        exact e1.symm.trans e2
      subst hd
      rfl
    · intro b hb
      rw [hTdef] at hb
      obtain ⟨e, c⟩ := b
      rw [Finset.mem_sigma] at hb
      obtain ⟨he_mem, hc_mem⟩ := hb
      rw [Nat.mem_divisors] at he_mem hc_mem
      have hedvd2 : e ∣ N := he_mem.1
      have hNediv_ne : N / e ≠ 0 := hc_mem.2
      have hcdvd : c ∣ N / e := hc_mem.1
      have he_pos : 0 < e := Nat.pos_of_dvd_of_pos hedvd2 hN
      have hNediv_pos : 0 < N / e := Nat.pos_of_ne_zero hNediv_ne
      have hc_pos : 0 < c := Nat.pos_of_dvd_of_pos hcdvd hNediv_pos
      have ⟨j, hj⟩ := hedvd2
      obtain ⟨k, hk⟩ := hcdvd
      have hcc : e * (N / e) = N := Nat.mul_div_cancel' hedvd2
      have hN_eq : N = e * (c * k) := by
        rw [hk] at hcc
        exact hcc.symm
      refine ⟨Sigma.mk (e * c) c, ?_, ?_⟩
      · rw [hSdef, Finset.mem_sigma]
        refine ⟨Nat.mem_divisors.mpr ⟨⟨k, by rw [hN_eq]; ring⟩, hNne⟩,
          Nat.mem_divisors.mpr ⟨⟨e, mul_comm e c⟩, mul_ne_zero (ne_of_gt he_pos) (ne_of_gt hc_pos)⟩⟩
      · have hcc2 : e * c / c = e := Nat.mul_div_cancel _ hc_pos
        simp [hcc2]
    · intro a _
      obtain ⟨d, c⟩ := a
      exact mul_comm _ _
  have hmu : ∀ e ∈ N.divisors, (∑ c ∈ (N / e).divisors, (ArithmeticFunction.moebius c : ℂ))
      = (if N / e = 1 then (1 : ℂ) else 0) := by
    intro e he
    apply sum_moebius_divisors
    rw [Nat.mem_divisors] at he
    exact Nat.div_pos (Nat.le_of_dvd hN he.1) (Nat.pos_of_dvd_of_pos he.1 hN)
  have hfin : (∑ e ∈ N.divisors, Q e * ∑ c ∈ (N / e).divisors, (ArithmeticFunction.moebius c : ℂ))
      = ∑ e ∈ N.divisors, (if e = N then Q e else 0) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hmu e he]
    by_cases h : e = N
    · subst h
      rw [Nat.div_self hN]
      simp
    · have hne : N / e ≠ 1 := by
        intro hcon
        apply h
        rw [Nat.mem_divisors] at he
        have hNe : N = e * (N / e) := (Nat.mul_div_cancel' he.1).symm
        rw [hcon, mul_one] at hNe
        exact hNe.symm
      simp [h, hne]
  rw [collapse, hbij, ← expand, hfin, Finset.sum_ite_eq']
  have hmem : N ∈ N.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hNne⟩
  simp only [hmem, ite_true]

/-- Split a sum over `(i : Fin (k+1)) → Fin (n i)` into head and tail sums. -/
private lemma sum_split_head (k : ℕ) (n : Fin (k + 1) → ℕ) (F : ((i : Fin (k + 1)) → Fin (n i)) → ℂ)
    :
    (∑ d, F d) = ∑ d0 : Fin (n 0), ∑ dt : (i : Fin k) → Fin (n i.succ),
      F (Fin.cons (α := fun i => Fin (n i)) d0 dt) := by
  have h1 := Fintype.sum_equiv (Fin.consEquiv (fun i => Fin (n i)))
    (fun p : Fin (n 0) × ((i : Fin k) → Fin (n i.succ)) =>
      F (Fin.cons (α := fun i => Fin (n i)) p.1 p.2))
    F (fun p => rfl)
  rw [← h1, Fintype.sum_prod_type]

/-- Multivariable Möbius inversion: `f` is recovered from its `wG`-transform. -/
private lemma wG_inversion (k : ℕ) (f : (Fin k → ℕ) → ℂ) (n : (Fin k → ℕ))
    (hn : ∀ i, 0 < n i) :
    f n = ∑ d : (i : Fin k) → Fin (n i),
      if ∀ i, (d i : ℕ) + 1 ∣ n i then wG k f (fun i => (d i : ℕ) + 1) else 0 := by
  induction k with
  | zero =>
    have hwG0 : ∀ m : Fin 0 → ℕ, wG 0 f m = f n := by
      intro m
      change (∑ e : (i : Fin 0) → Fin (m i),
        (if ∀ i, ((e i : ℕ) + 1 ∣ m i) then
          (∏ i, (ArithmeticFunction.moebius (((e i) : ℕ) + 1) : ℂ)) *
            f (fun i => m i / (((e i) : ℕ) + 1))
        else 0)) = f n
      rw [Fintype.sum_unique, ite_eq_left (fun i => nomatch i)]
      have hfn : (fun i => m i / ((((default : (i : Fin 0) → Fin (m i)) i) : ℕ) + 1)) = n :=
        funext fun i => nomatch i
      rw [hfn]
      simp
    rw [Fintype.sum_unique, ite_eq_left (fun i => nomatch i)]
    exact (hwG0 _).symm
  | succ k ih =>
    have hsplit2 : (∑ d : (i : Fin (k + 1)) → Fin (n i),
          (if ∀ i, ((d i : ℕ) + 1 ∣ n i) then wG (k + 1) f (fun i => (d i : ℕ) + 1) else 0))
        = ∑ d0 : Fin (n 0), ∑ dt : (i : Fin k) → Fin (n i.succ),
          (if ∀ i, (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i) then
            wG (k + 1) f (fun i => (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1)) else
                0) :=
      sum_split_head k n _
    have hcond : ∀ d0 : Fin (n 0), ∀ dt : (i : Fin k) → Fin (n i.succ),
        (∀ i : Fin (k + 1), (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i))
        ↔ ((((d0 : ℕ) + 1 ∣ n 0) ∧ ∀ i : Fin k, ((((dt i) : ℕ) + 1) ∣ n i.succ))) := by
      intro d0 dt
      rw [Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hexpand : ∀ (d0 : Fin (n 0)) (dt : (i : Fin k) → Fin (n i.succ)),
        wG (k + 1) f (fun i => (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1))
        = ∑ c0 : Fin ((d0 : ℕ) + 1), if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
            (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
              wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                (fun i => ((dt i : ℕ) + 1))
          else 0 := by
      intro d0 dt
      exact wG_succ k f _
    have per_d0 : ∀ d0 : Fin (n 0),
        (∑ dt : (i : Fin k) → Fin (n i.succ),
          (if ∀ i, (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i) then
            wG (k + 1) f (fun i => (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1)) else
                0))
        = (if ((d0 : ℕ) + 1 ∣ n 0) then
            (∑ c ∈ ((d0 : ℕ) + 1).divisors,
              (ArithmeticFunction.moebius c : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / c)) (fun i => n i.succ))) else 0) := by
      intro d0
      by_cases h0 : ((d0 : ℕ) + 1 ∣ n 0)
      · rw [ite_eq_left h0]
        have hcC : ∀ dt : (i : Fin k) → Fin (n i.succ),
            (if ∀ i, (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i) then
              wG (k + 1) f (fun i => (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1)) else
                  0)
            = (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
              wG (k + 1) f (fun i => (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1)) else
                  0) := by
          intro dt
          by_cases ht : ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ)
          · rw [ite_eq_left ht, ite_eq_left ((hcond d0 dt).mpr ⟨h0, ht⟩)]
          · rw [ite_eq_right ht, ite_eq_right (fun h => ht ((hcond d0 dt).mp h).2)]
        simp only [hcC]
        simp only [hexpand d0]
        have hpush : (∑ dt : (i : Fin k) → Fin (n i.succ),
            (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
              (∑ c0 : Fin ((d0 : ℕ) + 1),
                (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
                  (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                    wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                      (fun i => ((dt i : ℕ) + 1)) else 0)) else 0))
            = ∑ c0 : Fin ((d0 : ℕ) + 1), ∑ dt : (i : Fin k) → Fin (n i.succ),
              (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
                (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
                  (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                    wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                      (fun i => ((dt i : ℕ) + 1)) else 0) else 0) := by
          trans ∑ dt : (i : Fin k) → Fin (n i.succ), ∑ c0 : Fin ((d0 : ℕ) + 1),
            (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
              (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
                (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                  wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                    (fun i => ((dt i : ℕ) + 1)) else 0) else 0)
          · apply Finset.sum_congr rfl
            intro dt _
            by_cases ht : ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ)
            · simp only [ite_eq_left ht]
            · simp only [ite_eq_right ht]
              symm
              exact Finset.sum_eq_zero (fun c0 _ => rfl)
          · exact Finset.sum_comm
        rw [hpush]
        have mufac : ∀ c0 : Fin ((d0 : ℕ) + 1),
            (∑ dt : (i : Fin k) → Fin (n i.succ),
              (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
                (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                  wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                    (fun i => ((dt i : ℕ) + 1)) else 0))
            = (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
              ∑ dt : (i : Fin k) → Fin (n i.succ),
              (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
                wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                  (fun i => ((dt i : ℕ) + 1)) else 0) := by
          intro c0
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro dt _
          rw [mul_ite, mul_zero]
        have hih : ∀ c0 : Fin ((d0 : ℕ) + 1),
            (∑ dt : (i : Fin k) → Fin (n i.succ),
              (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
                wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                  (fun i => ((dt i : ℕ) + 1)) else 0))
            = f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) (fun i => n i.succ)) :=
          fun c0 => (ih (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
            (fun i => n i.succ) (fun i => hn i.succ)).symm
        have hdiv : (∑ c0 : Fin ((d0 : ℕ) + 1),
            (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
              (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) (fun i => n i.succ)) else 0))
            = ∑ c ∈ ((d0 : ℕ) + 1).divisors,
              (ArithmeticFunction.moebius c : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / c)) (fun i => n i.succ)) :=
          sum_fin_divisors ((d0 : ℕ) + 1)
            (fun e => (ArithmeticFunction.moebius e : ℂ) *
              f (Fin.cons ((((d0 : ℕ) + 1) / e)) (fun i => n i.succ)))
        have stepC : ∀ c0 : Fin ((d0 : ℕ) + 1),
            (∑ dt : (i : Fin k) → Fin (n i.succ),
              (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
                (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
                  (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                    wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                      (fun i => ((dt i : ℕ) + 1)) else 0) else 0))
            = (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
              (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) (fun i => n i.succ)) else 0) := by
          intro c0
          by_cases hc : ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1)
          · simp only [ite_eq_left hc]
            rw [mufac c0, hih c0]
          · simp only [ite_eq_right hc]
            apply Finset.sum_eq_zero
            intro dt _
            split_ifs with ht <;> rfl
        have hstepC : (∑ c0 : Fin ((d0 : ℕ) + 1), ∑ dt : (i : Fin k) → Fin (n i.succ),
            (if ∀ i, ((((dt i) : ℕ) + 1) ∣ n i.succ) then
              (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
                (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                  wG k (fun t => f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) t))
                    (fun i => ((dt i : ℕ) + 1)) else 0) else 0))
          = (∑ c0 : Fin ((d0 : ℕ) + 1),
            (if ((c0 : ℕ) + 1 ∣ (d0 : ℕ) + 1) then
              (ArithmeticFunction.moebius (((c0 : ℕ) + 1) : ℕ) : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / ((c0 : ℕ) + 1))) (fun i => n i.succ)) else 0)) :=
          Finset.sum_congr rfl (fun c0 _ => stepC c0)
        rw [hstepC]
        exact hdiv
      · rw [ite_eq_right h0]
        apply Finset.sum_eq_zero
        intro dt _
        exact ite_eq_right (fun h => h0 ((hcond d0 dt).mp h).1)
    have hstep1 : (∑ d0 : Fin (n 0), ∑ dt : (i : Fin k) → Fin (n i.succ),
          (if ∀ i, (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1 ∣ n i) then
            wG (k + 1) f (fun i => (((Fin.cons (α := fun i => Fin (n i)) d0 dt i) : ℕ) + 1)) else
                0))
        = (∑ d0 : Fin (n 0),
          (if ((d0 : ℕ) + 1 ∣ n 0) then
            (∑ c ∈ ((d0 : ℕ) + 1).divisors,
              (ArithmeticFunction.moebius c : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / c)) (fun i => n i.succ))) else 0)) :=
      Finset.sum_congr rfl (fun d0 _ => per_d0 d0)
    have houter : (∑ d0 : Fin (n 0),
          (if ((d0 : ℕ) + 1 ∣ n 0) then
            (∑ c ∈ ((d0 : ℕ) + 1).divisors,
              (ArithmeticFunction.moebius c : ℂ) *
                f (Fin.cons ((((d0 : ℕ) + 1) / c)) (fun i => n i.succ))) else 0))
        = ∑ e ∈ (n 0).divisors, ∑ c ∈ e.divisors,
          (ArithmeticFunction.moebius c : ℂ) *
            f (Fin.cons ((e / c)) (fun i => n i.succ)) :=
      sum_fin_divisors (n 0)
        (fun e => ∑ c ∈ e.divisors,
          (ArithmeticFunction.moebius c : ℂ) * f (Fin.cons ((e / c)) (fun i => n i.succ)))
    rw [hsplit2, hstep1, houter]
    have h1d := moebius_inv_1d (n 0) (hn 0)
      (fun e => f (Fin.cons e (fun i => n i.succ)))
    have hcons : Fin.cons (n 0) (fun i => n i.succ) = n := Fin.cons_self_tail n
    have hfn : f n = f (Fin.cons (n 0) (fun i => n i.succ)) := congrArg f hcons.symm
    rw [hfn]
    exact h1d.symm

private noncomputable def wF (k : ℕ) (f : (Fin k → ℕ) → ℂ) (x m : (Fin k → ℕ)) : ℂ :=
  (wG k f (fun i => m i + 1) * ∏ i, (((x i / (m i + 1) : ℕ)) : ℂ)) / ∏ i, (x i : ℂ)

/-- For fixed `x`, the box average equals the `tsum` of `wF`. -/
private lemma box_avg_eq_tsum (k : ℕ) (f : (Fin k → ℕ) → ℂ) :
    (fun x : Fin k → ℕ =>
      (∑ n : (i : Fin k) → Fin (x i), f (fun i => (n i : ℕ) + 1)) /
        ∏ i, (x i : ℂ)) =ᶠ[Filter.atTop] (fun x => ∑' m : Fin k → ℕ, wF k f x m) := by
  apply Filter.Eventually.of_forall
  intro x
  change (∑ n : (i : Fin k) → Fin (x i), f (fun i => (n i : ℕ) + 1)) / ∏ i, (x i : ℂ)
    = ∑' m : Fin k → ℕ, wF k f x m
  have hsub : ∀ n : (i : Fin k) → Fin (x i),
      f (fun i => (n i : ℕ) + 1)
      = ∑ d : (i : Fin k) → Fin (x i),
        (if ∀ i, (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then
          wG k f (fun i => (d i : ℕ) + 1) else 0) := by
    intro n
    have hpos : ∀ i, 0 < (n i : ℕ) + 1 := fun i => Nat.succ_pos _
    have hinv := wG_inversion k f (fun i => (n i : ℕ) + 1) hpos
    set φ : ((i : Fin k) → Fin ((n i : ℕ) + 1)) → ((i : Fin k) → Fin (x i)) :=
      fun e i => (⟨(e i : ℕ), lt_of_lt_of_le (e i).2 (Nat.succ_le_of_lt (n i).2)⟩ : Fin (x i))
    have hφval : ∀ e : (i : Fin k) → Fin ((n i : ℕ) + 1), ∀ i, ((φ e i : Fin (x i)) : ℕ)
        = (e i : ℕ) :=
      fun e i => rfl
    have hinj : Function.Injective φ := by
      intro e1 e2 h
      funext i
      have hφ : ((φ e1 i : Fin (x i)) : ℕ) = ((φ e2 i : Fin (x i)) : ℕ) :=
        congrArg (@Fin.val (x i)) (congrFun h i)
      have hval : ((e1 i : ℕ)) = ((e2 i : ℕ)) := hφ
      exact Fin.ext hval
    have himage : ∀ d : (i : Fin k) → Fin (x i),
        d ∈ Finset.univ.image φ ↔ ∀ i, (d i : ℕ) < (n i : ℕ) + 1 := by
      intro d
      constructor
      · intro h i
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp h
        exact (e i).2
      · intro h
        exact Finset.mem_image.mpr
          ⟨(fun i => (⟨(d i : ℕ), h i⟩ : Fin ((n i : ℕ) + 1))), Finset.mem_univ _,
            funext fun i => Fin.ext rfl⟩
    have hvan : ∀ d : (i : Fin k) → Fin (x i), d ∉ Finset.univ.image φ →
        (if ∀ i, (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then
          wG k f (fun i => (d i : ℕ) + 1) else 0) = 0 := by
      intro d hnim
      exact ite_eq_right (fun h => hnim (by
        rw [himage]
        intro i
        have hdvd := h i
        have hle := Nat.le_of_dvd (Nat.succ_pos _) hdvd
        omega))
    have hsub2 : (∑ d : (i : Fin k) → Fin (x i),
        (if ∀ i, (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then
          wG k f (fun i => (d i : ℕ) + 1) else 0))
        = ∑ d ∈ Finset.univ.image φ,
          (if ∀ i, (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then
            wG k f (fun i => (d i : ℕ) + 1) else 0) :=
      (Finset.sum_subset (Finset.subset_univ _) (fun d _ hnim => hvan d hnim)).symm
    have hbij2 : (∑ e : (i : Fin k) → Fin ((n i : ℕ) + 1),
          (if ∀ i, (((e i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then
            wG k f (fun i => (e i : ℕ) + 1) else 0))
        = (∑ d ∈ Finset.univ.image φ,
        (if ∀ i, (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then
          wG k f (fun i => (d i : ℕ) + 1) else 0)) := by
      refine Finset.sum_bij (fun e _ => φ e) ?_ ?_ ?_ ?_
      · intro e _
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
      · intro e1 _ e2 _ h
        exact hinj h
      · intro d hd
        obtain ⟨e, heU, heq⟩ := Finset.mem_image.mp hd
        exact ⟨e, heU, heq⟩
      · intro e _
        simp only [hφval]
    rw [hinv, hbij2, hsub2]
  have hcoord : ∀ i : Fin k, ∀ D : ℕ,
      (∑ j : Fin (x i), (if (D ∣ ((j : ℕ) + 1)) then (1 : ℂ) else 0))
      = (((x i / D : ℕ)) : ℂ) := by
    intro i D
    have h1 : (∑ j : Fin (x i), (if (D ∣ ((j : ℕ) + 1)) then (1 : ℂ) else 0))
        = ∑ e ∈ Finset.range (x i), (if (D ∣ e + 1) then (1 : ℂ) else 0) :=
      Fin.sum_univ_eq_sum_range (fun e => if (D ∣ e + 1) then (1 : ℂ) else 0) (x i)
    rw [h1, Finset.sum_boole, Nat.card_multiples]
  have hcount : ∀ d : (i : Fin k) → Fin (x i),
      (∑ n : (i : Fin k) → Fin (x i),
        (if ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1))) then
          wG k f (fun i => (d i : ℕ) + 1) else 0))
      = wG k f (fun i => (d i : ℕ) + 1) * ∏ i, ((((x i / ((d i : ℕ) + 1) : ℕ))) : ℂ) := by
    intro d
    have hprod_ite : ∀ n : (i : Fin k) → Fin (x i),
        (if ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1))) then (1 : ℂ) else 0)
        = ∏ i, (if (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then (1 : ℂ) else 0) := by
      intro n
      by_cases h : ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)))
      · rw [ite_eq_left h]
        symm
        apply Finset.prod_eq_one
        intro i _
        rw [ite_eq_left (h i)]
      · rw [ite_eq_right h]
        symm
        obtain ⟨i, hi⟩ := not_forall.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    have hps : (∑ n : (i : Fin k) → Fin (x i), ∏ i,
        (if (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then (1 : ℂ) else 0))
        = ∏ i, ∑ j : Fin (x i),
          (if (((d i : ℕ) + 1) ∣ ((j : ℕ) + 1)) then (1 : ℂ) else 0) :=
      (Fintype.prod_sum (fun i (j : Fin (x i)) =>
        if (((d i : ℕ) + 1) ∣ ((j : ℕ) + 1)) then (1 : ℂ) else 0)).symm
    have hind : (∑ n : (i : Fin k) → Fin (x i),
        (if ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1))) then (1 : ℂ) else 0))
        = ∏ i, ((((x i / ((d i : ℕ) + 1) : ℕ))) : ℂ) := by
      calc (∑ n : (i : Fin k) → Fin (x i),
          (if ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1))) then (1 : ℂ) else 0))
          = (∑ n : (i : Fin k) → Fin (x i), ∏ i,
            (if (((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)) then (1 : ℂ) else 0)) :=
            Finset.sum_congr rfl (fun n _ => hprod_ite n)
        _ = ∏ i, ∑ j : Fin (x i),
            (if (((d i : ℕ) + 1) ∣ ((j : ℕ) + 1)) then (1 : ℂ) else 0) := hps
        _ = ∏ i, ((((x i / ((d i : ℕ) + 1) : ℕ))) : ℂ) :=
            Finset.prod_congr rfl (fun i _ => hcoord i _)
    trans wG k f (fun i => (d i : ℕ) + 1) *
      ∑ n : (i : Fin k) → Fin (x i),
        (if ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1))) then (1 : ℂ) else 0)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1)))
      · simp only [ite_eq_left h, mul_one]
      · simp only [ite_eq_right h, mul_zero]
    · rw [hind]
  have hS : (∑ n : (i : Fin k) → Fin (x i), f (fun i => (n i : ℕ) + 1))
      = ∑ d : (i : Fin k) → Fin (x i),
        wG k f (fun i => (d i : ℕ) + 1) * ∏ i, ((((x i / ((d i : ℕ) + 1) : ℕ))) : ℂ) := by
    rw [show (∑ n : (i : Fin k) → Fin (x i), f (fun i => (n i : ℕ) + 1))
        = ∑ n : (i : Fin k) → Fin (x i), ∑ d : (i : Fin k) → Fin (x i),
          (if ∀ i, ((((d i : ℕ) + 1) ∣ ((n i : ℕ) + 1))) then
            wG k f (fun i => (d i : ℕ) + 1) else 0) from
      Finset.sum_congr rfl (fun n _ => hsub n)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun d _ => hcount d)
  have hts : (∑' m : Fin k → ℕ, wF k f x m)
      = ∑ d : (i : Fin k) → Fin (x i), wF k f x (fun i => (d i : ℕ)) := by
    have hvan : ∀ m : Fin k → ℕ,
        m ∉ Finset.univ.image (fun d : (i : Fin k) → Fin (x i) => fun i => (d i : ℕ)) →
        wF k f x m = 0 := by
      intro m hm
      have hex : ∃ i, x i ≤ m i := by
        by_contra hcon
        apply hm
        exact Finset.mem_image.mpr
          ⟨(fun i => (⟨m i, lt_of_not_ge (fun h => hcon ⟨i, h⟩)⟩ : Fin (x i))),
            Finset.mem_univ _, funext fun i => rfl⟩
      obtain ⟨i, hi⟩ := hex
      have hzero : x i / (m i + 1) = 0 :=
        Nat.div_eq_of_lt (lt_of_le_of_lt hi (Nat.lt_succ_self _))
      have hprod0 : ∏ j, ((((x j / (m j + 1) : ℕ))) : ℂ) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [hzero]
        exact Nat.cast_zero
      change ((wG k f (fun i => m i + 1) * ∏ i, ((((x i / (m i + 1) : ℕ))) : ℂ)) /
        ∏ i, (x i : ℂ)) = 0
      rw [hprod0, mul_zero, zero_div]
    rw [tsum_eq_sum hvan]
    exact Finset.sum_image (fun d1 _ d2 _ h => funext fun i => Fin.ext (congrFun h i))
  have h1 : (∑ n : (i : Fin k) → Fin (x i), f (fun i => (n i : ℕ) + 1)) / ∏ i, (x i : ℂ)
      = ∑ d : (i : Fin k) → Fin (x i), wF k f x (fun i => (d i : ℕ)) := by
    rw [hS, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    exact rfl
  exact h1.trans hts.symm

private noncomputable def wBound (k : ℕ) (f : (Fin k → ℕ) → ℂ) (m : (Fin k → ℕ)) : ℝ :=
  ‖wG k f (fun i => m i + 1)‖ / ∏ i, ((m i + 1 : ℕ) : ℝ)

private lemma hbound_aux (d : ℕ) (hd : 0 < d) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ‖((x / d : ℕ) : ℂ) / (x : ℂ) - (1 : ℂ) / (d : ℂ)‖ ≤ 1 / (x : ℝ) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  have hxpos : 0 < x := hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hxpos
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmod : d * (x / d) + x % d = x := Nat.div_add_mod x d
  have hmodC : (d : ℂ) * ((x / d : ℕ) : ℂ) + ((x % d : ℕ) : ℂ) = (x : ℂ) := by
    exact_mod_cast hmod
  have hlt : x % d < d := Nat.mod_lt x hd
  have heq : ((x / d : ℕ) : ℂ) / (x : ℂ) - (1 : ℂ) / (d : ℂ)
      = -(((x % d : ℕ) : ℂ) / ((d : ℂ) * (x : ℂ))) := by
    have h1 : ((x / d : ℕ) : ℂ) / (x : ℂ) - (1 : ℂ) / (d : ℂ)
        = (((x / d : ℕ) : ℂ) * (d : ℂ) - (x : ℂ)) / ((x : ℂ) * (d : ℂ)) := by
      field_simp
    have h2 : (((x % d : ℕ) : ℂ) / ((d : ℂ) * (x : ℂ)))
        = ((x : ℂ) - ((x / d : ℕ) : ℂ) * (d : ℂ)) / ((x : ℂ) * (d : ℂ)) := by
      have hrr : ((x % d : ℕ) : ℂ) = (x : ℂ) - (d : ℂ) * ((x / d : ℕ) : ℂ) := by
        linear_combination hmodC
      rw [hrr]
      field_simp
    rw [h1, h2]
    field_simp
    ring
  rw [heq, norm_neg, Complex.norm_div]
  rw [Complex.norm_natCast, Complex.norm_mul]
  rw [Complex.norm_natCast, Complex.norm_natCast]
  have hr_le : ((x % d : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.le_of_lt hlt
  have hdx : (0 : ℝ) < (d : ℝ) * (x : ℝ) := mul_pos hdR hxR
  have hrw : (1 : ℝ) / (x : ℝ) = (d : ℝ) / ((d : ℝ) * (x : ℝ)) := by
    field_simp
  rw [hrw]
  exact div_le_div_of_nonneg_right hr_le (le_of_lt hdx)

private lemma nat_div_div_tendsto (d : ℕ) (hd : 0 < d) :
    Filter.Tendsto (fun x : ℕ => ((x / d : ℕ) : ℂ) / (x : ℂ)) Filter.atTop
      (nhds ((1 : ℂ) / (d : ℂ))) := by
  have hlim : Filter.Tendsto (fun x : ℕ => (1 : ℝ) / (x : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h0 : Filter.Tendsto (fun x : ℕ => ((x / d : ℕ) : ℂ) / (x : ℂ) - (1 : ℂ) / (d : ℂ))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' (hbound_aux d hd) hlim
  have hadd := h0.add (tendsto_const_nhds (x := ((1 : ℂ) / (d : ℂ))))
  simpa using hadd

private lemma proj_tendsto_atTop (k : ℕ) (i : Fin k) :
    Filter.Tendsto (fun x : (Fin k → ℕ) => x i) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨fun _ => b, fun a ha => ha i⟩

private lemma wF_tendsto (k : ℕ) (f : (Fin k → ℕ) → ℂ) (m : (Fin k → ℕ)) :
    Filter.Tendsto (fun x : (Fin k → ℕ) => wF k f x m) Filter.atTop
      (nhds (wG k f (fun i => m i + 1) / ∏ i, ((m i + 1 : ℕ) : ℂ))) := by
  have h1d : ∀ i : Fin k, Filter.Tendsto
      (fun x : (Fin k → ℕ) => (((x i / (m i + 1) : ℕ)) : ℂ) / (x i : ℂ))
      Filter.atTop (nhds ((1 : ℂ) / ((m i + 1 : ℕ) : ℂ))) := by
    intro i
    exact (nat_div_div_tendsto (m i + 1) (Nat.succ_pos _)).comp (proj_tendsto_atTop k i)
  have hprod := tendsto_finsetProd Finset.univ (fun i _ => h1d i)
  have h_eq : (fun x : (Fin k → ℕ) => wF k f x m)
      = (fun x => wG k f (fun i => m i + 1) * ∏ i,
          ((((x i / (m i + 1) : ℕ)) : ℂ) / (x i : ℂ))) := by
    funext x
    unfold wF
    rw [mul_div_assoc, Finset.prod_div_distrib]
  have h_lim_eq : wG k f (fun i => m i + 1) * ∏ i, ((1 : ℂ) / ((m i + 1 : ℕ) : ℂ))
      = wG k f (fun i => m i + 1) / ∏ i, ((m i + 1 : ℕ) : ℂ) := by
    have : ∏ i, ((1 : ℂ) / ((m i + 1 : ℕ) : ℂ)) = 1 / ∏ i, ((m i + 1 : ℕ) : ℂ) := by
      rw [Finset.prod_div_distrib]
      simp
    rw [this, mul_one_div]
  have hcm := hprod.const_mul (wG k f (fun i => m i + 1))
  rw [← h_eq, h_lim_eq] at hcm
  exact hcm

private lemma wF_bound (k : ℕ) (f : (Fin k → ℕ) → ℂ) (x m : (Fin k → ℕ)) :
    ‖wF k f x m‖ ≤ wBound k f m := by
  unfold wF wBound
  by_cases hx : ∏ i, (x i : ℂ) = 0
  · rw [hx, div_zero, norm_zero]
    apply div_nonneg (norm_nonneg _)
    apply Finset.prod_nonneg
    intro i _
    positivity
  · have hneC : ∀ i ∈ Finset.univ, (x i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.mp hx
    have hneN : ∀ i : Fin k, x i ≠ 0 := by
      intro i
      have h := hneC i (Finset.mem_univ i)
      exact_mod_cast h
    have hpos_xi : ∀ i : Fin k, (0 : ℝ) < (x i : ℝ) := by
      intro i
      have h : 0 < x i := Nat.pos_of_ne_zero (hneN i)
      exact_mod_cast h
    have hpos_x : 0 < ∏ i, (x i : ℝ) :=
      Finset.prod_pos (fun i _ => hpos_xi i)
    have hpos_d : 0 < ∏ i, ((m i + 1 : ℕ) : ℝ) := by
      apply Finset.prod_pos
      intro i _
      have : 0 < m i + 1 := Nat.succ_pos _
      exact_mod_cast this
    have hle_nat : ∏ i, ((x i / (m i + 1)) * (m i + 1)) ≤ ∏ i, x i := by
      apply Finset.prod_le_prod
      intro i _
      exact Nat.div_mul_le_self _ _
    have hle_real : (∏ i, ((x i / (m i + 1) : ℕ) : ℝ)) * (∏ i, ((m i + 1 : ℕ) : ℝ))
        ≤ ∏ i, (x i : ℝ) := by
      have hcast : (((∏ i, ((x i / (m i + 1)) * (m i + 1)) : ℕ)) : ℝ)
          ≤ (((∏ i, x i : ℕ)) : ℝ) := Nat.cast_le.mpr hle_nat
      rw [Nat.cast_prod, Nat.cast_prod] at hcast
      have hmul : ∀ i : Fin k, (((x i / (m i + 1)) * (m i + 1) : ℕ) : ℝ)
          = ((x i / (m i + 1) : ℕ) : ℝ) * ((m i + 1 : ℕ) : ℝ) := by
        intro i
        push_cast
        ring
      simp only [hmul, Finset.prod_mul_distrib] at hcast
      exact hcast
    have hnorm : ‖(wG k f (fun i => m i + 1) * ∏ i, (((x i / (m i + 1) : ℕ)) : ℂ)) / ∏ i, (x i : ℂ)‖
        = ‖wG k f (fun i => m i + 1)‖ *
            ((∏ i, ((x i / (m i + 1) : ℕ) : ℝ)) / (∏ i, (x i : ℝ))) := by
      rw [Complex.norm_div, Complex.norm_mul, Complex.norm_prod, Complex.norm_prod]
      simp only [Complex.norm_natCast]
      ring
    rw [hnorm]
    have hle_div : (∏ i, ((x i / (m i + 1) : ℕ) : ℝ)) / (∏ i, (x i : ℝ))
        ≤ 1 / (∏ i, ((m i + 1 : ℕ) : ℝ)) := by
      have hne_x : (∏ i, (x i : ℝ)) ≠ 0 := ne_of_gt hpos_x
      have hne_d : (∏ i, ((m i + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hpos_d
      rw [div_le_div_iff₀ hpos_x hpos_d]
      calc (∏ i, ((x i / (m i + 1) : ℕ) : ℝ)) * (∏ i, ((m i + 1 : ℕ) : ℝ))
          ≤ ∏ i, (x i : ℝ) := hle_real
        _ = 1 * ∏ i, (x i : ℝ) := by ring
    calc ‖wG k f (fun i => m i + 1)‖ * ((∏ i, ((x i / (m i + 1) : ℕ) : ℝ)) / (∏ i, (x i : ℝ)))
        ≤ ‖wG k f (fun i => m i + 1)‖ * (1 / (∏ i, ((m i + 1 : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hle_div (norm_nonneg _)
      _ = ‖wG k f (fun i => m i + 1)‖ / (∏ i, ((m i + 1 : ℕ) : ℝ)) := by ring

set_option linter.unusedVariables false in
/--
**Wintner's mean-value theorem in several variables.** Let $k \ge 1$ and let $f$ be a
complex-valued function on $k$-tuples of natural numbers. For a $k$-tuple
$n = (n_1, \dots, n_k)$ of positive integers put
$$
(\mu * f)(n) = \sum_{d_1 \mid n_1, \dots, d_k \mid n_k}
\mu(d_1) \cdots \mu(d_k) \, f(n_1/d_1, \dots, n_k/d_k),
$$
where $\mu$ is the Möbius function and the $d_i$ run over positive divisors. If the series
$$\sum_{m \in \mathbb{Z}_{\ge 1}^k} \frac{|(\mu * f)(m)|}{m_1 \cdots m_k}$$
converges, then
$$
\frac{1}{x_1 \cdots x_k} \sum_{n_1 = 1}^{x_1} \cdots \sum_{n_k = 1}^{x_k} f(n_1, \dots, n_k)
\to \sum_{m \in \mathbb{Z}_{\ge 1}^k} \frac{(\mu * f)(m)}{m_1 \cdots m_k}
$$
as the integers $x_1, \dots, x_k$ all tend to infinity.

Source: László Tóth,
"On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components,"
Journal of Integer Sequences 27 (2024), Article 24.8.5,
Theorem `Th_Wintner_gen`, lines 300–311,
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex>.
Proved by H. Ushiroya (2012) as a generalization of Wintner's classical one-variable theorem.
-/
theorem wintner_mean_value_multivariable
    (k : ℕ) (hk : 0 < k) (f : (Fin k → ℕ) → ℂ) :
    let mobiusConvolution : (Fin k → ℕ) → ℂ := (fun n =>
      ∑ d : (i : Fin k) → Fin (n i),
        if ∀ i, (d i : ℕ) + 1 ∣ n i then
          (∏ i, (ArithmeticFunction.moebius ((d i : ℕ) + 1) : ℂ)) *
            f (fun i => n i / ((d i : ℕ) + 1))
        else 0);
    Summable (fun m : Fin k → ℕ =>
      ‖mobiusConvolution (fun i => m i + 1)‖ /
        ∏ i, (m i + 1 : ℝ)) →
      Filter.Tendsto
        (fun x : Fin k → ℕ =>
          (∑ n : (i : Fin k) → Fin (x i), f (fun i => (n i : ℕ) + 1)) /
            ∏ i, (x i : ℂ))
        Filter.atTop
        (nhds (∑' m : Fin k → ℕ,
          mobiusConvolution (fun i => m i + 1) /
            ∏ i, (m i + 1 : ℂ))) := by
  intro mobiusConvolution hsum
  have heq : mobiusConvolution = wG k f := rfl
  have hcastR : ∀ m : Fin k → ℕ, ∏ i, ((m i + 1 : ℕ) : ℝ) = ∏ i, ((m i : ℝ) + 1) := by
    intro m
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have hcastC : ∀ m : Fin k → ℕ, ∏ i, ((m i + 1 : ℕ) : ℂ) = ∏ i, ((m i : ℂ) + 1) := by
    intro m
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have hbound_sum : Summable (wBound k f) := by
    have hEq : (wBound k f) = (fun m : Fin k → ℕ =>
      ‖mobiusConvolution (fun i => m i + 1)‖ / ∏ i, ((m i : ℝ) + 1)) := by
      funext m
      unfold wBound
      rw [← heq, hcastR]
    rw [hEq]
    simpa using hsum
  have hterm : ∀ m : Fin k → ℕ, Filter.Tendsto (fun x => wF k f x m) Filter.atTop
      (nhds (wG k f (fun i => m i + 1) / ∏ i, ((m i + 1 : ℕ) : ℂ))) :=
    fun m => wF_tendsto k f m
  have hb : ∀ᶠ _x : Fin k → ℕ in Filter.atTop, ∀ m : Fin k → ℕ, ‖wF k f _x m‖ ≤ wBound k f m :=
    Filter.Eventually.of_forall (fun x m => wF_bound k f x m)
  have hlim : Filter.Tendsto (fun x : Fin k → ℕ => ∑' m : Fin k → ℕ, wF k f x m)
      Filter.atTop (nhds (∑' m : Fin k → ℕ, wG k f (fun i => m i + 1) / ∏ i,
          ((m i + 1 : ℕ) : ℂ))) :=
    tendsto_tsum_of_dominated_convergence hbound_sum hterm hb
  have hbox := box_avg_eq_tsum k f
  have hlim_eq : (∑' m : Fin k → ℕ, wG k f (fun i => m i + 1) / ∏ i, ((m i + 1 : ℕ) : ℂ))
      = (∑' m : Fin k → ℕ, mobiusConvolution (fun i => m i + 1) / ∏ i, ((m i : ℂ) + 1)) := by
    congr 1
    funext m
    rw [← heq, hcastC]
  rw [hlim_eq] at hlim
  have hconcl : (∑' m : Fin k → ℕ, mobiusConvolution (fun i => m i + 1) / ∏ i, ((m i : ℂ) + 1))
      = (∑' m : Fin k → ℕ, mobiusConvolution (fun i => m i + 1) / ∏ i, (m i + 1 : ℂ)) := rfl
  rw [hconcl] at hlim
  exact Filter.Tendsto.congr' hbox.symm hlim

end MetaMathlibExt
end
