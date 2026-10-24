/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Complex.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry1Euleriangf
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry4
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 3

For `p ≠ -1`, the operator `φ ↦ ∑ aₙ hⁿ φ⁽ⁿ⁾` with
`aₙ = (-1)ⁿ ψₙ(p) / (n! (p + 1)ⁿ⁺¹)`, where `ψₙ` is the Eulerian polynomial evaluated at
`-p`, inverts `φ(x) ↦ φ(x + h) + p φ(x)` on complex polynomials, and no other coefficient
sequence does.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry3

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry1Euleriangf Entry4

noncomputable section

def chapter5Entry3Coeff (n : ℕ) (p : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * chapter5Psi n p /
    ((n.factorial : ℂ) * (p + 1) ^ (n + 1))

private theorem aux_deriv_iter_X_pow (n k : ℕ) :
    (Polynomial.derivative^[n] ((Polynomial.X ^ k : ℂ[X]))) =
      if n ≤ k then Polynomial.C ((Nat.descFactorial k n : ℕ) : ℂ) * Polynomial.X ^ (k - n)
      else 0 := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    by_cases hnk : n + 1 ≤ k
    · have hnk' : n ≤ k := Nat.le_of_succ_le hnk
      have ihk := ih k
      simp only [hnk, hnk', ite_true] at ihk ⊢
      have hkn : k - n = (k - (n + 1)) + 1 := by omega
      have e2 : (k - (n + 1) + 1) - 1 = k - (n + 1) := by omega
      rw [Function.iterate_succ_apply', ihk, hkn, Polynomial.derivative_C_mul_X_pow, e2]
      have hdesc : Nat.descFactorial k (n + 1) = Nat.descFactorial k n * (k - n) := by
        rw [Nat.descFactorial_succ]
        ring
      rw [hdesc, hkn]
      push_cast
      ring
    · have ihk := ih k
      simp only [hnk, ite_false] at ⊢
      by_cases hn : n ≤ k
      · simp only [hn, ite_true] at ihk
        have hkn0 : k - n = 0 := by omega
        rw [Function.iterate_succ_apply', ihk, hkn0]
        simp
      · simp only [hn, ite_false] at ihk
        rw [Function.iterate_succ_apply', ihk]
        simp

private theorem aux_Dexp_X_pow (a : ℕ → ℂ) (h : ℂ) (k : ℕ) :
    chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X]) =
      ∑ n ∈ range (k + 1), Polynomial.C (a n * h ^ n * ((Nat.descFactorial k n : ℕ) : ℂ)) *
        Polynomial.X ^ (k - n) := by
  unfold chapter5DerivativeExpansion
  rw [Polynomial.natDegree_X_pow]
  apply Finset.sum_congr rfl
  intro n hn
  have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  rw [aux_deriv_iter_X_pow n k]
  simp only [hnk, ite_true]
  rw [← mul_assoc, ← Polynomial.C_mul]

private theorem aux_eval_Dexp_X_pow (a : ℕ → ℂ) (h x : ℂ) (k : ℕ) :
    (chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval x =
      ∑ n ∈ range (k + 1), a n * h ^ n * ((Nat.descFactorial k n : ℕ) : ℂ) * x ^ (k - n) := by
  rw [aux_Dexp_X_pow]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem aux_eval_Sexp (h x : ℂ) (q : Polynomial ℂ) :
    (Polynomial.taylor h q).eval x = q.eval (x + h) := by
  rw [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]

private theorem aux_eval_Dexp_at_self (a : ℕ → ℂ) (h : ℂ) (k : ℕ) :
    (chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval h =
      h ^ k * ∑ n ∈ range (k + 1), a n * ((Nat.descFactorial k n : ℕ) : ℂ) := by
  rw [aux_eval_Dexp_X_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hpow : h ^ n * h ^ (k - n) = h ^ k := by
    rw [← pow_add]
    congr 1
    omega
  calc a n * h ^ n * ↑(Nat.descFactorial k n) * h ^ (k - n)
      = (h ^ n * h ^ (k - n)) * (a n * ↑(Nat.descFactorial k n)) := by ring
    _ = h ^ k * (a n * ↑(Nat.descFactorial k n)) := by rw [hpow]

private theorem aux_eval_Dexp_at_zero (a : ℕ → ℂ) (h : ℂ) (k : ℕ) :
    (chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval 0 =
      a k * h ^ k * ((k.factorial : ℕ) : ℂ) := by
  rw [aux_eval_Dexp_X_pow]
  rw [Finset.sum_eq_single k]
  · rw [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
  · intro n hn hnk
    have hle : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hlt : k - n ≠ 0 := by omega
    rw [zero_pow hlt]
    ring
  · intro habs
    simp at habs

private def auxRec (p : ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, (∑ n ∈ range (k + 1), a n * ((Nat.descFactorial k n : ℕ) : ℂ)) +
    p * (a k * ((k.factorial : ℕ) : ℂ)) = if k = 0 then 1 else 0

private theorem aux_eval_Op_at_zero (p : ℂ) (a : ℕ → ℂ) (h : ℂ) (k : ℕ) :
    (Polynomial.taylor h (chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])) +
      Polynomial.C p * chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval 0 =
      (chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval h +
        p * ((chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval 0) := by
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, aux_eval_Sexp]
  simp only [zero_add]

private theorem aux_eval_Dexp_one_one (a : ℕ → ℂ) (k : ℕ) :
    (chapter5DerivativeExpansion a 1 (Polynomial.X ^ k : ℂ[X])).eval 1 =
      ∑ n ∈ range (k + 1), a n * ((Nat.descFactorial k n : ℕ) : ℂ) := by
  rw [aux_eval_Dexp_X_pow]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [one_pow, mul_one]

private theorem aux_eval_Dexp_one_zero (a : ℕ → ℂ) (k : ℕ) :
    (chapter5DerivativeExpansion a 1 (Polynomial.X ^ k : ℂ[X])).eval 0 =
      a k * ((k.factorial : ℕ) : ℂ) := by
  have h := aux_eval_Dexp_at_zero a 1 k
  simpa using h

private theorem aux_eval_Dexp (a : ℕ → ℂ) (h : ℂ) (psi : Polynomial ℂ) (y : ℂ) :
    (chapter5DerivativeExpansion a h psi).eval y =
    ∑ n ∈ range (psi.natDegree + 1), a n * h ^ n * (((Polynomial.derivative^[n]) psi).eval y) := by
  unfold chapter5DerivativeExpansion
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval_mul, Polynomial.eval_C]

private theorem aux_Dexp_eval_big (a : ℕ → ℂ) (h y : ℂ) (k N : ℕ) (hN : k ≤ N) :
    (chapter5DerivativeExpansion a h (Polynomial.X ^ k : ℂ[X])).eval y =
    ∑ n ∈ range (N + 1),
      a n * h ^ n * (((Polynomial.derivative^[n]) (Polynomial.X ^ k : ℂ[X])).eval y) := by
  rw [aux_eval_Dexp a h (Polynomial.X ^ k : ℂ[X]) y, Polynomial.natDegree_X_pow]
  have hsub : Finset.range (k + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  apply Finset.sum_subset hsub
  intro n hn hnmem
  have hnk : ¬ n ≤ k := by
    intro hle
    have hmem : n ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    exact hnmem hmem
  have hder : (((Polynomial.derivative^[n]) (Polynomial.X ^ k : ℂ[X])).eval y) = 0 := by
    rw [aux_deriv_iter_X_pow n k]
    simp only [hnk, ite_false, Polynomial.eval_zero]
  rw [hder, mul_zero]

private theorem aux_rec_of_op_eq (p : ℂ) (a : ℕ → ℂ)
    (hop : ∀ (h : ℂ) (phi : Polynomial ℂ),
      Polynomial.taylor h (chapter5DerivativeExpansion a h phi) +
        Polynomial.C p * chapter5DerivativeExpansion a h phi = phi) :
    auxRec p a := by
  intro k
  have hk := hop 1 (Polynomial.X ^ k : ℂ[X])
  have heval :
      (Polynomial.taylor 1 (chapter5DerivativeExpansion a 1 (Polynomial.X ^ k : ℂ[X])) +
      Polynomial.C p * chapter5DerivativeExpansion a 1 (Polynomial.X ^ k : ℂ[X])).eval 0 =
      ((Polynomial.X ^ k : ℂ[X]).eval 0) := by rw [hk]
  rw [aux_eval_Op_at_zero, aux_eval_Dexp_one_one, aux_eval_Dexp_one_zero] at heval
  rw [heval]
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · simp only [hk0, ite_false]
    have : ((Polynomial.X ^ k : ℂ[X]).eval (0 : ℂ)) = 0 := by
      rw [Polynomial.eval_pow, Polynomial.eval_X]
      exact zero_pow hk0
    rw [this]

private theorem aux_rec_unique (p : ℂ) (hp : p ≠ -1) (a c : ℕ → ℂ)
    (ha : auxRec p a) (hc : auxRec p c) : ∀ n, a n = c n := by
  have hp1 : (p + 1 : ℂ) ≠ 0 := by
    have : p - (-1) ≠ 0 := sub_ne_zero.mpr hp
    simpa using this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hak := ha n
    have hck := hc n
    rw [Finset.sum_range_succ] at hak hck
    rw [Nat.descFactorial_self] at hak hck
    have hfact : (((n.factorial : ℕ)) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hsum : ∑ x ∈ range n, a x * ↑(Nat.descFactorial n x) =
        ∑ x ∈ range n, c x * ↑(Nat.descFactorial n x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    have hdiff : (∑ x ∈ range n, c x * ↑(Nat.descFactorial n x) +
        a n * ↑n.factorial + p * (a n * ↑n.factorial)) -
        (∑ x ∈ range n, c x * ↑(Nat.descFactorial n x) +
        c n * ↑n.factorial + p * (c n * ↑n.factorial)) = 0 := by
      rw [hsum] at hak
      rw [hak, hck, sub_self]
    have hdiff2 : (a n * ((n.factorial : ℕ) : ℂ) + p * (a n * ((n.factorial : ℕ) : ℂ))) -
        (c n * ((n.factorial : ℕ) : ℂ) + p * (c n * ((n.factorial : ℕ) : ℂ))) = 0 := by
      have hring : (∑ x ∈ range n, c x * ↑(Nat.descFactorial n x) +
          a n * ↑n.factorial + p * (a n * ↑n.factorial)) -
          (∑ x ∈ range n, c x * ↑(Nat.descFactorial n x) +
          c n * ↑n.factorial + p * (c n * ↑n.factorial)) =
          (a n * ↑n.factorial + p * (a n * ↑n.factorial)) -
          (c n * ↑n.factorial + p * (c n * ↑n.factorial)) := by ring
      rw [hring] at hdiff
      exact hdiff
    have hfactor : (a n - c n) * ((p + 1) * ((n.factorial : ℕ) : ℂ)) =
        (a n * ((n.factorial : ℕ) : ℂ) + p * (a n * ((n.factorial : ℕ) : ℂ))) -
        (c n * ((n.factorial : ℕ) : ℂ) + p * (c n * ((n.factorial : ℕ) : ℂ))) := by ring
    have key : (a n - c n) * ((p + 1) * ((n.factorial : ℕ) : ℂ)) = 0 := by
      rw [hfactor]
      exact hdiff2
    have hprod : (p + 1) * ((n.factorial : ℕ) : ℂ) ≠ 0 :=
      mul_ne_zero hp1 hfact
    have hsub0 : a n - c n = 0 :=
      (mul_eq_zero.mp key).resolve_right hprod
    exact sub_eq_zero.mp hsub0

private theorem aux_E_unfold (n k : ℕ) : eulerianNumber (n + 1) k =
    (k + 1) * eulerianNumber n k +
      (n + 1 - k) * (if k = 0 then 0 else eulerianNumber n (k - 1)) := rfl

private theorem aux_E_strict_vanish : ∀ n k : ℕ, n + 1 ≤ k → eulerianNumber n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    intro k hk
    rw [aux_E_unfold]
    have e1 : eulerianNumber n k = 0 := ih k (by omega)
    have e2 : (if k = 0 then (0:ℕ) else eulerianNumber n (k - 1)) = 0 := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · simp only [hk0, ite_false]
        apply ih
        omega
    rw [e1, e2]
    simp

private theorem aux_E_diag_vanish (n : ℕ) : eulerianNumber (n + 1) (n + 1) = 0 := by
  rw [aux_E_unfold]
  have e1 : eulerianNumber n (n + 1) = 0 := aux_E_strict_vanish n (n + 1) (by omega)
  rw [e1]
  simp

private noncomputable def auxQ (j : ℕ) (t : ℂ) : ℂ :=
  ∑ i ∈ range (j + 1), (eulerianNumber j i : ℂ) * t ^ i

private noncomputable def auxV (j : ℕ) (t : ℂ) : ℂ :=
  ∑ i ∈ range (j + 1), (i : ℂ) * (eulerianNumber j i : ℂ) * t ^ i

private theorem aux_Q_top_zero (k : ℕ) (t : ℂ) :
    (eulerianNumber (k + 1) (k + 1) : ℂ) * t ^ (k + 1) = 0 := by
  rw [aux_E_diag_vanish]
  simp

private theorem aux_Q_succ (k : ℕ) (t : ℂ) :
    auxQ (k + 1) t = (1 + k * t) * auxQ k t + (1 - t) * auxV k t := by
  unfold auxQ auxV
  rw [Finset.sum_range_succ, aux_Q_top_zero, add_zero]
  have hexpand : ∀ m ∈ range (k + 1),
      ((eulerianNumber (k + 1) m : ℕ) : ℂ) * t ^ m =
      ((m + 1 : ℕ) : ℂ) * ((eulerianNumber k m : ℕ) : ℂ) * t ^ m +
        ((((k + 1 - m : ℕ)) : ℂ) *
          if m = 0 then 0 else ((eulerianNumber k (m - 1) : ℕ) : ℂ)) * t ^ m := by
    intro m hm
    rw [aux_E_unfold]
    push_cast
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ m ∈ range (k + 1), ((m + 1 : ℕ) : ℂ) * ((eulerianNumber k m : ℕ) : ℂ) * t ^ m =
      (∑ m ∈ range (k + 1), ((eulerianNumber k m : ℕ) : ℂ) * t ^ m) +
      (∑ m ∈ range (k + 1), (m : ℂ) * ((eulerianNumber k m : ℕ) : ℂ) * t ^ m) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    push_cast
    ring
  have h2 : ∑ m ∈ range (k + 1), ((((k + 1 - m : ℕ)) : ℂ) *
      (if m = 0 then (0:ℂ) else ((eulerianNumber k (m - 1) : ℕ) : ℂ))) * t ^ m =
      t * (∑ l ∈ range (k + 1), (((k : ℕ) : ℂ) * ((eulerianNumber k l : ℕ) : ℂ) * t ^ l -
        (l : ℂ) * ((eulerianNumber k l : ℕ) : ℂ) * t ^ l)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, pow_zero, ite_true, mul_zero, add_zero, mul_one]
    rw [Finset.sum_range_succ]
    have hlast : ((k : ℕ) : ℂ) * ((eulerianNumber k k : ℕ) : ℂ) * t ^ k -
        (k : ℂ) * ((eulerianNumber k k : ℕ) : ℂ) * t ^ k = 0 := by ring
    rw [hlast, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hsub : k + 1 - (m + 1) = k - m := by
      have hmlt : m < k := Finset.mem_range.mp hm
      omega
    rw [hsub]
    by_cases hm0 : m + 1 = 0
    · omega
    · simp only [hm0, ite_false]
      have hsub2 : m + 1 - 1 = m := by omega
      rw [hsub2]
      rw [pow_succ]
      have hmk : m ≤ k := Nat.le_of_lt (Finset.mem_range.mp hm)
      rw [Nat.cast_sub hmk]
      ring
  rw [h1, h2]
  simp only [Finset.mul_sum, mul_sub]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private noncomputable def auxS (k : ℕ) (t : ℂ) : ℂ :=
  ∑ j ∈ range (k + 1), (Nat.choose k j : ℂ) * auxQ j t * (t - 1) ^ (k - j)

private noncomputable def auxM (k : ℕ) (t : ℂ) : ℂ := auxS k t - t * auxQ k t

private theorem aux_M_zero (t : ℂ) : auxM 0 t = 1 - t := by
  have e00 : ((eulerianNumber 0 0 : ℕ) : ℂ) = 1 := by
    have h : eulerianNumber 0 0 = 1 := rfl
    rw [h]
    simp
  unfold auxM auxS auxQ
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul,
    pow_zero, mul_one, Nat.sub_self]
  rw [e00]
  ring

/-! Polynomial reframing of the Eulerian convolution identity. -/

private theorem aux_choose_mul_pred (k j : ℕ) :
    Nat.choose k j * (k - j) = k * Nat.choose (k - 1) j := by
  cases k with
  | zero =>
    cases j with
    | zero => rfl
    | succ j => simp [Nat.choose_eq_zero_of_lt (Nat.zero_lt_succ j)]
  | succ k =>
    have hk1 : k + 1 - 1 = k := Nat.add_sub_cancel k 1
    rw [hk1]
    have h := Nat.choose_mul_succ_eq k j
    calc Nat.choose (k + 1) j * (k + 1 - j)
        = Nat.choose k j * (k + 1) := h.symm
      _ = (k + 1) * Nat.choose k j := mul_comm _ _

private theorem aux_mul_choose_succ (k i : ℕ) :
    (i + 1) * Nat.choose k (i + 1) = k * Nat.choose (k - 1) i := by
  have h1 := Nat.choose_succ_right_eq k i
  have h2 := aux_choose_mul_pred k i
  calc (i + 1) * Nat.choose k (i + 1)
      = Nat.choose k (i + 1) * (i + 1) := mul_comm _ _
    _ = Nat.choose k i * (k - i) := h1
    _ = k * Nat.choose (k - 1) i := h2

private theorem aux_E00 : eulerianNumber 0 0 = 1 := rfl

private theorem aux_E10 : eulerianNumber 1 0 = 1 := rfl

private theorem aux_E11 : eulerianNumber 1 1 = 0 := aux_E_diag_vanish 0

private theorem aux_E20 : eulerianNumber 2 0 = 1 := rfl

private theorem aux_E21 : eulerianNumber 2 1 = 1 := rfl

private theorem aux_E22 : eulerianNumber 2 2 = 0 := aux_E_diag_vanish 1

private noncomputable def Qpoly (j : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (j + 1), Polynomial.C (eulerianNumber j i : ℂ) * Polynomial.X ^ i

private noncomputable def Vpoly (j : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (j + 1),
    Polynomial.C ((i : ℂ) * (eulerianNumber j i : ℂ)) * Polynomial.X ^ i

private noncomputable def Spoly (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (k + 1),
    Polynomial.C (Nat.choose k j : ℂ) * Qpoly j * (Polynomial.X - 1) ^ (k - j)

private noncomputable def Tpoly (k : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (k + 1),
    Polynomial.C (Nat.choose k i : ℂ) * Qpoly (i + 1) *
      (Polynomial.X - 1) ^ (k - i)

private noncomputable def Upoly (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (k + 1),
    Polynomial.C (Nat.choose k j : ℂ) * Vpoly j * (Polynomial.X - 1) ^ (k - j)

private noncomputable def Mpoly (k : ℕ) : Polynomial ℂ :=
  Spoly k - Polynomial.X * Qpoly k

private theorem Qpoly_eval (j : ℕ) (t : ℂ) : (Qpoly j).eval t = auxQ j t := by
  unfold Qpoly auxQ
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem Vpoly_eval (j : ℕ) (t : ℂ) : (Vpoly j).eval t = auxV j t := by
  unfold Vpoly auxV
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem Spoly_eval (k : ℕ) (t : ℂ) : (Spoly k).eval t = auxS k t := by
  unfold Spoly auxS
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Qpoly_eval,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]

private theorem Mpoly_eval (k : ℕ) (t : ℂ) : (Mpoly k).eval t = auxM k t := by
  unfold Mpoly auxM
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Spoly_eval,
    Qpoly_eval]

private theorem Qpoly_zero : Qpoly 0 = 1 := by
  unfold Qpoly
  rw [Finset.sum_range_one]
  simp [aux_E00]

private theorem Qpoly_one : Qpoly 1 = 1 := by
  unfold Qpoly
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [aux_E10, aux_E11]

private theorem Vpoly_zero : Vpoly 0 = 0 := by
  unfold Vpoly
  rw [Finset.sum_range_one]
  simp

private theorem Vpoly_one : Vpoly 1 = 0 := by
  unfold Vpoly
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [aux_E11]

private theorem Qpoly_succ (k : ℕ) :
    Qpoly (k + 1) = (1 + Polynomial.C (k : ℂ) * Polynomial.X) * Qpoly k +
      (1 - Polynomial.X) * Vpoly k := by
  apply Polynomial.funext
  intro t
  have h := aux_Q_succ k t
  rw [Qpoly_eval]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, Qpoly_eval,
    Vpoly_eval]
  exact h

private theorem Vpoly_eq_X_deriv_Qpoly (j : ℕ) :
    Vpoly j = Polynomial.X * (Qpoly j).derivative := by
  unfold Vpoly Qpoly
  rw [Polynomial.derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, mul_one]
  by_cases hi0 : i = 0
  · subst hi0
    simp
  · have hpow : (Polynomial.X : Polynomial ℂ) ^ (i - 1) * Polynomial.X =
        Polynomial.X ^ i := by
      have hi1 : i - 1 + 1 = i := by omega
      calc (Polynomial.X : Polynomial ℂ) ^ (i - 1) * Polynomial.X
          = Polynomial.X ^ (i - 1) * Polynomial.X ^ 1 := by rw [pow_one]
        _ = Polynomial.X ^ ((i - 1) + 1) := by rw [pow_add]
        _ = Polynomial.X ^ i := by rw [hi1]
    calc Polynomial.C ((i : ℂ) * (eulerianNumber j i : ℂ)) * Polynomial.X ^ i
        = Polynomial.C ((eulerianNumber j i : ℂ) * (i : ℂ)) * Polynomial.X ^ i := by
          rw [mul_comm (i : ℂ)]
      _ = Polynomial.C (eulerianNumber j i : ℂ) * Polynomial.C (i : ℂ) *
            Polynomial.X ^ i := by
          rw [Polynomial.C_mul]
      _ = Polynomial.X * (Polynomial.C (eulerianNumber j i : ℂ) *
            (Polynomial.C (i : ℂ) * Polynomial.X ^ (i - 1))) := by
          rw [← hpow]
          ring

private theorem Spoly_succ (k : ℕ) :
    Spoly (k + 1) = (Polynomial.X - 1) * Spoly k + Tpoly k := by
  have hchoose : ∀ j ∈ range (k + 1),
      Polynomial.C (Nat.choose (k + 1) (j + 1) : ℂ) =
        Polynomial.C (Nat.choose k j : ℂ) +
          Polynomial.C (Nat.choose k (j + 1) : ℂ) := by
    intro j hj
    rw [Nat.choose_succ_succ k j, Nat.cast_add, Polynomial.C_add]
  have hpow : ∀ j ∈ range (k + 1),
      (Polynomial.X - 1 : Polynomial ℂ) ^ (k + 1 - (j + 1)) =
        (Polynomial.X - 1) ^ (k - j) := by
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have e : k + 1 - (j + 1) = k - j := by omega
    rw [e]
  have hterm : ∀ j ∈ range (k + 1),
      Polynomial.C (Nat.choose (k + 1) (j + 1) : ℂ) * Qpoly (j + 1) *
        (Polynomial.X - 1 : Polynomial ℂ) ^ (k + 1 - (j + 1)) =
        (Polynomial.C (Nat.choose k j : ℂ) * Qpoly (j + 1) *
          (Polynomial.X - 1) ^ (k - j)) +
        ((Polynomial.X - 1) * (Polynomial.C (Nat.choose k (j + 1) : ℂ) *
          Qpoly (j + 1) * (Polynomial.X - 1) ^ (k - (j + 1)))) := by
    intro j hj
    rw [hchoose j hj, hpow j hj]
    by_cases hjk2 : j < k
    · have e : k - j = (k - (j + 1)) + 1 := by omega
      rw [e, pow_succ']
      ring
    · have hjk_eq : j = k := by
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        omega
      rw [hjk_eq]
      have h0 : Polynomial.C (Nat.choose k (k + 1) : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
        simp
      rw [h0]
      simp
  have hsum : (∑ j ∈ range (k + 1),
        Polynomial.C (Nat.choose (k + 1) (j + 1) : ℂ) * Qpoly (j + 1) *
          (Polynomial.X - 1 : Polynomial ℂ) ^ (k + 1 - (j + 1))) =
      Tpoly k + (Polynomial.X - 1) *
        (∑ j ∈ range (k + 1), Polynomial.C (Nat.choose k (j + 1) : ℂ) *
          Qpoly (j + 1) * (Polynomial.X - 1) ^ (k - (j + 1))) := by
    unfold Tpoly
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j hj
  have hF0 : Polynomial.C (Nat.choose (k + 1) 0 : ℂ) * Qpoly 0 *
      (Polynomial.X - 1 : Polynomial ℂ) ^ (k + 1 - 0) =
      (Polynomial.X - 1) * (Polynomial.C (Nat.choose k 0 : ℂ) * Qpoly 0 *
        (Polynomial.X - 1) ^ (k - 0)) := by
    simp only [Nat.choose_zero_right, Nat.cast_one, Polynomial.C_1, one_mul,
      Nat.sub_zero]
    rw [pow_succ']
    ring
  have hFk1 : Polynomial.C (Nat.choose k (k + 1) : ℂ) * Qpoly (k + 1) *
      (Polynomial.X - 1 : Polynomial ℂ) ^ (k - (k + 1)) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
    simp
  have hreidx : (∑ j ∈ range (k + 1), Polynomial.C (Nat.choose k (j + 1) : ℂ) *
        Qpoly (j + 1) * (Polynomial.X - 1 : Polynomial ℂ) ^ (k - (j + 1))) +
        (Polynomial.C (Nat.choose k 0 : ℂ) * Qpoly 0 *
          (Polynomial.X - 1 : Polynomial ℂ) ^ (k - 0)) =
        Spoly k + Polynomial.C (Nat.choose k (k + 1) : ℂ) * Qpoly (k + 1) *
          (Polynomial.X - 1 : Polynomial ℂ) ^ (k - (k + 1)) := by
    have e1 := Finset.sum_range_succ' (fun j =>
      Polynomial.C (Nat.choose k j : ℂ) * Qpoly j *
        (Polynomial.X - 1 : Polynomial ℂ) ^ (k - j)) (k + 1)
    have e2 := Finset.sum_range_succ (fun j =>
      Polynomial.C (Nat.choose k j : ℂ) * Qpoly j *
        (Polynomial.X - 1 : Polynomial ℂ) ^ (k - j)) (k + 1)
    unfold Spoly
    linear_combination -e1 + e2
  rw [hFk1, add_zero] at hreidx
  have hSpoly : Spoly (k + 1) =
      (∑ j ∈ range (k + 1),
        Polynomial.C (Nat.choose (k + 1) (j + 1) : ℂ) * Qpoly (j + 1) *
          (Polynomial.X - 1 : Polynomial ℂ) ^ (k + 1 - (j + 1))) +
      (Polynomial.C (Nat.choose (k + 1) 0 : ℂ) * Qpoly 0 *
        (Polynomial.X - 1 : Polynomial ℂ) ^ (k + 1 - 0)) := by
    unfold Spoly
    rw [Finset.sum_range_succ']
  rw [hSpoly, hsum, hF0]
  linear_combination (Polynomial.X - 1) * hreidx

private theorem Tpoly_expand (k : ℕ) (hk : 1 ≤ k) :
    Tpoly k = Spoly k + Polynomial.C (k : ℂ) * Polynomial.X * Tpoly (k - 1) +
      (1 - Polynomial.X) * Upoly k := by
  have hsub : ∀ i ∈ range (k + 1),
      Polynomial.C (Nat.choose k i : ℂ) * Qpoly (i + 1) *
        (Polynomial.X - 1) ^ (k - i) =
        (Polynomial.C (Nat.choose k i : ℂ) * Qpoly i *
          (Polynomial.X - 1) ^ (k - i)) +
        (Polynomial.X * (Polynomial.C (Nat.choose k i : ℂ) *
          Polynomial.C (i : ℂ) * Qpoly i * (Polynomial.X - 1) ^ (k - i))) +
        ((1 - Polynomial.X) * (Polynomial.C (Nat.choose k i : ℂ) * Vpoly i *
          (Polynomial.X - 1) ^ (k - i))) := by
    intro i hi
    rw [Qpoly_succ i]
    ring
  have hsum : Tpoly k = Spoly k +
      (Polynomial.X * (∑ i ∈ range (k + 1), Polynomial.C (Nat.choose k i : ℂ) *
        Polynomial.C (i : ℂ) * Qpoly i * (Polynomial.X - 1) ^ (k - i))) +
      ((1 - Polynomial.X) * Upoly k) := by
    unfold Tpoly Spoly Upoly
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hsub i hi
  have hk1 : k - 1 + 1 = k := by omega
  have hJ : (∑ i ∈ range (k + 1), Polynomial.C (Nat.choose k i : ℂ) *
      Polynomial.C (i : ℂ) * Qpoly i * (Polynomial.X - 1) ^ (k - i)) =
      Polynomial.C (k : ℂ) * Tpoly (k - 1) := by
    unfold Tpoly
    rw [hk1, Finset.mul_sum, Finset.sum_range_succ']
    have hF0 : Polynomial.C (Nat.choose k 0 : ℂ) * Polynomial.C ((0 : ℕ) : ℂ) *
        Qpoly 0 * (Polynomial.X - 1) ^ (k - 0) = 0 := by simp
    rw [hF0, add_zero]
    apply Finset.sum_congr rfl
    intro i' hi'
    have hA : (((i' + 1) * Nat.choose k (i' + 1) : ℕ) : ℂ) =
        ((k * Nat.choose (k - 1) i' : ℕ) : ℂ) := by
      exact_mod_cast aux_mul_choose_succ k i'
    have hi'k : i' < k := Finset.mem_range.mp hi'
    have he : k - (i' + 1) = k - 1 - i' := by omega
    rw [he, ← Polynomial.C_mul, ← Nat.cast_mul,
      mul_comm (Nat.choose k (i' + 1)) (i' + 1), hA, Nat.cast_mul,
      Polynomial.C_mul]
    ring
  rw [hsum, hJ]
  ring

private theorem Upoly_eq (k : ℕ) (hk : 1 ≤ k) :
    Upoly k = Polynomial.X * (Spoly k).derivative -
      Polynomial.C (k : ℂ) * Polynomial.X * Spoly (k - 1) := by
  have hP : ∀ j ∈ range (k + 1),
      Polynomial.derivative ((Polynomial.X - 1 : Polynomial ℂ) ^ (k - j)) =
        Polynomial.C ((k - j : ℕ) : ℂ) * (Polynomial.X - 1) ^ (k - j - 1) := by
    intro j hj
    rw [Polynomial.derivative_pow]
    have hX1 : Polynomial.derivative (Polynomial.X - 1 : Polynomial ℂ) = 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_one, sub_zero]
    rw [hX1, mul_one]
  have hderiv : (Spoly k).derivative =
      ∑ j ∈ range (k + 1),
        (Polynomial.C (Nat.choose k j : ℂ) * (Qpoly j).derivative *
          (Polynomial.X - 1) ^ (k - j) +
        Polynomial.C (Nat.choose k j : ℂ) * Qpoly j *
          (Polynomial.C ((k - j : ℕ) : ℂ) * (Polynomial.X - 1) ^ (k - j - 1))) := by
    unfold Spoly
    rw [Polynomial.derivative_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.derivative_mul, Polynomial.derivative_C_mul, hP j hj]
  have hcast : ∀ j : ℕ, Polynomial.C (Nat.choose k j : ℂ) *
      Polynomial.C ((k - j : ℕ) : ℂ) =
      Polynomial.C (k : ℂ) * Polynomial.C (Nat.choose (k - 1) j : ℂ) := by
    intro j
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, ← Nat.cast_mul, ← Nat.cast_mul]
    congr 1
    exact_mod_cast aux_choose_mul_pred k j
  have hk1 : k - 1 + 1 = k := by omega
  have hB : (∑ j ∈ range (k + 1), Polynomial.X *
      (Polynomial.C (Nat.choose k j : ℂ) * Qpoly j *
        (Polynomial.C ((k - j : ℕ) : ℂ) * (Polynomial.X - 1) ^ (k - j - 1)))) =
      Polynomial.C (k : ℂ) * Polynomial.X * Spoly (k - 1) := by
    unfold Spoly
    rw [hk1, Finset.mul_sum]
    have hBlast : Polynomial.X * (Polynomial.C (Nat.choose k k : ℂ) * Qpoly k *
        (Polynomial.C ((k - k : ℕ) : ℂ) * (Polynomial.X - 1) ^ (k - k - 1))) = 0 := by
      simp
    rw [Finset.sum_range_succ, hBlast, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have he : k - j - 1 = k - 1 - j := by omega
    rw [he]
    linear_combination (Polynomial.X * Qpoly j * (Polynomial.X - 1) ^ (k - 1 - j)) *
      (hcast j)
  have hA : (∑ j ∈ range (k + 1), Polynomial.X *
      (Polynomial.C (Nat.choose k j : ℂ) * (Qpoly j).derivative *
        (Polynomial.X - 1) ^ (k - j))) = Upoly k := by
    unfold Upoly
    apply Finset.sum_congr rfl
    intro j hj
    rw [Vpoly_eq_X_deriv_Qpoly j]
    ring
  rw [hderiv, Finset.mul_sum]
  simp only [mul_add]
  rw [Finset.sum_add_distrib, hA, hB]
  ring

private theorem Mpoly_one : Mpoly 1 = 0 := by
  unfold Mpoly Spoly
  rw [Finset.sum_range_succ, Finset.sum_range_one, Qpoly_zero, Qpoly_one]
  simp

private theorem Mpoly_two : Mpoly 2 = 0 := by
  have hQ2 : Qpoly 2 = 1 + Polynomial.X := by
    unfold Qpoly
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [aux_E20, aux_E21, aux_E22]
  unfold Mpoly Spoly
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    Qpoly_zero, Qpoly_one, hQ2]
  simp
  simp only [Polynomial.C_ofNat]
  ring

private theorem Mpoly_main (n : ℕ) (hn : 1 ≤ n) : Mpoly n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      exact Mpoly_one
    · by_cases hn2 : n = 2
      · subst hn2
        exact Mpoly_two
      · have hn3 : 3 ≤ n := by omega
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hm : 2 ≤ m := by omega
        have hm1 : 1 ≤ m := by omega
        have hm2 : 1 ≤ m - 1 := by omega
        have hlt1 : m < m + 1 := Nat.lt_succ_self m
        have hlt2 : m - 1 < m + 1 := by omega
        have IH1 := ih m hlt1 hm1
        have IH2 := ih (m - 1) hlt2 hm2
        have hSm : Spoly m = Polynomial.X * Qpoly m := by
          unfold Mpoly at IH1
          linear_combination IH1
        have hSm1 : Spoly (m - 1) = Polynomial.X * Qpoly (m - 1) := by
          unfold Mpoly at IH2
          linear_combination IH2
        have hS := Spoly_succ m
        have hT := Tpoly_expand m hm1
        have hT' : Tpoly (m - 1) = Spoly m - (Polynomial.X - 1) * Spoly (m - 1) := by
          have h := Spoly_succ (m - 1)
          have hm0 : m - 1 + 1 = m := by omega
          rw [hm0] at h
          linear_combination -h
        have hU := Upoly_eq m hm1
        have hD : (Spoly m).derivative =
            Qpoly m + Polynomial.X * (Qpoly m).derivative := by
          have h := congrArg Polynomial.derivative hSm
          rw [Polynomial.derivative_mul, Polynomial.derivative_X] at h
          linear_combination h
        have hV := Vpoly_eq_X_deriv_Qpoly m
        have hQ := Qpoly_succ m
        unfold Mpoly
        rw [hS, hT, hT', hU, hD, hSm, hSm1, hQ, hV]
        ring

/-- Core Eulerian convolution identity: for `k ≥ 1`, `M_k(t) = 0` for all `t`. -/
private theorem aux_M_eq_zero (k : ℕ) (hk : 1 ≤ k) (t : ℂ) : auxM k t = 0 := by
  have h := Mpoly_main k hk
  rw [← Mpoly_eval, h]
  simp

/-- `auxQ` at `-p` equals `chapter5Psi`. Uses vanishing of the top Eulerian term. -/
private theorem auxQ_eq_Psi (j : ℕ) (p : ℂ) : auxQ j (-p) = chapter5Psi j p := by
  cases j with
  | zero =>
    have e00 : eulerianNumber 0 0 = 1 := rfl
    unfold auxQ chapter5Psi
    simp [e00]
  | succ j =>
    have htop := aux_Q_top_zero j (-p)
    unfold auxQ chapter5Psi
    simp only [Nat.succ_ne_zero, ite_false]
    rw [Finset.sum_range_succ, htop, add_zero]

/-- The given coefficients satisfy the recurrence. Follows from `aux_M_eq_zero`
by clearing denominators (`p + 1 ≠ 0`, factorials nonzero). -/
private theorem aux_Rec_of_coeff (p : ℂ) (hp : p ≠ -1) :
    auxRec p (fun n => chapter5Entry3Coeff n p) := by
  have hp1 : p + 1 ≠ 0 := by
    have h : p - (-1) ≠ 0 := sub_ne_zero.mpr hp
    simpa using h
  have hfact : ∀ n : ℕ, ((n.factorial : ℕ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast Nat.factorial_ne_zero n
  have hpp : ∀ m : ℕ, (p + 1 : ℂ) ^ m ≠ 0 := fun m => pow_ne_zero m hp1
  have hM : ∀ k : ℕ, 1 ≤ k → auxM k (-p) = 0 := fun k hk => aux_M_eq_zero k hk (-p)
  have hM0 : auxM 0 (-p) = 1 - (-p) := aux_M_zero (-p)
  have hQ : ∀ j : ℕ, auxQ j (-p) = chapter5Psi j p := fun j => auxQ_eq_Psi j p
  have hdesc : ∀ k n : ℕ, ((Nat.descFactorial k n : ℕ) : ℂ) =
      ((n.factorial : ℂ)) * ((Nat.choose k n : ℂ)) := fun k n => by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose k n
  have hrel : ∀ n k : ℕ, n ≤ k →
      (-1 : ℂ) ^ n * (p + 1) ^ (k - n) = (-1 : ℂ) ^ k * (-p - 1) ^ (k - n) := by
    intro n k hnk
    have hpt : p + 1 = (-1 : ℂ) * (-p - 1) := by ring
    have e : n + (k - n) = k := by omega
    rw [hpt, mul_pow, ← mul_assoc, ← pow_add, e]
  have hPk : ∀ n k : ℕ, n ≤ k →
      (p + 1 : ℂ) ^ (k + 1) = (p + 1) ^ (n + 1) * (p + 1) ^ (k - n) := by
    intro n k hnk
    have e : n + 1 + (k - n) = k + 1 := by omega
    rw [← pow_add, e]
  have hterm : ∀ k n : ℕ, n ∈ range (k + 1) →
      chapter5Entry3Coeff n p * ((Nat.descFactorial k n : ℕ) : ℂ) =
        ((-1 : ℂ) ^ k / (p + 1) ^ (k + 1)) *
          ((Nat.choose k n : ℂ) * chapter5Psi n p * (-p - 1) ^ (k - n)) := by
    intro k n hn
    have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have ne1 : ((n.factorial : ℂ)) * (p + 1) ^ (n + 1) ≠ 0 :=
      mul_ne_zero (hfact n) (hpp (n + 1))
    have ne2 : (p + 1) ^ (n + 1) * (p + 1) ^ (k - n) ≠ 0 :=
      mul_ne_zero (hpp (n + 1)) (hpp (k - n))
    unfold chapter5Entry3Coeff
    rw [hdesc k n, hPk n k hnk, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff ne1 ne2]
    linear_combination (chapter5Psi n p * (Nat.choose k n : ℂ) *
      ((n.factorial : ℂ)) * (p + 1) ^ (n + 1)) * (hrel n k hnk)
  have h2 : ∀ k : ℕ, p * (chapter5Entry3Coeff k p * ((k.factorial : ℕ) : ℂ)) =
      -(((-1 : ℂ) ^ k / (p + 1) ^ (k + 1)) * ((-p) * chapter5Psi k p)) := by
    intro k
    unfold chapter5Entry3Coeff
    field_simp [hpp (k + 1), hfact k]
  intro k
  change (∑ n ∈ range (k + 1), chapter5Entry3Coeff n p *
      ((Nat.descFactorial k n : ℕ) : ℂ)) +
      p * (chapter5Entry3Coeff k p * ((k.factorial : ℕ) : ℂ)) =
      (if k = 0 then 1 else 0)
  have h1 : (∑ n ∈ range (k + 1), chapter5Entry3Coeff n p *
      ((Nat.descFactorial k n : ℕ) : ℂ)) =
      ∑ n ∈ range (k + 1), ((-1 : ℂ) ^ k / (p + 1) ^ (k + 1)) *
        ((Nat.choose k n : ℂ) * chapter5Psi n p * (-p - 1) ^ (k - n)) :=
    Finset.sum_congr rfl (fun n hn => hterm k n hn)
  have key : (∑ n ∈ range (k + 1), chapter5Entry3Coeff n p *
      ((Nat.descFactorial k n : ℕ) : ℂ)) +
      p * (chapter5Entry3Coeff k p * ((k.factorial : ℕ) : ℂ)) =
      ((-1 : ℂ) ^ k / (p + 1) ^ (k + 1)) * auxM k (-p) := by
    unfold auxM auxS
    rw [h1]
    simp only [hQ]
    rw [mul_sub, Finset.mul_sum]
    linear_combination h2 k
  rw [key]
  by_cases hk0 : k = 0
  · subst hk0
    rw [hM0, show (if (0 : ℕ) = 0 then (1 : ℂ) else 0) = 1 from rfl]
    simp only [pow_zero, Nat.zero_add, pow_one]
    have e : (1 : ℂ) - -p = p + 1 := by ring
    rw [e]
    exact div_mul_cancel₀ 1 hp1
  · rw [hM k (by omega), mul_zero]
    simp only [hk0, ite_false]

/-- Operator identity on monomials assuming the recurrence.
Double-sum binomial computation using `ha`. -/
private theorem aux_Op_X_pow_of_Rec (p : ℂ) (a : ℕ → ℂ) (ha : auxRec p a) (h : ℂ) (m : ℕ) :
    Polynomial.taylor h (chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])) +
      Polynomial.C p * chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X]) =
      (Polynomial.X ^ m : ℂ[X]) := by
  apply Polynomial.funext
  intro x
  have hcc : ∀ (n j : ℕ), n + j ≤ m →
      Nat.choose m n * Nat.choose (m - n) j
        = Nat.choose m j * Nat.choose (m - j) n := by
    intro n j hle
    have e1 : Nat.choose m (m - n) * Nat.choose (m - n) j
        = Nat.choose m j * Nat.choose (m - j) ((m - n) - j) :=
      Nat.choose_mul (by omega : j ≤ m - n)
    have e2 : Nat.choose m (m - n) = Nat.choose m n :=
      Nat.choose_symm (by omega : n ≤ m)
    have e3 : (m - n) - j = (m - j) - n := by omega
    have e4 : Nat.choose (m - j) ((m - j) - n) = Nat.choose (m - j) n :=
      Nat.choose_symm (by omega : n ≤ m - j)
    rw [e3, e2] at e1
    rw [e1, e4]
  have hdesc_choose : ∀ (n j : ℕ), n + j ≤ m →
      ((Nat.descFactorial m n : ℕ) : ℂ) * ((Nat.choose (m - n) j : ℕ) : ℂ)
      = ((Nat.choose m j : ℕ) : ℂ) * ((Nat.descFactorial (m - j) n : ℕ) : ℂ) := by
    intro n j hle
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    have hccC : ((Nat.choose m n * Nat.choose (m - n) j : ℕ) : ℂ)
        = ((Nat.choose m j * Nat.choose (m - j) n : ℕ) : ℂ) := by
      exact_mod_cast hcc n j hle
    push_cast at hccC
    push_cast
    linear_combination (n.factorial : ℂ) * hccC
  have hdesc_eq : ∀ (j : ℕ), j ≤ m →
      ((Nat.descFactorial m (m - j) : ℕ) : ℂ)
      = ((Nat.choose m j : ℕ) : ℂ) * (((m - j).factorial : ℕ) : ℂ) := by
    intro j hjm
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm hjm]
    push_cast
    ring
  have stepA : ∀ n ∈ range (m + 1),
      a n * h ^ n * ↑(Nat.descFactorial m n) * (x + h) ^ (m - n)
      = ∑ j ∈ range (m + 1), (if n + j ≤ m then
          a n * h ^ n * ↑(Nat.descFactorial m n) *
            (x ^ j * h ^ (m - n - j) * ↑(Nat.choose (m - n) j)) else 0) := by
    intro n hn
    have hnm : n ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [add_pow, Finset.mul_sum]
    trans ∑ j ∈ range (m - n + 1),
      (if n + j ≤ m then
        a n * h ^ n * ↑(Nat.descFactorial m n) *
          (x ^ j * h ^ (m - n - j) * ↑(Nat.choose (m - n) j)) else 0)
    · apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ m - n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hnij : n + j ≤ m := by omega
      simp only [hnij, ite_true]
    · refine Finset.sum_subset ?_ ?_
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj hjmem
        have hnij : ¬ n + j ≤ m := by
          intro hle
          apply hjmem
          simp only [Finset.mem_range]
          omega
        simp only [hnij, ite_false]
  have hGj : ∀ j ∈ range (m + 1),
      (∑ n ∈ range (m - j + 1),
        a n * h ^ n * ↑(Nat.descFactorial m n) *
          (x ^ j * h ^ (m - n - j) * ↑(Nat.choose (m - n) j)))
      = x ^ j * h ^ (m - j) * ↑(Nat.choose m j) *
        (∑ n ∈ range (m - j + 1), a n * ↑(Nat.descFactorial (m - j) n)) := by
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnj : n + j ≤ m := by
      have h1 : n ≤ m - j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      omega
    have hpow : h ^ n * h ^ (m - n - j) = h ^ (m - j) := by
      have e : m - j = n + (m - n - j) := by omega
      rw [e, pow_add]
    have hdc := hdesc_choose n j hnj
    linear_combination (a n * x ^ j * (↑(Nat.descFactorial m n) * ↑(Nat.choose (m - n) j))) * hpow
      + (a n * x ^ j * h ^ (m - j)) * hdc
  have hLHS1 : (∑ n ∈ range (m + 1), a n * h ^ n * ↑(Nat.descFactorial m n) * (x + h) ^ (m - n))
      = ∑ j ∈ range (m + 1),
        x ^ j * h ^ (m - j) * ↑(Nat.choose m j) *
          (∑ n ∈ range (m - j + 1), a n * ↑(Nat.descFactorial (m - j) n)) := by
    trans ∑ n ∈ range (m + 1), ∑ j ∈ range (m + 1),
      (if n + j ≤ m then
        a n * h ^ n * ↑(Nat.descFactorial m n) *
          (x ^ j * h ^ (m - n - j) * ↑(Nat.choose (m - n) j)) else 0)
    · exact Finset.sum_congr rfl (fun n hn => stepA n hn)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      trans ∑ n ∈ range (m - j + 1),
        a n * h ^ n * ↑(Nat.descFactorial m n) *
          (x ^ j * h ^ (m - n - j) * ↑(Nat.choose (m - n) j))
      · symm
        trans ∑ n ∈ range (m - j + 1),
          (if n + j ≤ m then
            a n * h ^ n * ↑(Nat.descFactorial m n) *
              (x ^ j * h ^ (m - n - j) * ↑(Nat.choose (m - n) j)) else 0)
        · apply Finset.sum_congr rfl
          intro n hn
          have hnj : n + j ≤ m := by
            have h1 : n ≤ m - j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
            have h2 : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            omega
          simp only [hnj, ite_true]
        · refine Finset.sum_subset ?_ ?_
          · intro n hn
            simp only [Finset.mem_range] at hn ⊢
            have h2 : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            omega
          · intro n hn hnmem
            have hnj : ¬ n + j ≤ m := by
              intro hle
              apply hnmem
              simp only [Finset.mem_range]
              have h2 : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
              omega
            simp only [hnj, ite_false]
      · exact hGj j hj
  have hpterm : p * (∑ n ∈ range (m + 1), a n * h ^ n * ↑(Nat.descFactorial m n) * x ^ (m - n))
      = ∑ j ∈ range (m + 1),
        x ^ j * (p * a (m - j) * h ^ (m - j) * ↑(Nat.descFactorial m (m - j))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => m - n) ?_ ?_ ?_ ?_
    · intro n hn
      show m - n ∈ Finset.range (m + 1)
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n₁ hn₁ n₂ hn₂ heq
      have e12 : m - n₁ = m - n₂ := heq
      simp only [Finset.mem_range] at hn₁ hn₂
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨m - j, Finset.mem_range.mpr (by omega), show m - (m - j) = j from by omega⟩
    · intro n hn
      have hnm : n ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      have e : m - (m - n) = n := by omega
      change p * (a n * h ^ n * ↑(Nat.descFactorial m n) * x ^ (m - n))
        = x ^ (m - n) * (p * a (m - (m - n)) * h ^ (m - (m - n)) *
          ↑(Nat.descFactorial m (m - (m - n))))
      rw [e]
      ring
  have hper : ∀ j ∈ range (m + 1),
      (x ^ j * h ^ (m - j) * ↑(Nat.choose m j) *
        (∑ n ∈ range (m - j + 1), a n * ↑(Nat.descFactorial (m - j) n)) +
      x ^ j * (p * a (m - j) * h ^ (m - j) * ↑(Nat.descFactorial m (m - j))))
      = (x ^ j * h ^ (m - j) * ↑(Nat.choose m j)) *
        ((∑ n ∈ range (m - j + 1), a n * ↑(Nat.descFactorial (m - j) n)) +
          p * (a (m - j) * ↑((m - j).factorial))) := by
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [hdesc_eq j hjm]
    ring
  have h0 : ∀ j ∈ range (m + 1), j ≠ m →
      (x ^ j * h ^ (m - j) * ↑(Nat.choose m j) *
        (∑ n ∈ range (m - j + 1), a n * ↑(Nat.descFactorial (m - j) n)) +
      x ^ j * (p * a (m - j) * h ^ (m - j) * ↑(Nat.descFactorial m (m - j)))) = 0 := by
    intro j hj hjm'
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hmj : m - j ≠ 0 := by omega
    rw [hper j hj, ha (m - j)]
    simp only [hmj, ite_false, mul_zero]
  have hSm : (x ^ m * h ^ (m - m) * ↑(Nat.choose m m) *
        (∑ n ∈ range (m - m + 1), a n * ↑(Nat.descFactorial (m - m) n)) +
      x ^ m * (p * a (m - m) * h ^ (m - m) * ↑(Nat.descFactorial m (m - m)))) = x ^ m := by
    rw [hper m (Finset.mem_range.mpr (by omega : m < m + 1)), ha (m - m)]
    simp only [Nat.sub_self, ite_true, Nat.choose_self, pow_zero, Nat.cast_one, mul_one]
  have h1 : m ∉ range (m + 1) →
      (x ^ m * h ^ (m - m) * ↑(Nat.choose m m) *
        (∑ n ∈ range (m - m + 1), a n * ↑(Nat.descFactorial (m - m) n)) +
      x ^ m * (p * a (m - m) * h ^ (m - m) * ↑(Nat.descFactorial m (m - m)))) = 0 := by
    intro hcon
    simp at hcon
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, aux_eval_Sexp,
    aux_eval_Dexp_X_pow a h (x + h) m, aux_eval_Dexp_X_pow a h x m,
    Polynomial.eval_pow, Polynomial.eval_X, hLHS1, hpterm, ← Finset.sum_add_distrib,
    Finset.sum_eq_single m h0 h1]
  exact hSm

/-- Linearity lifting: monomial case implies general case. -/
private theorem aux_Op_eq_of_monomials (p : ℂ) (a : ℕ → ℂ)
    (hm : ∀ (h : ℂ) (m : ℕ),
      Polynomial.taylor h (chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])) +
        Polynomial.C p * chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X]) =
        (Polynomial.X ^ m : ℂ[X])) :
    ∀ (h : ℂ) (phi : Polynomial ℂ),
      Polynomial.taylor h (chapter5DerivativeExpansion a h phi) +
        Polynomial.C p * chapter5DerivativeExpansion a h phi = phi := by
  intro h phi
  have Hadd : ∀ (n : ℕ) (u v : Polynomial ℂ),
      (Polynomial.derivative^[n]) (u + v)
        = (Polynomial.derivative^[n]) u + (Polynomial.derivative^[n]) v := by
    intro n
    induction n with
    | zero => intro u v; simp
    | succ n ih =>
      intro u v
      simp only [Function.iterate_succ_apply']
      rw [ih, Polynomial.derivative_add]
  have Hscalar : ∀ (n : ℕ) (c : ℂ) (u : Polynomial ℂ),
      (Polynomial.derivative^[n]) (Polynomial.C c * u)
        = Polynomial.C c * (Polynomial.derivative^[n]) u := by
    intro n
    induction n with
    | zero => intro c u; simp
    | succ n ih =>
      intro c u
      simp only [Function.iterate_succ_apply']
      rw [ih, Polynomial.derivative_C_mul]
  have Hzero : ∀ (n : ℕ), (Polynomial.derivative^[n]) (0 : Polynomial ℂ) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, Polynomial.derivative_zero]
  have Hsum : ∀ (n : ℕ) (s : Finset ℕ) (f : ℕ → Polynomial ℂ),
      (Polynomial.derivative^[n]) (∑ i ∈ s, f i)
        = ∑ i ∈ s, (Polynomial.derivative^[n]) (f i) := by
    intro n s
    refine Finset.induction_on s ?_ ?_
    · intro f
      simp [Hzero]
    · intro b s hb ih f
      rw [Finset.sum_insert hb, Finset.sum_insert hb, Hadd _ _ _, ih f]
  have H1 : ∀ (n : ℕ) (y : ℂ), ((Polynomial.derivative^[n]) phi).eval y =
      ∑ m ∈ range (phi.natDegree + 1),
        phi.coeff m * (((Polynomial.derivative^[n]) (Polynomial.X ^ m : ℂ[X])).eval y) := by
    intro n y
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow phi, Hsum, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Hscalar, Polynomial.eval_mul, Polynomial.eval_C]
  have HD : ∀ (y : ℂ), (chapter5DerivativeExpansion a h phi).eval y =
      ∑ m ∈ range (phi.natDegree + 1),
        phi.coeff m * ((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval y) := by
    intro y
    rw [aux_eval_Dexp a h phi y]
    simp_rw [H1, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [aux_Dexp_eval_big a h y m _ (Nat.le_of_lt_succ (Finset.mem_range.mp hm)),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have Hm : ∀ (m : ℕ) (x : ℂ),
      ((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval (x + h)) +
      p * ((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval x) =
      ((Polynomial.X ^ m : ℂ[X]).eval x) := by
    intro m x
    have hmx := congrArg (fun q : Polynomial ℂ => q.eval x) (hm h m)
    rwa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      aux_eval_Sexp] at hmx
  have Hphi : ∀ (x : ℂ),
      (∑ m ∈ range (phi.natDegree + 1),
        phi.coeff m * ((Polynomial.X ^ m : ℂ[X]).eval x)) = phi.eval x := by
    intro x
    simp_rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact (Polynomial.eval_eq_sum_range x).symm
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, aux_eval_Sexp,
    HD, HD, Finset.mul_sum, ← Finset.sum_add_distrib]
  trans ∑ m ∈ range (phi.natDegree + 1), phi.coeff m * ((Polynomial.X ^ m : ℂ[X]).eval x)
  · apply Finset.sum_congr rfl
    intro m hm
    calc phi.coeff m * ((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval (x + h)) +
          p * (phi.coeff m * ((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval x))
        = phi.coeff m *
          (((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval (x + h)) +
          p * ((chapter5DerivativeExpansion a h (Polynomial.X ^ m : ℂ[X])).eval x)) := by ring
      _ = phi.coeff m * ((Polynomial.X ^ m : ℂ[X]).eval x) := by rw [Hm]
  · exact Hphi x

/-- **Eulerian-polynomial inverse of a shift-plus-multiple operator.** Let $A(n, k)$ be the
Eulerian numbers, given by $A(0, 0) = 1$, $A(0, k) = 0$ for $k \ge 1$ and
$A(n + 1, k) = (k + 1) A(n, k) + (n + 1 - k) A(n, k - 1)$, the last term read as $0$ when
$k = 0$. For $p \in \mathbb{C}$ set $\psi_0(p) = 1$ and
$\psi_n(p) = \sum_{k=0}^{n-1} A(n, k) (-p)^k$ for $n \ge 1$. For a sequence $a_0, a_1, \ldots$
of complex numbers, $h \in \mathbb{C}$ and a polynomial $\varphi \in \mathbb{C}[x]$, write
$E_{a,h} \varphi = \sum_{n=0}^{\deg \varphi} a_n h^n \varphi^{(n)}$, where $\varphi^{(n)}$ is the
$n$-th derivative. Fix $p \in \mathbb{C}$ with $p \ne -1$ and put
$c_n = \frac{(-1)^n \psi_n(p)}{n! \, (p + 1)^{n + 1}}$. Then:
(1) for every $h \in \mathbb{C}$ and every $\varphi \in \mathbb{C}[x]$, the polynomial
$f = E_{c,h} \varphi$ satisfies $f(x + h) + p f(x) = \varphi(x)$ as polynomials in $x$;
(2) if a sequence $a$ of complex numbers is such that $f = E_{a,h} \varphi$ satisfies
$f(x + h) + p f(x) = \varphi(x)$ for every $h \in \mathbb{C}$ and every $\varphi \in \mathbb{C}[x]$,
then $a_n = c_n$ for every $n \ge 0$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5.
Proves `Wanted` entry `ramanujan_part1_ch5_entry3`.
-/
theorem ramanujan_part1_ch5_entry3 (p : ℂ) (hp : p ≠ -1) :
    (∀ (h : ℂ) (phi : Polynomial ℂ),
      Polynomial.taylor h
            (chapter5DerivativeExpansion (fun n => chapter5Entry3Coeff n p) h phi) +
          Polynomial.C p *
            chapter5DerivativeExpansion (fun n => chapter5Entry3Coeff n p) h phi =
        phi) ∧
      ∀ a : ℕ → ℂ,
        (∀ (h : ℂ) (phi : Polynomial ℂ),
          Polynomial.taylor h (chapter5DerivativeExpansion a h phi) +
              Polynomial.C p * chapter5DerivativeExpansion a h phi =
            phi) →
        ∀ n : ℕ, a n = chapter5Entry3Coeff n p := by
  have hRec_c := aux_Rec_of_coeff p hp
  constructor
  · exact aux_Op_eq_of_monomials p _ (fun h m => aux_Op_X_pow_of_Rec p _ hRec_c h m)
  · intro a ha n
    have hRec_a := aux_rec_of_op_eq p a ha
    exact aux_rec_unique p hp a _ hRec_a hRec_c n

end

end Entry3

end MathlibExt.Analysis.Ramanujan.Part1Ch5
