/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.FibStepConvolution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
# Convolution of an even number of consecutive Fibonacci step sequences

The denominator identity for the Fibonacci step generating functions writes each
consecutive difference as a monomial times the product of the pair. Multiplying these
identities over the pairs expresses the product of the differences as a monomial times
the product of all `2 * l` consecutive generating functions. Comparing coefficients,
identified with the composition sums `compProdSum`, gives the even convolution identity.

Statements from Robert Frontczak and Karol Gryszka,
"General Convolution Sums Involving Fibonacci `m`-Step
Numbers", *Journal of Integer Sequences* 27 (2024),
Article 24.8.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex>).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

/-- **Sums over compositions.** Given integer sequences $a_0, \dots, a_{r-1}$ and a natural
number $n$, the sum over the compositions $K(r, n)$ of $n$ into $r$ nonnegative parts is the
sum, over all $(k_0, \dots, k_{r-1}) \in \mathbb{N}^r$ with $k_0 + \dots + k_{r-1} = n$, of
$\prod_{i=0}^{r-1} a_i(k_i)$. -/
def compProdSum {r : ℕ} (seqs : Fin r → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ (Finset.univ : Finset (Fin r → Fin (n + 1))).filter
      (fun k => ∑ i, (k i).val = n), ∏ i, seqs i (k i).val

private lemma length_fibStepSeq (m n : ℕ) : (fibStepSeq m n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [fibStepSeq, ih]

private lemma getD_fibStepSeq (m n k : ℕ) (hk : k ≤ n) :
    (fibStepSeq m n).getD k 0 = fibStep m k := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    obtain h | rfl := lt_or_eq_of_le hk
    · cases n with
      | zero =>
        obtain rfl : k = 0 := by omega
        rfl
      | succ n =>
        rw [fibStepSeq, List.getD_append _ _ _ _ (by simpa [length_fibStepSeq] using h)]
        exact ih (by omega)
    · rfl

private lemma fibStep_add_two (m n : ℕ) :
    fibStep m (n + 2) = ∑ j ∈ Finset.Icc 1 m, fibStep m (n + 2 - j) := by
  rw [fibStep, fibStepSeq, List.getD_append_right _ _ _ _ (by simp [length_fibStepSeq])]
  simp only [length_fibStepSeq, Nat.sub_self, List.getD_cons_zero]
  exact Finset.sum_congr rfl fun j hj =>
    getD_fibStepSeq m (n + 1) _ (by have := (Finset.mem_Icc.mp hj).1; omega)

open PowerSeries

private lemma coeff_shift (m j n : ℕ) :
    coeff n (X ^ j * fibStepGF m) = (fibStep m (n - j) : ℚ) := by
  rw [coeff_X_pow_mul']
  split_ifs with hj
  · exact coeff_mk ..
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    rfl

private lemma fibStepGF_denom (m : ℕ) :
    (1 - ∑ j ∈ Finset.Icc 1 m, X ^ j) * fibStepGF m = X := by
  ext n
  simp only [sub_mul, one_mul, Finset.sum_mul, map_sub, map_sum, coeff_shift, coeff_X]
  rw [fibStepGF, coeff_mk]
  have h0 : fibStep m 0 = 0 := rfl
  match n with
  | 0 => simp [h0]
  | 1 =>
    have hz (j : ℕ) (hj : j ∈ Finset.Icc 1 m) : (fibStep m (1 - j) : ℚ) = 0 := by
      simp [Nat.sub_eq_zero_of_le (Finset.mem_Icc.mp hj).1, h0]
    simp [Finset.sum_eq_zero hz, show fibStep m 1 = 1 from rfl]
  | n + 2 => simp [fibStep_add_two m n]

private lemma fibStepGF_sub_succ (m : ℕ) :
    fibStepGF m - fibStepGF (m + 1) =
      -(X ^ m) * fibStepGF m * fibStepGF (m + 1) := by
  have hm := fibStepGF_denom m
  have hs := fibStepGF_denom (m + 1)
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), pow_succ] at hs
  apply X_mul_cancel
  linear_combination fibStepGF (m + 1) * hm - fibStepGF m * hs

private lemma diff_single (t : ℕ) :
    fibStepGF (t + 1) - fibStepGF t = X ^ t * fibStepGF t * fibStepGF (t + 1) := by
  have h := fibStepGF_sub_succ t
  linear_combination -h

private lemma shift_succ (l m : ℕ) :
    (l + 1) * (m + (l + 1) - 1) = l * (m + l - 1) + (m + 2 * l) := by
  cases l with
  | zero => simp
  | succ l =>
    have e1 : m + (l + 1 + 1) - 1 = m + l + 1 := by omega
    have e2 : m + (l + 1) - 1 = m + l := by omega
    rw [e1, e2]
    ring

private lemma coeff_prod_mk_aux (r : ℕ) :
    ∀ (g : Fin r → ℕ → ℚ) (n N : ℕ), n ≤ N →
      coeff n (∏ j, PowerSeries.mk (g j)) =
        ∑ k ∈ (Finset.univ : Finset (Fin r → Fin (N + 1))).filter
          (fun k => ∑ i, (k i).val = n), ∏ i, g i (k i).val := by
  induction r with
  | zero =>
    intro g n N hN
    have hU := Finset.univ_unique (α := Fin 0 → Fin (N + 1))
    rw [hU]
    by_cases hn : n = 0
    · subst hn
      simp
    · have hn' : ¬ (0 = n) := fun h => hn h.symm
      simp [hn, hn']
  | succ r ih =>
    intro g n N hN
    have hProd : (∏ j, PowerSeries.mk (g j)) =
        PowerSeries.mk (g 0) * ∏ j : Fin r, PowerSeries.mk (g j.succ) :=
      Fin.prod_univ_succ _
    rw [hProd]
    simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_mk]
    have hMid : ∀ (t : Fin (N + 1)) (s : Fin r → Fin (N + 1)),
        (if ∑ i, (((Fin.consEquiv (fun _ : Fin (r + 1) => Fin (N + 1))) (t, s)) i).val
            = n then
          ∏ i, g i ((((Fin.consEquiv (fun _ : Fin (r + 1) => Fin (N + 1))) (t, s))) i).val
          else (0 : ℚ)) =
        (if t.val + ∑ i, (s i).val = n then
          g 0 t.val * ∏ i : Fin r, g i.succ (s i).val else 0) := by
      intro t s
      rw [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero]
      have hS : (∑ i : Fin r, ((Fin.cons
            (α := fun _ : Fin (r + 1) => Fin (N + 1)) (t, s).1 (t, s).2 i.succ).val : ℕ)) =
          ∑ i : Fin r, (((t, s).2 i).val : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.cons_succ]
      have hP : (∏ i : Fin r, g i.succ ((Fin.cons
            (α := fun _ : Fin (r + 1) => Fin (N + 1)) (t, s).1 (t, s).2 i.succ).val : ℕ)) =
          ∏ i : Fin r, g i.succ (((t, s).2 i).val : ℕ) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Fin.cons_succ]
      rw [hS, hP]
    have hInner : ∀ (t : Fin (N + 1)),
        (∑ s : Fin r → Fin (N + 1), (if t.val + ∑ i, (s i).val = n then
          g 0 t.val * ∏ i : Fin r, g i.succ (s i).val else (0 : ℚ))) =
        (if t.val ≤ n then g 0 t.val *
          (∑ s ∈ (Finset.univ : Finset (Fin r → Fin (N + 1))).filter
            (fun s => ∑ i, (s i).val = n - t.val),
            ∏ i : Fin r, g i.succ (s i).val) else 0) := by
      intro t
      by_cases ht : t.val ≤ n
      · rw [ite_eq_left ht, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : ∑ i, (s i).val = n - t.val
        · have hP : t.val + ∑ i, (s i).val = n := by omega
          rw [ite_eq_left hP, ite_eq_left hs]
        · have hP : ¬ (t.val + ∑ i, (s i).val = n) := by omega
          rw [ite_eq_right hP, ite_eq_right hs]
      · rw [ite_eq_right ht]
        apply Finset.sum_eq_zero
        intro s _
        have hP : ¬ (t.val + ∑ i, (s i).val = n) := by omega
        exact ite_eq_right hP
    have hRHS : (∑ k ∈ (Finset.univ : Finset (Fin (r + 1) → Fin (N + 1))).filter
          (fun k => ∑ i, (k i).val = n), ∏ i, g i (k i).val) =
        ∑ k ∈ Finset.range n.succ,
          g 0 k * (∑ s ∈ (Finset.univ : Finset (Fin r → Fin (N + 1))).filter
            (fun s => ∑ i, (s i).val = n - k), ∏ i : Fin r, g i.succ (s i).val) := by
      rw [Finset.sum_filter]
      have hRe := (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => Fin (N + 1)))
        (fun k => if ∑ i, (k i).val = n then ∏ i, g i (k i).val else (0 : ℚ))).symm
      rw [hRe, Fintype.sum_prod_type]
      simp only [hMid, hInner]
      rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ n then g 0 k *
        (∑ s ∈ (Finset.univ : Finset (Fin r → Fin (N + 1))).filter
          (fun s => ∑ i, (s i).val = n - k), ∏ i : Fin r, g i.succ (s i).val) else 0)]
      have hSub : Finset.range n.succ ⊆ Finset.range (N + 1) :=
        Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
      have hVan : ∀ k ∈ Finset.range (N + 1), k ∉ Finset.range n.succ →
          (if k ≤ n then g 0 k * (∑ s ∈ (Finset.univ : Finset (Fin r → Fin (N + 1))).filter
            (fun s => ∑ i, (s i).val = n - k), ∏ i : Fin r, g i.succ (s i).val) else (0 : ℚ)) =
              0 := by
        intro k _ hk
        have hk' : ¬ k ≤ n := by
          rw [Finset.mem_range, not_lt] at hk
          omega
        rw [ite_eq_right hk']
      rw [(Finset.sum_subset hSub hVan).symm]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by
        have hkm := Finset.mem_range.mp hk
        omega
      rw [ite_eq_left hkn]
    rw [hRHS]
    apply Finset.sum_congr rfl
    intro k hk
    have hle : n - k ≤ N := by
      have hkm := Finset.mem_range.mp hk
      omega
    congr 1
    exact ih (fun j t => g j.succ t) (n - k) N hle

private lemma prod_diff_eq (l m : ℕ) :
    ∏ j : Fin l, (fibStepGF (m + 2 * j.val + 1) - fibStepGF (m + 2 * j.val)) =
      X ^ (l * (m + l - 1)) * ∏ j : Fin (2 * l), fibStepGF (m + j.val) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hLHS : (∏ j : Fin (l + 1),
          (fibStepGF (m + 2 * j.val + 1) - fibStepGF (m + 2 * j.val))) =
        (∏ j : Fin l, (fibStepGF (m + 2 * j.val + 1) - fibStepGF (m + 2 * j.val))) *
          (fibStepGF (m + 2 * l + 1) - fibStepGF (m + 2 * l)) := by
      rw [Fin.prod_univ_castSucc]
      congr 1
    have hRHS : (∏ j : Fin (2 * (l + 1)), fibStepGF (m + j.val)) =
        (∏ j : Fin (2 * l), fibStepGF (m + j.val)) *
          fibStepGF (m + 2 * l) * fibStepGF (m + 2 * l + 1) := by
      rw [show 2 * (l + 1) = 2 * l + 1 + 1 by ring, Fin.prod_univ_castSucc,
        Fin.prod_univ_castSucc]
      congr 1
    rw [hLHS, hRHS, ih, diff_single, shift_succ, pow_add]
    ring

private lemma coeff_compProdSum_fibStep (r : ℕ) (s : Fin r → ℕ) (t : ℕ) :
    ((compProdSum (fun j k => fibStep (s j) k) t : ℤ) : ℚ) =
      coeff t (∏ j : Fin r, fibStepGF (s j)) := by
  have h := coeff_prod_mk_aux r (fun j k => ((fibStep (s j) k : ℤ) : ℚ)) t t le_rfl
  unfold compProdSum fibStepGF at ⊢
  push_cast at ⊢
  exact h.symm

private lemma coeff_compProdSum_diff (l m t : ℕ) :
    ((compProdSum (fun (j : Fin l) k =>
      fibStep (m + 2 * j.val + 1) k - fibStep (m + 2 * j.val) k) t : ℤ) : ℚ) =
      coeff t (∏ j : Fin l,
        (fibStepGF (m + 2 * j.val + 1) - fibStepGF (m + 2 * j.val))) := by
  have h := coeff_prod_mk_aux l
    (fun j k => (((fibStep (m + 2 * j.val + 1) k - fibStep (m + 2 * j.val) k : ℤ)) : ℚ))
    t t le_rfl
  have hmk : ∀ j : Fin l, PowerSeries.mk
        (fun k => (((fibStep (m + 2 * j.val + 1) k - fibStep (m + 2 * j.val) k : ℤ)) : ℚ))
      = fibStepGF (m + 2 * j.val + 1) - fibStepGF (m + 2 * j.val) := by
    intro j
    ext k
    simp only [PowerSeries.coeff_mk, map_sub, fibStepGF]
    exact Int.cast_sub _ _
  simp only [hmk] at h
  unfold compProdSum at ⊢
  push_cast at h ⊢
  exact h.symm

-- Coefficient comparison gives the result without using the positivity hypotheses.
set_option linter.unusedVariables false in
/-- **Convolution of an even number of consecutive Fibonacci step sequences.** Write $F^{(s)}_k$
for the Fibonacci $s$-step numbers, and write $\sum_{K(r,N)}$ for a sum over all
$(k_1, \dots, k_r) \in \mathbb{N}^r$ with $k_1 + \dots + k_r = N$. For all natural numbers
$\ell \ge 1$, $m \ge 1$ and $n \ge \ell(m + \ell - 1)$,
$$
\sum_{K(2\ell, n - \ell(m + \ell - 1))} \prod_{j=0}^{2\ell-1} F^{(m+j)}_{k_{j+1}} =
\sum_{K(\ell, n)} \prod_{j=0}^{\ell-1} \left(F^{(m+2j+1)}_{k_{j+1}} - F^{(m+2j)}_{k_{j+1}}\right).
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 35. -/
theorem compProdSum_even (l m n : ℕ) (hl : 1 ≤ l)
    (hm : 1 ≤ m) (hn : l * (m + l - 1) ≤ n) :
    @compProdSum (2 * l) (fun (j : Fin (2 * l)) k =>
        fibStep (m + j.val) k) (n - l * (m + l - 1)) =
      @compProdSum l (fun (j : Fin l) k =>
        fibStep (m + 2 * j.val + 1) k - fibStep (m + 2 * j.val) k) n
    := by
  apply Int.cast_injective (α := ℚ)
  rw [coeff_compProdSum_fibStep, coeff_compProdSum_diff, prod_diff_eq]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel, PowerSeries.coeff_X_pow_mul]

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
