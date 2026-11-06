/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry1Euleriangf

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 1

Bernoulli numbers uniquely solve a shift-derivative operator identity.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry1

open scoped Nat Real BigOperators Interval Polynomial
open Filter Finset Complex Topology
open Entry1Euleriangf (chapter5DerivativeExpansion)

noncomputable section

def chapter5Entry1MinusCoeff (n : ℕ) : ℝ :=
  (bernoulli n : ℝ) / (n.factorial : ℝ)

private lemma iter_deriv_zero (n : ℕ) :
    (Polynomial.derivative^[n]) (0 : ℝ[X]) = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp

private lemma iter_deriv_C_mul (a : ℝ) (p : ℝ[X]) (n : ℕ) :
    (Polynomial.derivative^[n]) (Polynomial.C a * p)
      = Polynomial.C a * (Polynomial.derivative^[n]) p := by
  induction n generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact Polynomial.derivative_C_mul a _

private lemma eval_iter_deriv_X_pow (x : ℝ) (m n : ℕ) :
    Polynomial.eval x ((Polynomial.derivative^[n]) ((Polynomial.X : ℝ[X]) ^ m)) =
      (Nat.descFactorial m n : ℝ) * x ^ (m - n) := by
  induction n generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases m with
    | zero =>
      have hX0 : ((Polynomial.X : ℝ[X]) ^ 0) = Polynomial.C 1 := by simp
      rw [hX0]
      have hder : Polynomial.derivative (Polynomial.C (1 : ℝ)) = 0 :=
        Polynomial.derivative_C
      have h0 : (Polynomial.derivative^[k]) (Polynomial.derivative (Polynomial.C (1 : ℝ))) = 0 := by
        rw [hder]; exact iter_deriv_zero k
      have hdesc : Nat.descFactorial 0 (k + 1) = 0 := by
        cases k with
        | zero => simp [Nat.descFactorial_succ]
        | succ j => rw [Nat.descFactorial_succ]; simp
      rw [h0, hdesc]; simp
    | succ m =>
      have hder : Polynomial.derivative ((Polynomial.X : ℝ[X]) ^ (m + 1))
          = Polynomial.C ((m + 1 : ℕ) : ℝ) * Polynomial.X ^ m := by
        have h := Polynomial.derivative_X_pow (R := ℝ) (m + 1)
        rwa [Nat.add_sub_cancel] at h
      rw [hder, iter_deriv_C_mul]
      have hih := ih m
      rw [Polynomial.eval_mul, Polynomial.eval_C, hih]
      have hdesc : Nat.descFactorial (m + 1) (k + 1) = (m + 1) * Nat.descFactorial m k := by
        exact Nat.succ_descFactorial_succ m k
      have hexp : (m + 1) - (k + 1) = m - k := by omega
      rw [hdesc, hexp]
      push_cast
      ring

private lemma desc_eq_fact_div_real (m n : ℕ) (h : n ≤ m) :
    (Nat.descFactorial m n : ℝ) = (m.factorial : ℝ) / ((m - n).factorial : ℝ) := by
  have hnat := Nat.factorial_mul_descFactorial h
  have hcast : (((m - n).factorial : ℕ) : ℝ) * (Nat.descFactorial m n : ℝ)
      = (m.factorial : ℝ) := by
    exact_mod_cast hnat
  have hne : (((m - n).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [eq_div_iff hne, mul_comm]
  exact hcast

private lemma choose_eq_fact_div_real (m j : ℕ) (h : j ≤ m) :
    (Nat.choose m j : ℝ) = (m.factorial : ℝ) / ((j.factorial : ℝ) * ((m - j).factorial : ℝ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial h
  have hcast : ((Nat.choose m j : ℕ) : ℝ) * (j.factorial : ℝ) * (((m - j).factorial : ℕ) : ℝ)
      = (m.factorial : ℝ) := by
    exact_mod_cast hnat
  have hne : (j.factorial : ℝ) * (((m - j).factorial : ℕ) : ℝ) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [eq_div_iff hne]
  linarith [hcast]

private lemma desc_choose_mul_real (m n j : ℕ) (h : n + j ≤ m) :
    (Nat.descFactorial m n : ℝ) * (Nat.choose (m - n) j : ℝ)
      = (Nat.choose m j : ℝ) * (Nat.descFactorial (m - j) n : ℝ) := by
  have hn_le : n ≤ m := by omega
  have hj_le : j ≤ m := by omega
  have hjn : j ≤ m - n := by omega
  have hnj : n ≤ m - j := by omega
  have hsub : m - n - j = m - j - n := by omega
  rw [desc_eq_fact_div_real m n hn_le,
    choose_eq_fact_div_real (m - n) j hjn,
    choose_eq_fact_div_real m j hj_le,
    desc_eq_fact_div_real (m - j) n hnj,
    hsub]
  field_simp

private lemma bernoulli_sum_real (K : ℕ) :
    ∑ n ∈ Finset.range K, (Nat.choose K n : ℝ) * (bernoulli n : ℝ)
      = if K = 1 then 1 else 0 := by
  have h := sum_bernoulli K
  have hcast : ((∑ k ∈ Finset.range K, ((K.choose k : ℚ)) * bernoulli k : ℚ) : ℝ)
      = (((if K = 1 then (1 : ℚ) else 0) : ℚ) : ℝ) := by
    exact_mod_cast h
  rw [Rat.cast_sum] at hcast
  simp only [Rat.cast_mul, Rat.cast_natCast] at hcast
  rw [hcast]
  split
  · simp
  · simp

private lemma bernoulli_term_real (K n : ℕ) :
    (bernoulli n : ℝ) / (n.factorial : ℝ) * (Nat.descFactorial K n : ℝ)
      = (Nat.choose K n : ℝ) * (bernoulli n : ℝ) := by
  have hdesc := Nat.descFactorial_eq_factorial_mul_choose K n
  have hcast : ((Nat.descFactorial K n : ℕ) : ℝ)
      = ((n.factorial : ℝ)) * ((Nat.choose K n : ℕ) : ℝ) := by
    have : ((Nat.descFactorial K n : ℕ) : ℝ)
        = (((n.factorial * Nat.choose K n : ℕ)) : ℝ) := by
      rw [hdesc]
    push_cast at this
    exact this
  have hne : ((n.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hcast]
  field_simp

private lemma inner_bernoulli_sum (K : ℕ) :
    ∑ n ∈ Finset.range K, (bernoulli n : ℝ) / (n.factorial : ℝ) * (Nat.descFactorial K n : ℝ)
      = if K = 1 then 1 else 0 := by
  have : ∀ n ∈ Finset.range K, (bernoulli n : ℝ) / (n.factorial : ℝ) * (Nat.descFactorial K n : ℝ)
      = (Nat.choose K n : ℝ) * (bernoulli n : ℝ) := by
    intro n _
    exact bernoulli_term_real K n
  rw [Finset.sum_congr rfl this]
  exact bernoulli_sum_real K

private lemma pow_add_sub_pow (x h : ℝ) (N : ℕ) :
    (x + h) ^ N - x ^ N
      = ∑ j ∈ Finset.range N, (Nat.choose N j : ℝ) * x ^ j * h ^ (N - j) := by
  have hadd := add_pow x h N
  rw [Finset.sum_range_succ] at hadd
  have htop : x ^ N * h ^ (N - N) * (Nat.choose N N : ℝ) = x ^ N := by
    rw [Nat.choose_self]
    simp
  rw [htop] at hadd
  have : (x + h) ^ N = (∑ m ∈ Finset.range N, x ^ m * h ^ (N - m) * (Nat.choose N m : ℝ)) + x ^ N := hadd
  rw [this]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  ring

private def numE (a : ℕ → ℝ) (m : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), a n * h ^ n * (Nat.descFactorial m n : ℝ) * x ^ (m - n)

private lemma numE_diff_eq (a : ℕ → ℝ) (m : ℕ) (x h : ℝ) :
    numE a m (x + h) h - numE a m x h
      = ∑ n ∈ Finset.range (m + 1),
          a n * h ^ n * (Nat.descFactorial m n : ℝ)
            * (∑ j ∈ Finset.range (m - n), (Nat.choose (m - n) j : ℝ) * x ^ j * h ^ (m - n - j)) := by
  unfold numE
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn_le : n ≤ m := by
    have := Finset.mem_range.mp hn
    omega
  have hpow := pow_add_sub_pow x h (m - n)
  have : a n * h ^ n * (Nat.descFactorial m n : ℝ) * (x + h) ^ (m - n)
      - a n * h ^ n * (Nat.descFactorial m n : ℝ) * x ^ (m - n)
      = a n * h ^ n * (Nat.descFactorial m n : ℝ)
        * ((x + h) ^ (m - n) - x ^ (m - n)) := by ring
  rw [this, hpow, Finset.mul_sum]

-- Closed form after swapping sums
private lemma numE_diff_closed (a : ℕ → ℝ) (m : ℕ) (x h : ℝ) :
    numE a m (x + h) h - numE a m x h
      = ∑ j ∈ Finset.range m,
          x ^ j * (h ^ (m - j) * (Nat.choose m j : ℝ)
            * (∑ n ∈ Finset.range (m - j), a n * (Nat.descFactorial (m - j) n : ℝ))) := by
  rw [numE_diff_eq]
  set F : ℕ → ℕ → ℝ := fun n j =>
    if j < m - n then
      a n * h ^ n * (Nat.descFactorial m n : ℝ)
        * ((Nat.choose (m - n) j : ℝ) * x ^ j * h ^ (m - n - j))
    else 0 with hF
  have hF_eq : ∀ n ∈ Finset.range (m + 1),
      a n * h ^ n * (Nat.descFactorial m n : ℝ)
        * (∑ j ∈ Finset.range (m - n), (Nat.choose (m - n) j : ℝ) * x ^ j * h ^ (m - n - j))
      = ∑ j ∈ Finset.range (m + 1), F n j := by
    intro n hn
    have hsub : Finset.range (m - n) ⊆ Finset.range (m + 1) := by
      intro y hy
      have hy' : y < m - n := Finset.mem_range.mp hy
      exact Finset.mem_range.mpr (by omega)
    have h1 : ∑ j ∈ Finset.range (m + 1), F n j
        = ∑ j ∈ Finset.range (m - n), F n j := by
      apply Eq.symm
      apply Finset.sum_subset hsub
      intro j _ hj2
      have hneg : ¬ j < m - n := fun hlt => hj2 (Finset.mem_range.mpr hlt)
      simp only [hF, if_neg hneg]
    rw [h1]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < m - n := Finset.mem_range.mp hj
    simp only [hF, if_pos hjlt]
  rw [Finset.sum_congr rfl hF_eq]
  rw [Finset.sum_comm]
  have hdrop : ∑ j ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1), F n j
      = ∑ j ∈ Finset.range m, ∑ n ∈ Finset.range (m + 1), F n j := by
    cases m with
    | zero => simp [hF]
    | succ m =>
      rw [Finset.sum_range_succ]
      have hm0 : ∑ n ∈ Finset.range (m + 1 + 1), F n (m + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro n _
        simp only [hF]
        rw [if_neg (by omega)]
      rw [hm0, add_zero]
  rw [hdrop]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  have hinner : ∑ n ∈ Finset.range (m + 1), F n j
      = ∑ n ∈ Finset.range (m - j),
          a n * h ^ n * (Nat.descFactorial m n : ℝ)
            * ((Nat.choose (m - n) j : ℝ) * x ^ j * h ^ (m - n - j)) := by
    have hsub2 : Finset.range (m - j) ⊆ Finset.range (m + 1) := by
      intro y hy
      have hy' : y < m - j := Finset.mem_range.mp hy
      exact Finset.mem_range.mpr (by omega)
    have h1 : ∑ n ∈ Finset.range (m + 1), F n j
        = ∑ n ∈ Finset.range (m - j), F n j := by
      apply Eq.symm
      apply Finset.sum_subset hsub2
      intro n _ hn2
      have hneg : ¬ j < m - n := by
        have : ¬ n < m - j := fun hlt => hn2 (Finset.mem_range.mpr hlt)
        omega
      simp only [hF, if_neg hneg]
    rw [h1]
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt : n < m - j := Finset.mem_range.mp hn
    have hpos : j < m - n := by omega
    simp only [hF, if_pos hpos]
  rw [hinner]
  have hfact : ∀ n ∈ Finset.range (m - j),
      a n * h ^ n * (Nat.descFactorial m n : ℝ)
        * ((Nat.choose (m - n) j : ℝ) * x ^ j * h ^ (m - n - j))
      = x ^ j * (h ^ (m - j) * (Nat.choose m j : ℝ) * (a n * (Nat.descFactorial (m - j) n : ℝ))) := by
    intro n hn
    have hnlt : n < m - j := Finset.mem_range.mp hn
    have hle : n + j ≤ m := by omega
    have hexp : n + (m - n - j) = m - j := by omega
    have hdc := desc_choose_mul_real m n j hle
    have hpow : h ^ n * h ^ (m - n - j) = h ^ (m - j) := by
      rw [← pow_add, hexp]
    have hrr : a n * h ^ n * (Nat.descFactorial m n : ℝ)
        * ((Nat.choose (m - n) j : ℝ) * x ^ j * h ^ (m - n - j))
        = x ^ j * (h ^ n * h ^ (m - n - j)) * ((Nat.descFactorial m n : ℝ) * (Nat.choose (m - n) j : ℝ)) * a n := by
      ring
    rw [hrr, hpow, hdc]
    ring
  rw [Finset.sum_congr rfl hfact, Finset.mul_sum, Finset.mul_sum]

private lemma numE_bernoulli_diff (m : ℕ) (x h : ℝ) :
    numE (fun n => (bernoulli n : ℝ) / (n.factorial : ℝ)) m (x + h) h
      - numE (fun n => (bernoulli n : ℝ) / (n.factorial : ℝ)) m x h
      = h * (m : ℝ) * x ^ (m - 1) := by
  rw [numE_diff_closed]
  cases m with
  | zero =>
    simp
  | succ m =>
    have hinner : ∀ j ∈ Finset.range (m + 1),
        (∑ n ∈ Finset.range (m + 1 - j),
          (bernoulli n : ℝ) / (n.factorial : ℝ) * (Nat.descFactorial (m + 1 - j) n : ℝ))
        = if m + 1 - j = 1 then 1 else 0 := by
      intro j _
      exact inner_bernoulli_sum (m + 1 - j)
    have hterm : ∀ j ∈ Finset.range (m + 1),
        x ^ j * (h ^ (m + 1 - j) * (Nat.choose (m + 1) j : ℝ)
          * (∑ n ∈ Finset.range (m + 1 - j),
            (bernoulli n : ℝ) / (n.factorial : ℝ) * (Nat.descFactorial (m + 1 - j) n : ℝ)))
        = if j = m then h * ((m : ℝ) + 1) * x ^ m else 0 := by
      intro j hj
      have hjlt : j < m + 1 := Finset.mem_range.mp hj
      by_cases hjj : j = m
      · rw [hjj]
        have hmj : m + 1 - m = 1 := by omega
        have hch : (Nat.choose (m + 1) m : ℝ) = (m : ℝ) + 1 := by
          have hnat : Nat.choose (m + 1) m = m + 1 := Nat.choose_succ_self_right m
          rw [hnat]
          push_cast
          ring
        have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
        rw [hinner m hmem, hmj, hch]
        simp only [if_true]
        ring
      · have hne : m + 1 - j ≠ 1 := by omega
        rw [hinner j hj, if_neg hne, if_neg hjj]
        ring
    rw [Finset.sum_congr rfl hterm]
    have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
    have hsum : ∑ j ∈ Finset.range (m + 1), (if j = m then h * ((m : ℝ) + 1) * x ^ m else 0)
        = h * ((m : ℝ) + 1) * x ^ m := by
      rw [Finset.sum_ite_eq']
      simp [hmem]
    rw [hsum]
    have hexp : m + 1 - 1 = m := Nat.add_sub_cancel m 1
    have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hexp, hcast]

private lemma desc_zero_of_lt {i n : ℕ} (h : i < n) : i.descFactorial n = 0 := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : i < k
    · rw [Nat.descFactorial_succ, ih hk, mul_zero]
    · have hik : i = k := by omega
      subst hik
      rw [Nat.descFactorial_succ]
      simp

private lemma iter_deriv_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ[X]) (n : ℕ) :
    (Polynomial.derivative^[n]) (∑ i ∈ s, g i) = ∑ i ∈ s, (Polynomial.derivative^[n]) (g i) := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih]
    exact Polynomial.derivative_sum

private lemma eval_expansion (a : ℕ → ℝ) (h x : ℝ) (phi : ℝ[X]) :
    Polynomial.eval x (chapter5DerivativeExpansion a h phi)
      = ∑ n ∈ range (phi.natDegree + 1),
        (a n * h ^ n) * Polynomial.eval x ((Polynomial.derivative^[n]) phi) := by
  unfold chapter5DerivativeExpansion
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.eval_mul, Polynomial.eval_C]

private lemma eval_iter_deriv_phi (phi : ℝ[X]) (y : ℝ) (n : ℕ) :
    Polynomial.eval y ((Polynomial.derivative^[n]) phi)
      = ∑ i ∈ range (phi.natDegree + 1),
        phi.coeff i * (Nat.descFactorial i n : ℝ) * y ^ (i - n) := by
  have hphi : phi
      = ∑ i ∈ range (phi.natDegree + 1), Polynomial.C (phi.coeff i) * Polynomial.X ^ i :=
    Polynomial.as_sum_range_C_mul_X_pow phi
  nth_rewrite 1 [hphi]
  rw [iter_deriv_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iter_deriv_C_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_iter_deriv_X_pow]
  ring

private lemma eval_expansion_X_pow (a : ℕ → ℝ) (h x : ℝ) (m : ℕ) :
    Polynomial.eval x (chapter5DerivativeExpansion a h ((Polynomial.X : ℝ[X]) ^ m))
      = numE a m x h := by
  have hnd : ((Polynomial.X : ℝ[X]) ^ m).natDegree = m := Polynomial.natDegree_X_pow m
  unfold chapter5DerivativeExpansion numE
  rw [hnd, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_iter_deriv_X_pow]
  ring

private lemma monomial_eval_identity (m : ℕ) (x h : ℝ) :
    Polynomial.eval x (Polynomial.taylor h
        (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h ((Polynomial.X : ℝ[X]) ^ m))
        - chapter5DerivativeExpansion chapter5Entry1MinusCoeff h ((Polynomial.X : ℝ[X]) ^ m))
      = Polynomial.eval x (Polynomial.C h * ((Polynomial.X : ℝ[X]) ^ m).derivative) := by
  have hbern : numE chapter5Entry1MinusCoeff m (x + h) h - numE chapter5Entry1MinusCoeff m x h
      = h * (m : ℝ) * x ^ (m - 1) :=
    numE_bernoulli_diff m x h
  rw [Polynomial.eval_sub, Polynomial.taylor_eval, eval_expansion_X_pow, eval_expansion_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    hbern]
  ring

private lemma monomial_poly_identity (m : ℕ) (h : ℝ) :
    Polynomial.taylor h
        (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h ((Polynomial.X : ℝ[X]) ^ m))
        - chapter5DerivativeExpansion chapter5Entry1MinusCoeff h ((Polynomial.X : ℝ[X]) ^ m)
      = Polynomial.C h * ((Polynomial.X : ℝ[X]) ^ m).derivative := by
  apply Polynomial.funext
  intro x
  exact monomial_eval_identity m x h

private lemma general_eval_identity (phi : ℝ[X]) (x h : ℝ) :
    Polynomial.eval x (Polynomial.taylor h
        (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi)
        - chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi)
      = Polynomial.eval x (Polynomial.C h * phi.derivative) := by
  rw [Polynomial.eval_sub, Polynomial.taylor_eval]
  have hexp : ∀ y : ℝ,
      Polynomial.eval y (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi)
      = ∑ i ∈ Finset.range (phi.natDegree + 1),
        phi.coeff i * numE chapter5Entry1MinusCoeff i y h := by
    intro y
    rw [eval_expansion]
    have h1 : ∀ n ∈ Finset.range (phi.natDegree + 1),
        (chapter5Entry1MinusCoeff n * h ^ n)
          * Polynomial.eval y ((Polynomial.derivative^[n]) phi)
        = ∑ i ∈ Finset.range (phi.natDegree + 1),
          phi.coeff i
            * (chapter5Entry1MinusCoeff n * h ^ n * (Nat.descFactorial i n : ℝ) * y ^ (i - n)) := by
      intro n _
      rw [eval_iter_deriv_phi phi y n, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i ≤ phi.natDegree := by
      have hmem := Finset.mem_range.mp hi
      omega
    have hsub : Finset.range (i + 1) ⊆ Finset.range (phi.natDegree + 1) := by
      intro z hz
      have hz' : z < i + 1 := Finset.mem_range.mp hz
      exact Finset.mem_range.mpr (by omega)
    have h2 : ∑ n ∈ Finset.range (phi.natDegree + 1),
          phi.coeff i
            * (chapter5Entry1MinusCoeff n * h ^ n * (Nat.descFactorial i n : ℝ) * y ^ (i - n))
        = phi.coeff i * numE chapter5Entry1MinusCoeff i y h := by
      rw [← Finset.mul_sum]
      congr 1
      have h3 : ∑ n ∈ Finset.range (phi.natDegree + 1),
            chapter5Entry1MinusCoeff n * h ^ n * (Nat.descFactorial i n : ℝ) * y ^ (i - n)
          = ∑ n ∈ Finset.range (i + 1),
            chapter5Entry1MinusCoeff n * h ^ n * (Nat.descFactorial i n : ℝ) * y ^ (i - n) := by
        apply Eq.symm
        apply Finset.sum_subset hsub
        intro n _ hn2
        have hlt : i < n := by
          have hnn : ¬ n < i + 1 := fun hlt => hn2 (Finset.mem_range.mpr hlt)
          omega
        rw [desc_zero_of_lt hlt]
        simp
      rw [h3]
      unfold numE
      apply Finset.sum_congr rfl
      intro n _
      ring
    exact h2
  rw [hexp (x + h), hexp x, ← Finset.sum_sub_distrib]
  have hbern : ∀ i : ℕ,
      numE chapter5Entry1MinusCoeff i (x + h) h - numE chapter5Entry1MinusCoeff i x h
      = h * (i : ℝ) * x ^ (i - 1) := fun i => numE_bernoulli_diff i x h
  have hdiff : ∀ i ∈ Finset.range (phi.natDegree + 1),
      phi.coeff i * numE chapter5Entry1MinusCoeff i (x + h) h
        - phi.coeff i * numE chapter5Entry1MinusCoeff i x h
      = phi.coeff i * (h * (i : ℝ) * x ^ (i - 1)) := by
    intro i _
    have hmul : phi.coeff i * numE chapter5Entry1MinusCoeff i (x + h) h
        - phi.coeff i * numE chapter5Entry1MinusCoeff i x h
        = phi.coeff i
          * (numE chapter5Entry1MinusCoeff i (x + h) h - numE chapter5Entry1MinusCoeff i x h) := by
      ring
    rw [hmul, hbern i]
  rw [Finset.sum_congr rfl hdiff]
  have hederiv : Polynomial.eval x phi.derivative
      = ∑ i ∈ Finset.range (phi.natDegree + 1), phi.coeff i * (i : ℝ) * x ^ (i - 1) := by
    have hphi : phi = ∑ i ∈ Finset.range (phi.natDegree + 1),
        Polynomial.C (phi.coeff i) * Polynomial.X ^ i :=
      Polynomial.as_sum_range_C_mul_X_pow phi
    nth_rewrite 1 [hphi]
    rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  rw [Polynomial.eval_mul, Polynomial.eval_C, hederiv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma general_poly_identity (phi : ℝ[X]) (h : ℝ) :
    Polynomial.taylor h
        (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi)
        - chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi
      = Polynomial.C h * phi.derivative := by
  apply Polynomial.funext
  intro x
  exact general_eval_identity phi x h

private lemma T_eq_of_hyp (a : ℕ → ℝ)
    (H : ∀ (phi : ℝ[X]) (h : ℝ),
      Polynomial.taylor h (chapter5DerivativeExpansion a h phi)
        - chapter5DerivativeExpansion a h phi = Polynomial.C h * phi.derivative)
    (m : ℕ) :
    (∑ n ∈ Finset.range m, a n * (Nat.descFactorial m n : ℝ))
      = (if m = 1 then (1 : ℝ) else 0) := by
  have hH := H ((Polynomial.X : ℝ[X]) ^ m) 1
  have heval : Polynomial.eval 0 (Polynomial.taylor 1
        (chapter5DerivativeExpansion a 1 ((Polynomial.X : ℝ[X]) ^ m))
        - chapter5DerivativeExpansion a 1 ((Polynomial.X : ℝ[X]) ^ m))
      = Polynomial.eval 0 (Polynomial.C 1 * (((Polynomial.X : ℝ[X]) ^ m).derivative)) := by
    rw [hH]
  rw [Polynomial.eval_sub, Polynomial.taylor_eval, eval_expansion_X_pow,
    eval_expansion_X_pow] at heval
  have hrhs : Polynomial.eval 0 (Polynomial.C (1 : ℝ) * (((Polynomial.X : ℝ[X]) ^ m).derivative))
      = (if m = 1 then (1 : ℝ) else 0) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.derivative_X_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    cases m with
    | zero => simp
    | succ k =>
      cases k with
      | zero => simp
      | succ k => simp
  rw [hrhs] at heval
  have hclosed := numE_diff_closed a m 0 1
  simp only [zero_add] at heval hclosed
  rw [hclosed] at heval
  have hcollapse : ∀ (G : ℕ → ℝ), ∑ j ∈ Finset.range m, (0 : ℝ) ^ j * G j
      = (if m = 0 then 0 else G 0) := by
    intro G
    cases m with
    | zero => simp
    | succ k =>
      rw [Finset.sum_range_succ']
      have hzero : ∑ i ∈ Finset.range k, (0 : ℝ) ^ (i + 1) * G (i + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [pow_succ]
        simp
      rw [hzero, zero_add, pow_zero, one_mul, if_neg (Nat.succ_ne_zero k)]
  have hcol := hcollapse (fun j => (1 : ℝ) ^ (m - j) * (Nat.choose m j : ℝ)
    * (∑ n ∈ Finset.range (m - j), a n * (Nat.descFactorial (m - j) n : ℝ)))
  rw [hcol] at heval
  cases m with
  | zero => simp
  | succ k =>
    have hm0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    rw [if_neg hm0] at heval
    have hG0 : (1 : ℝ) ^ (k + 1 - 0) * (Nat.choose (k + 1) 0 : ℝ)
        * (∑ n ∈ Finset.range (k + 1 - 0), a n * (Nat.descFactorial (k + 1 - 0) n : ℝ))
        = ∑ n ∈ Finset.range (k + 1), a n * (Nat.descFactorial (k + 1) n : ℝ) := by
      simp
    rw [hG0] at heval
    exact heval

private lemma coeff_eq_of_T_eq (a : ℕ → ℝ)
    (hT : ∀ K : ℕ, (∑ n ∈ Finset.range K, a n * (Nat.descFactorial K n : ℝ))
      = (∑ n ∈ Finset.range K,
        chapter5Entry1MinusCoeff n * (Nat.descFactorial K n : ℝ))) :
    a = chapter5Entry1MinusCoeff := by
  have key : ∀ K n : ℕ, n < K → a n = chapter5Entry1MinusCoeff n := by
    intro K
    induction K with
    | zero =>
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ K ih =>
      intro n hn
      by_cases h : n < K
      · exact ih n h
      · have hnK : n = K := Nat.le_antisymm (Nat.le_of_lt_succ hn) (not_lt.mp h)
        rw [hnK]
        have hK := hT (K + 1)
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at hK
        have hprev : ∑ x ∈ Finset.range K, a x * (Nat.descFactorial (K + 1) x : ℝ)
            = ∑ x ∈ Finset.range K,
              chapter5Entry1MinusCoeff x * (Nat.descFactorial (K + 1) x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [ih x (Finset.mem_range.mp hx)]
        rw [hprev] at hK
        have hD : (Nat.descFactorial (K + 1) K : ℝ) ≠ 0 := by
          have hfact : Nat.descFactorial (K + 1) K = (K + 1).factorial := by
            have hle : K ≤ K + 1 := Nat.le_succ K
            have hdiv := Nat.descFactorial_eq_div hle
            have hsub : K + 1 - K = 1 := by omega
            rw [hdiv, hsub, Nat.factorial_one, Nat.div_one]
          rw [hfact]
          exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hcan := add_left_cancel_iff.mp hK
        exact mul_right_cancel₀ hD hcan
  funext n
  exact key (n + 1) n (Nat.lt_succ_self n)

/-- **Ramanujan's operator identity for the Bernoulli numbers.** For a sequence
$a = (a_n)_{n \ge 0}$ of real numbers, a real number $h$ and a real polynomial $\varphi$ of
degree $d$ (with $d = 0$ for $\varphi = 0$), let
$S_a(h, \varphi) = \sum_{n=0}^{d} a_n h^n \varphi^{(n)}$. Let $b_n = B_n / n!$, where $B_n$ are
the Bernoulli numbers with $B_1 = -\tfrac12$. Then for every real polynomial $\varphi$ and every
real $h$, $S_b(h, \varphi)(x + h) - S_b(h, \varphi)(x) = h \varphi'(x)$ as polynomials in $x$.
Moreover $b$ is the only such sequence: if a real sequence $a$ satisfies
$S_a(h, \varphi)(x + h) - S_a(h, \varphi)(x) = h \varphi'(x)$ for every real polynomial $\varphi$
and every real $h$, then $a_n = b_n$ for every $n$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5.
Proves `Wanted` entry `ramanujan_part1_ch5_entry1`. The source's shift `p(x) ↦ p(x + h)` is
`Polynomial.taylor h`, and the operator `∑ aₙ hⁿ Dⁿ` is
`Entry1Euleriangf.chapter5DerivativeExpansion`.
-/
theorem ramanujan_part1_ch5_entry1 :
    (∀ (phi : ℝ[X]) (h : ℝ),
      Polynomial.taylor h
          (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi) -
        chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi =
      Polynomial.C h * phi.derivative) ∧
    ∀ a : ℕ → ℝ,
      (∀ (phi : ℝ[X]) (h : ℝ),
        Polynomial.taylor h (chapter5DerivativeExpansion a h phi) -
            chapter5DerivativeExpansion a h phi =
          Polynomial.C h * phi.derivative) →
      a = chapter5Entry1MinusCoeff := by
  constructor
  · intro phi h
    exact general_poly_identity phi h
  · intro a H
    have hTBer : ∀ K : ℕ, (∑ n ∈ Finset.range K,
        chapter5Entry1MinusCoeff n * (Nat.descFactorial K n : ℝ))
        = (if K = 1 then (1 : ℝ) else 0) := by
      intro K
      have hterm : ∀ n ∈ Finset.range K,
          chapter5Entry1MinusCoeff n * (Nat.descFactorial K n : ℝ)
          = (bernoulli n : ℝ) / (n.factorial : ℝ) * (Nat.descFactorial K n : ℝ) := by
        intro n _
        rfl
      rw [Finset.sum_congr rfl hterm]
      exact inner_bernoulli_sum K
    have hTa : ∀ K : ℕ, (∑ n ∈ Finset.range K, a n * (Nat.descFactorial K n : ℝ))
        = (if K = 1 then (1 : ℝ) else 0) :=
      fun K => T_eq_of_hyp a H K
    have hTeq : ∀ K : ℕ, (∑ n ∈ Finset.range K, a n * (Nat.descFactorial K n : ℝ))
        = (∑ n ∈ Finset.range K,
          chapter5Entry1MinusCoeff n * (Nat.descFactorial K n : ℝ)) := by
      intro K
      rw [hTa K, hTBer K]
    exact coeff_eq_of_T_eq a hTeq

end

end Entry1

end MathlibExt.Analysis.Ramanujan.Part1Ch5
