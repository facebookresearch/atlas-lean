/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Generalized Stirling matrix factorization
-/

private theorem P_monic_aux (b c : ℝ) (k : ℕ) :
    (∏ i ∈ Finset.range k,
      (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i _
  apply Polynomial.monic_X_sub_C

private theorem P_natDegree_aux (b c : ℝ) (k : ℕ) :
    (∏ i ∈ Finset.range k,
      (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)).natDegree = k := by
  have h1 : ∀ i ∈ Finset.range k,
      ((Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)).natDegree = 1 := by
    intro i _
    exact Polynomial.natDegree_X_sub_C _
  rw [Polynomial.natDegree_prod_of_monic]
  · rw [Finset.sum_congr rfl h1]
    simp
  · intro i _
    apply Polynomial.monic_X_sub_C

private theorem coeff_top_aux (b c : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1),
      Polynomial.C (f k) *
        (∏ i ∈ Finset.range k,
          (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))).coeff n) = f n := by
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_range_succ]
  have hzero : ∀ k ∈ Finset.range n,
      ((Polynomial.C (f k) *
        (∏ i ∈ Finset.range k,
          (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))).coeff n) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hdeg : (∏ i ∈ Finset.range k,
        (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)).natDegree = k :=
      P_natDegree_aux b c k
    have hlt : (Polynomial.C (f k) *
        (∏ i ∈ Finset.range k,
          (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))).natDegree < n := by
      calc (Polynomial.C (f k) *
        (∏ i ∈ Finset.range k,
          (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))).natDegree
          ≤ (∏ i ∈ Finset.range k,
            (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)).natDegree :=
            Polynomial.natDegree_C_mul_le _ _
        _ = k := hdeg
        _ < n := hk
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  rw [Finset.sum_eq_zero hzero, zero_add]
  rw [Polynomial.coeff_C_mul]
  have hm := P_monic_aux b c n
  have hd := P_natDegree_aux b c n
  have hmc := Polynomial.Monic.coeff_natDegree hm
  rw [hd] at hmc
  rw [hmc, mul_one]

private theorem unique_aux (b c : ℝ) (f g : ℕ → ℝ) (n : ℕ)
    (h : (∑ k ∈ Finset.range (n + 1),
      Polynomial.C (f k) *
        (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) =
      (∑ k ∈ Finset.range (n + 1),
      Polynomial.C (g k) *
        (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)))) :
    ∀ k ∈ Finset.range (n + 1), f k = g k := by
  induction n generalizing f g with
  | zero =>
    intro k hk
    rw [Finset.mem_range] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have h0 := congrArg (fun p => p.coeff 0) h
    rw [coeff_top_aux b c f 0, coeff_top_aux b c g 0] at h0
    exact h0
  | succ n ih =>
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hkn : k = n + 1
    · subst hkn
      have h0 := congrArg (fun p => p.coeff (n + 1)) h
      rw [coeff_top_aux b c f (n + 1), coeff_top_aux b c g (n + 1)] at h0
      exact h0
    · have hlt : k < n + 1 := by omega
      have hk' : k ∈ Finset.range (n + 1) := by rw [Finset.mem_range]; exact hlt
      have htop : f (n + 1) = g (n + 1) := by
        have h0 := congrArg (fun p => p.coeff (n + 1)) h
        rw [coeff_top_aux b c f (n + 1), coeff_top_aux b c g (n + 1)] at h0
        exact h0
      have hsucc_f : (∑ k ∈ Finset.range (n + 1 + 1),
          Polynomial.C (f k) *
            (∏ i ∈ Finset.range k,
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) =
          (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (f k) *
            (∏ i ∈ Finset.range k,
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) +
          Polynomial.C (f (n + 1)) *
            (∏ i ∈ Finset.range (n + 1),
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)) :=
        Finset.sum_range_succ _ _
      have hsucc_g : (∑ k ∈ Finset.range (n + 1 + 1),
          Polynomial.C (g k) *
            (∏ i ∈ Finset.range k,
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) =
          (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (g k) *
            (∏ i ∈ Finset.range k,
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) +
          Polynomial.C (g (n + 1)) *
            (∏ i ∈ Finset.range (n + 1),
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)) :=
        Finset.sum_range_succ _ _
      have h2 : Polynomial.C (f (n + 1)) *
            (∏ i ∈ Finset.range (n + 1),
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)) =
            Polynomial.C (g (n + 1)) *
            (∏ i ∈ Finset.range (n + 1),
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ)) := by
        rw [htop]
      have h' : (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (f k) *
            (∏ i ∈ Finset.range k,
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) =
          (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (g k) *
            (∏ i ∈ Finset.range k,
              (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) := by
        rw [hsucc_f, hsucc_g, h2] at h
        exact add_right_cancel h
      exact ih f g h' k hk'

private theorem poly_from_fun_aux
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → ℝ)
    (hS : ∀ (a b c : ℝ) (n : ℕ) (x : ℝ),
      (∏ i ∈ Finset.range n, (x - (i : ℝ) * a)) =
        ∑ k ∈ Finset.range (n + 1), S a b c n k *
          ∏ i ∈ Finset.range k, ((x - c) - (i : ℝ) * b))
    (a b c : ℝ) (n : ℕ) :
    (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℝ) * a) : Polynomial ℝ)) =
      (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (S a b c n k) *
          (∏ i ∈ Finset.range k,
            (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) := by
  apply Polynomial.funext
  intro x
  have h := hS a b c n x
  have hL : Polynomial.eval x
      (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℝ) * a) : Polynomial ℝ)) =
      ∏ i ∈ Finset.range n, (x - (i : ℝ) * a) := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hR : Polynomial.eval x (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (S a b c n k) *
          (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (c + (i : ℝ) * b) : Polynomial ℝ))) =
      ∑ k ∈ Finset.range (n + 1), S a b c n k *
        ∏ i ∈ Finset.range k, ((x - c) - (i : ℝ) * b) := by
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [hL, hR, h]

/--
**Factorization of the generalized Stirling matrix.** Let $S$ assign to real numbers $a, b, c$
and natural numbers $n, k$ a real number $S(a, b, c; n, k)$, such that for all real $a, b, c, x$
and every natural number $n$

$$\prod_{i=0}^{n-1} (x - i a) =
\sum_{k=0}^{n} S(a, b, c; n, k) \prod_{i=0}^{k-1} (x - c - i b),$$

and $S(a, b, c; n, k) = 0$ whenever $n < k$. Then for all real $\alpha, \beta, \gamma$ and all
natural numbers $n, k$

$$S(\alpha, \beta, \gamma; n, k) = \sum_{j=0}^{n} \sum_{l=0}^{j}
S(\alpha, 0, 0; n, j)\, S(0, 0, \gamma; j, l)\, S(0, \beta, 0; l, k).$$

In matrix form, the generalized Stirling matrix with parameters $(\alpha, \beta, \gamma)$ is the
product of the matrices for $(\alpha, 0, 0)$ (first kind), $(0, 0, \gamma)$ (translation) and
$(0, \beta, 0)$ (second kind).

Proves `Wanted` entry `generalized_stirling_matrix_factorization`.

Source: Jiaqiang Pan, “Matrix Decomposition of the Unified Generalized Stirling Numbers and
Inversion of the Generalized Factorial Matrices,” Journal of Integer Sequences 15 (2012), Article 12.6.6, Theorem `t:Decomposition`, lines 250-256, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Pan/pan19.tex>.
-/
theorem generalized_stirling_matrix_factorization
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → ℝ)
    (hS : ∀ (a b c : ℝ) (n : ℕ) (x : ℝ),
      (∏ i ∈ Finset.range n, (x - (i : ℝ) * a)) =
        ∑ k ∈ Finset.range (n + 1), S a b c n k *
          ∏ i ∈ Finset.range k, ((x - c) - (i : ℝ) * b))
    (hzero : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0)
    (α β γ : ℝ) (n k : ℕ) :
    S α β γ n k =
      ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
        S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k := by
  by_cases hkn : n < k
  · rw [hzero α β γ n k hkn]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hj hl
    have hlk : l < k := by omega
    rw [hzero 0 β 0 l k hlk]
    ring
  · have hle : k ≤ n := by omega
    have hpolyS := poly_from_fun_aux S hS α β γ n
    have hpolyT :
        (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℝ) * α) : Polynomial ℝ)) =
        (∑ k' ∈ Finset.range (n + 1),
          Polynomial.C (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
            S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') *
            (∏ i ∈ Finset.range k',
              (Polynomial.X - Polynomial.C (γ + (i : ℝ) * β) : Polynomial ℝ))) := by
      apply Polynomial.funext
      intro x
      have hLQ : Polynomial.eval x
          (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℝ) * α) : Polynomial ℝ)) =
          ∏ i ∈ Finset.range n, (x - (i : ℝ) * α) := by
        rw [Polynomial.eval_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hRQ : Polynomial.eval x
          (∑ k' ∈ Finset.range (n + 1),
            Polynomial.C (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
              S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') *
              (∏ i ∈ Finset.range k',
                (Polynomial.X - Polynomial.C (γ + (i : ℝ) * β) : Polynomial ℝ))) =
          ∑ k' ∈ Finset.range (n + 1),
            (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
              S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') *
            ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by
        rw [Polynomial.eval_finsetSum]
        apply Finset.sum_congr rfl
        intro k' _
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        ring
      rw [hLQ, hRQ]
      have prod_pow : ∀ (y : ℝ) (j : ℕ), (∏ i ∈ Finset.range j, (y - (i : ℝ) * 0)) = y ^ j := by
        intro y j
        have h1 : ∀ i ∈ Finset.range j, (y - (i : ℝ) * 0) = y := by
          intro i _
          ring
        rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range]
      have prod_pow_shift : ∀ (j : ℕ), (∏ i ∈ Finset.range j, ((x - 0) - (i : ℝ) * 0)) = x ^ j := by
        intro j
        have h1 : ∀ i ∈ Finset.range j, ((x - 0) - (i : ℝ) * 0) = x := by
          intro i _
          ring
        rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range]
      have prod_pow_gamma : ∀ (l : ℕ),
          (∏ i ∈ Finset.range l, ((x - γ) - (i : ℝ) * 0)) = (x - γ) ^ l := by
        intro l
        have h1 : ∀ i ∈ Finset.range l, ((x - γ) - (i : ℝ) * 0) = (x - γ) := by
          intro i _
          ring
        rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range]
      have eA : (∏ i ∈ Finset.range n, (x - (i : ℝ) * α)) =
          ∑ j ∈ Finset.range (n + 1), S α 0 0 n j * x ^ j := by
        have h := hS α 0 0 n x
        calc (∏ i ∈ Finset.range n, (x - (i : ℝ) * α)) =
              ∑ j ∈ Finset.range (n + 1), S α 0 0 n j *
                ∏ i ∈ Finset.range j, ((x - 0) - (i : ℝ) * 0) := h
          _ = ∑ j ∈ Finset.range (n + 1), S α 0 0 n j * x ^ j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [prod_pow_shift j]
      have eB : ∀ j ∈ Finset.range (n + 1),
          x ^ j = ∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * (x - γ) ^ l := by
        intro j _
        have h := hS 0 0 γ j x
        rw [prod_pow x j] at h
        calc x ^ j = ∑ l ∈ Finset.range (j + 1), S 0 0 γ j l *
              ∏ i ∈ Finset.range l, ((x - γ) - (i : ℝ) * 0) := h
          _ = ∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * (x - γ) ^ l := by
              apply Finset.sum_congr rfl
              intro l _
              rw [prod_pow_gamma l]
      have eC : ∀ l ∈ Finset.range (n + 1),
          (x - γ) ^ l = ∑ k' ∈ Finset.range (n + 1), S 0 β 0 l k' *
            ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by
        intro l hl
        rw [Finset.mem_range] at hl
        have hl_le : l ≤ n := by omega
        set y := x - γ with hy
        have h := hS 0 β 0 l y
        rw [prod_pow y l] at h
        have hprod_eq : ∀ k' ∈ Finset.range (l + 1),
            S 0 β 0 l k' * ∏ i ∈ Finset.range k', ((y - 0) - (i : ℝ) * β) =
            S 0 β 0 l k' * ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by
          intro k' _
          congr 1
          apply Finset.prod_congr rfl
          intro i _
          rw [hy]
          ring
        have hsmall : y ^ l = ∑ k' ∈ Finset.range (l + 1), S 0 β 0 l k' *
            ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by
          calc y ^ l = ∑ k' ∈ Finset.range (l + 1), S 0 β 0 l k' *
                ∏ i ∈ Finset.range k', ((y - 0) - (i : ℝ) * β) := h
            _ = _ := Finset.sum_congr rfl hprod_eq
        have hext : (∑ k' ∈ Finset.range (l + 1), S 0 β 0 l k' *
            ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) =
            (∑ k' ∈ Finset.range (n + 1), S 0 β 0 l k' *
            ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) := by
          apply Finset.sum_subset
          · intro k' hk'
            rw [Finset.mem_range] at hk' ⊢
            omega
          · intro k' _ hk'
            rw [Finset.mem_range] at hk'
            have hlk : l < k' := by omega
            rw [hzero 0 β 0 l k' hlk, zero_mul]
        rw [hy] at hsmall
        rw [hsmall, hext]
      calc (∏ i ∈ Finset.range n, (x - (i : ℝ) * α))
          = ∑ j ∈ Finset.range (n + 1), S α 0 0 n j * x ^ j := eA
        _ = ∑ j ∈ Finset.range (n + 1), S α 0 0 n j *
              (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * (x - γ) ^ l) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [eB j hj]
        _ = ∑ j ∈ Finset.range (n + 1), S α 0 0 n j *
              (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l *
                (∑ k' ∈ Finset.range (n + 1), S 0 β 0 l k' *
                  ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β))) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply congrArg (fun v => S α 0 0 n j * v)
            apply Finset.sum_congr rfl
            intro l hl
            have hlmem : l ∈ Finset.range (n + 1) := by
              rw [Finset.mem_range] at hl ⊢
              rw [Finset.mem_range] at hj
              omega
            rw [eC l hlmem]
        _ = ∑ k' ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
                S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') *
              ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by
            have inner : ∀ j ∈ Finset.range (n + 1),
                (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l *
                  (∑ k' ∈ Finset.range (n + 1), S 0 β 0 l k' *
                    ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β))) =
                (∑ k' ∈ Finset.range (n + 1),
                  (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k') *
                  ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) := by
              intro j _
              have step : ∀ l ∈ Finset.range (j + 1),
                  S 0 0 γ j l * (∑ k' ∈ Finset.range (n + 1), S 0 β 0 l k' *
                    ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) =
                  ∑ k' ∈ Finset.range (n + 1), (S 0 0 γ j l * S 0 β 0 l k') *
                    ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by
                intro l _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k' _
                ring
              rw [Finset.sum_congr rfl step]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k' _
              rw [Finset.sum_mul]
            have step_outer : (∑ j ∈ Finset.range (n + 1), S α 0 0 n j *
                (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l *
                  (∑ k' ∈ Finset.range (n + 1), S 0 β 0 l k' *
                    ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)))) =
                (∑ j ∈ Finset.range (n + 1), S α 0 0 n j *
                (∑ k' ∈ Finset.range (n + 1),
                  (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k') *
                  ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β))) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [inner j hj]
            rw [step_outer]
            have step1 : ∀ j ∈ Finset.range (n + 1),
                S α 0 0 n j * (∑ k' ∈ Finset.range (n + 1),
                  (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k') *
                  ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) =
                ∑ k' ∈ Finset.range (n + 1), S α 0 0 n j *
                  ((∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k') *
                  ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) := by
              intro j _
              rw [Finset.mul_sum]
            rw [Finset.sum_congr rfl (fun j hj => step1 j hj)]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k' _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            have e1 : S α 0 0 n j *
                ((∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k') *
                ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β)) =
                (S α 0 0 n j * (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k')) *
                ∏ i ∈ Finset.range k', ((x - γ) - (i : ℝ) * β) := by ring
            have e2 : S α 0 0 n j * (∑ l ∈ Finset.range (j + 1), S 0 0 γ j l * S 0 β 0 l k') =
                (∑ l ∈ Finset.range (j + 1), S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l _
              ring
            rw [e1, e2]
    have heq : (∑ k' ∈ Finset.range (n + 1),
          Polynomial.C (S α β γ n k') *
            (∏ i ∈ Finset.range k',
              (Polynomial.X - Polynomial.C (γ + (i : ℝ) * β) : Polynomial ℝ))) =
        (∑ k' ∈ Finset.range (n + 1),
          Polynomial.C (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
            S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') *
            (∏ i ∈ Finset.range k',
              (Polynomial.X - Polynomial.C (γ + (i : ℝ) * β) : Polynomial ℝ))) := by
      rw [← hpolyS, ← hpolyT]
    have hmem : k ∈ Finset.range (n + 1) := by rw [Finset.mem_range]; omega
    have hres := unique_aux β γ (fun k' => S α β γ n k')
      (fun k' => ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
        S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k') n heq k hmem
    simpa using hres

end MetaMathlibExt
