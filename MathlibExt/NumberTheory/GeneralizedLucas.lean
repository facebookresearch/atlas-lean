/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence

/-!
# Shifted-index `k`-generalized Lucas numbers

Source: Herbert Batte and Florian Luca, *On the Largest Prime factor of the
`k`-generalized Lucas numbers*, arXiv `2311.13047v1`, Introduction, subsection
`Background`. For integers `k ≥ 2` the source defines the sequence on integer
indices `n ≥ 2 - k` with `L_0 = 2`, `L_1 = 1`, zeros on `2 - k, …, -1` for
`k ≥ 3`, and `L_n` the sum of the preceding `k` terms for every `n ≥ 2`
(`k = 2` is classical Lucas).

Formalized as `Nat.kGeneralizedLucas`, indexed exactly over the source domain:
the parameter carries `2 ≤ k` and each index carries `2 - k ≤ n`; no values
are assigned below `2 - k`. The engine is `LinearRecurrence.mkSol` of order
`k` with all coefficients `1`, where natural offset `j` corresponds to source
index `(2 - k) + j`.
-/

@[expose] public section

open Finset

namespace Nat

/-- **$k$-generalized Lucas numbers.** For a natural number $k \ge 2$, the $k$-generalized Lucas
numbers $L^{(k)}_n$ are the natural numbers indexed by the integers $n \ge 2 - k$ given by
$L^{(k)}_n = 0$ for $2 - k \le n \le -1$, $L^{(k)}_0 = 2$, $L^{(k)}_1 = 1$, and
$L^{(k)}_n = L^{(k)}_{n-1} + L^{(k)}_{n-2} + \dots + L^{(k)}_{n-k}$ for every integer $n \ge 2$. No
value is assigned at indices below $2 - k$. -/
public def kGeneralizedLucas (k : ℕ) (_hk : 2 ≤ k) (n : ℤ)
    (_h : 2 - (k : ℤ) ≤ n) : ℕ :=
  (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
    (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
    ((n - (2 - (k : ℤ))).toNat)

/-- **$k$-generalized Lucas numbers at index zero.** For every natural number $k \ge 2$, the
$k$-generalized Lucas number $L^{(k)}_0$ equals $2$. -/
public theorem kGeneralizedLucas_zero (k : ℕ) (hk : 2 ≤ k)
    (h0 : 2 - (k : ℤ) ≤ 0) :
    kGeneralizedLucas k hk 0 h0 = 2 := by
  unfold kGeneralizedLucas
  have hoff : ((0 : ℤ) - (2 - (k : ℤ))).toNat = k - 2 := by omega
  rw [hoff]
  have hmem : k - 2 < k := by omega
  have hcore :=
    LinearRecurrence.mkSol_eq_init (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ⟨k - 2, hmem⟩
  have hgoal :
      (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
          (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
          (k - 2) =
        (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
          ⟨k - 2, hmem⟩ := hcore
  rw [hgoal]
  have h2 : k - 2 + 2 = k := by omega
  change (if k - 2 + 2 = k then (2 : ℕ) else if k - 2 + 1 = k then (1 : ℕ) else (0 : ℕ)) = 2
  exact ite_eq_left h2

/-- **$k$-generalized Lucas numbers at index one.** For every natural number $k \ge 2$, the
$k$-generalized Lucas number $L^{(k)}_1$ equals $1$. -/
public theorem kGeneralizedLucas_one (k : ℕ) (hk : 2 ≤ k)
    (h1 : 2 - (k : ℤ) ≤ 1) :
    kGeneralizedLucas k hk 1 h1 = 1 := by
  unfold kGeneralizedLucas
  have hoff : ((1 : ℤ) - (2 - (k : ℤ))).toNat = k - 1 := by omega
  rw [hoff]
  have hmem : k - 1 < k := by omega
  have hcore :=
    LinearRecurrence.mkSol_eq_init (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ⟨k - 1, hmem⟩
  have hgoal :
      (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
          (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
          (k - 1) =
        (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
          ⟨k - 1, hmem⟩ := hcore
  rw [hgoal]
  have hne1 : k - 1 + 2 ≠ k := by omega
  have heq2 : k - 1 + 1 = k := by omega
  change (if k - 1 + 2 = k then (2 : ℕ) else if k - 1 + 1 = k then (1 : ℕ) else (0 : ℕ)) = 1
  rw [ite_eq_right hne1, ite_eq_left heq2]

/-- **$k$-generalized Lucas numbers vanish at negative indices.** For every natural number
$k \ge 3$ and every integer $n$ with $2 - k \le n \le -1$, the $k$-generalized Lucas number
$L^{(k)}_n$ equals $0$. -/
public theorem kGeneralizedLucas_neg_eq_zero (k : ℕ) (hk : 3 ≤ k) (n : ℤ)
    (h : 2 - (k : ℤ) ≤ n) (hn : n ≤ -1) :
    kGeneralizedLucas k (Nat.le_trans (by decide : 2 ≤ 3) hk) n h = 0 := by
  unfold kGeneralizedLucas
  have hnn : 0 ≤ n - (2 - (k : ℤ)) := by omega
  have hto : ((((n - (2 - (k : ℤ))).toNat : ℕ)) : ℤ) = n - (2 - (k : ℤ)) :=
    Int.toNat_of_nonneg hnn
  have hmem : (n - (2 - (k : ℤ))).toNat < k := by omega
  have hcore :=
    LinearRecurrence.mkSol_eq_init (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ⟨(n - (2 - (k : ℤ))).toNat, hmem⟩
  have hgoal :
      (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
          (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
          (n - (2 - (k : ℤ))).toNat =
        (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
          ⟨(n - (2 - (k : ℤ))).toNat, hmem⟩ := hcore
  rw [hgoal]
  have hne1 : (n - (2 - (k : ℤ))).toNat + 2 ≠ k := by omega
  have hne2 : (n - (2 - (k : ℤ))).toNat + 1 ≠ k := by omega
  change (if (n - (2 - (k : ℤ))).toNat + 2 = k then (2 : ℕ)
    else if (n - (2 - (k : ℤ))).toNat + 1 = k then (1 : ℕ) else (0 : ℕ)) = 0
  rw [ite_eq_right hne1, ite_eq_right hne2]

/-- **$k$-generalized Lucas numbers at the lowest index.** For every natural number $k \ge 3$,
the $k$-generalized Lucas number $L^{(k)}_{2-k}$ equals $0$. -/
public theorem kGeneralizedLucas_lower_zero (k : ℕ) (hk : 3 ≤ k)
    (h : 2 - (k : ℤ) ≤ 2 - (k : ℤ)) :
    kGeneralizedLucas k (Nat.le_trans (by decide : 2 ≤ 3) hk) (2 - (k : ℤ)) h =
      0 := by
  have hn : (2 - (k : ℤ)) ≤ -1 := by omega
  exact kGeneralizedLucas_neg_eq_zero k hk _ h hn

/-- **Recurrence for the $k$-generalized Lucas numbers.** For every natural number $k \ge 2$ and
every integer $n \ge 2$, the $k$-generalized Lucas numbers satisfy
$L^{(k)}_n = \sum_{i=0}^{k-1} L^{(k)}_{n-k+i}$, that is, $L^{(k)}_n$ is the sum
$L^{(k)}_{n-1} + \dots + L^{(k)}_{n-k}$ of the $k$ preceding values. -/
public theorem kGeneralizedLucas_recurrence (k : ℕ) (hk : 2 ≤ k) (n : ℤ)
    (hn : 2 ≤ n) (h : 2 - (k : ℤ) ≤ n) :
    kGeneralizedLucas k hk n h =
      ∑ i : Fin k,
        kGeneralizedLucas k hk ((n - (k : ℤ)) + (i.val : ℤ)) (by omega) := by
  have hnn : 0 ≤ n - (2 - (k : ℤ)) := by omega
  have hto : ((((n - (2 - (k : ℤ))).toNat : ℕ)) : ℤ) = n - (2 - (k : ℤ)) :=
    Int.toNat_of_nonneg hnn
  have hm_ge : k ≤ (n - (2 - (k : ℤ))).toNat := by omega
  have hsol_at :=
    LinearRecurrence.is_sol_mkSol (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ((n - (2 - (k : ℤ))).toNat - k)
  have hm_eq :
      (n - (2 - (k : ℤ))).toNat - k +
          (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).order =
        (n - (2 - (k : ℤ))).toNat :=
    Nat.sub_add_cancel hm_ge
  rw [hm_eq] at hsol_at
  have hlhs :
      kGeneralizedLucas k hk n h = (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
        (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
        (n - (2 - (k : ℤ))).toNat := rfl
  rw [hlhs, hsol_at]
  apply Finset.sum_congr rfl
  intro i _
  have hcoeff : (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).coeffs i = 1 := rfl
  rw [hcoeff, one_mul]
  have hterm_eq :
      kGeneralizedLucas k hk ((n - (k : ℤ)) + (i.val : ℤ)) (by omega) =
        (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
          (fun j : Fin k => if j.val + 2 = k then 2 else if j.val + 1 = k then 1 else 0)
          ((n - (2 - (k : ℤ))).toNat - k + i.val) := by
    have hilt := i.isLt
    unfold kGeneralizedLucas
    congr 1
    omega
  rw [hterm_eq]

end Nat
