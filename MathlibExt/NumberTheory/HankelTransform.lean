/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Hankel transforms

This module defines the zero-indexed Hankel transform of a sequence. Its `n`-th term is the
determinant of the `(n + 1) × (n + 1)` Hankel matrix, whose `(i, j)` entry is `a (i + j)`.

Sources:

* <https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry4/barry122.tex>
* <https://cs.uwaterloo.ca/journals/JIS/VOL10/French/french13.tex>

JIS concept: `jis_sem_44db93a38a920ba88ba59880`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Hankel transform.** Let $R$ be a commutative ring and let $(a_k)_{k \ge 0}$ be a sequence
in $R$. The Hankel transform of $a$ is the sequence $(h_n)_{n \ge 0}$ in $R$ whose term $h_n$ is
the determinant of the $(n + 1) \times (n + 1)$ Hankel matrix $(a_{i+j})_{0 \le i, j \le n}$. -/
def hankelTransform {R : Type*} [CommRing R] (a : ℕ → R) : ℕ → R :=
  fun n ↦ Matrix.det (Matrix.of fun i j : Fin (n + 1) ↦ a (i.val + j.val))

/-- A sequence over an integral domain with a nontrivial recurrence of order `r`
has vanishing Hankel transform at every index `N ≥ r`. -/
theorem hankelTransform.eq_zero_of_recurrence {R : Type*} [CommRing R] [IsDomain R]
    (P cs : ℕ → R) {N r : ℕ} (hr : r ≤ N) (hcs : ∃ k ≤ r, cs k ≠ 0)
    (hrec : ∀ n, r ≤ n → ∑ k ∈ Finset.range (r + 1), cs k * P (n - k) = 0) :
    hankelTransform P N = 0 := by
  obtain ⟨k, hk, hck⟩ := hcs
  unfold hankelTransform
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hrows
  -- The recurrence weights rows r, r - 1, ..., 0 in this order.
  let row (a : Fin (r + 1)) := a.rev.castLE (Nat.succ_le_succ hr)
  have hind := hrows.comp row ((Fin.castLE_injective _).comp Fin.rev_injective)
  apply hck
  apply Fintype.linearIndependent_iff.mp hind (fun a ↦ cs a) _ ⟨k, by omega⟩
  funext j
  have hj := hrec (r + j.val) (by omega)
  rw [← Fin.sum_univ_eq_sum_range] at hj
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Matrix.row_apply,
    Matrix.of_apply, row, Fin.val_castLE, Fin.val_rev, Nat.succ_sub_succ_eq_sub, smul_eq_mul,
    Pi.zero_apply]
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans hj
  rw [Nat.sub_add_comm (Nat.le_of_lt_succ a.isLt)]

/-- **Jacobi continued fraction expansion.** Let $K$ be a ring, not necessarily commutative, let
$(a_n)_{n \ge 0}$, $(\alpha_n)_{n \ge 0}$ and $(\beta_n)_{n \ge 0}$ be sequences in $K$, let
$\mu_0 \in K$, and let $(F_i)_{i \ge 0}$ be a sequence of formal power series over $K$ in the
variable $x$. These data form a Jacobi continued fraction expansion of $a$ when
$\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and, for every $i \ge 0$,
$(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$. Informally, the power series $F_i$ are the
tails of the continued fraction
$$
\sum_{n} a_n x^n = \cfrac{\mu_0}{1 - \alpha_0 x - \cfrac{\beta_1 x^2}{1 - \alpha_1 x - \cdots}}.
$$

This records only the continued fraction identities, not Heilermann's formula for the Hankel
determinants of $a$.

Source: Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel
Transforms," JIS 24 (2021), Article 21.10.2,
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117
(source SHA-256 `9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`;
lines 110-117 SHA-256 `11385eb5eee1af1081307348d4029cdc74b51d84e8bff2fbe9831891145d998e`).
JIS concept: `jis_dep_heilermann_049f63eb`. -/
def HasJacobiFraction {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) : Prop :=
  PowerSeries.mk a = PowerSeries.C mu0 * F 0 ∧
    ∀ i : ℕ,
      (1 - PowerSeries.C (alpha i) * PowerSeries.X -
        PowerSeries.C (beta (i + 1)) * PowerSeries.X ^ 2 * F (i + 1)) * F i = 1

end

end MetaMathlibExt
