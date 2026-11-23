/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.FavardForward
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open _root_.Polynomial

/-- The three-term recurrence plus monicity pins every degree:
`(p n).natDegree = n`. -/
private theorem favard_rev_deg (R : Type*) [Field R] (p : ℕ → Polynomial R)
    (α β : ℕ → R) (hmonic : ∀ n, (p n).Monic)
    (hp0 : p 0 = 1) (hp1 : p 1 = Polynomial.X - Polynomial.C (α 0))
    (hrec : ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
      p (n + 1) - Polynomial.C (β (n + 1)) * p n) :
    ∀ n, (p n).natDegree = n := by
  have step : ∀ n, (p n).natDegree = n → (p (n + 1)).natDegree = n + 1 →
      (p (n + 2)).natDegree = n + 2 := by
    intro n hn hn1
    rw [hrec n]
    have hX : ((Polynomial.X - Polynomial.C (α (n + 1))) * p (n + 1)).natDegree
        = n + 2 := by
      rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C _) (hmonic (n + 1)),
        Polynomial.natDegree_X_sub_C, hn1]
      omega
    have hle : (Polynomial.C (β (n + 1)) * p n).natDegree ≤ (p n).natDegree := by
      have hmul := Polynomial.natDegree_mul_le
        (p := Polynomial.C (β (n + 1))) (q := p n)
      rw [Polynomial.natDegree_C] at hmul
      omega
    have hlt : (Polynomial.C (β (n + 1)) * p n).natDegree <
        ((Polynomial.X - Polynomial.C (α (n + 1))) * p (n + 1)).natDegree := by
      omega
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hX]
  have h0 : (p 0).natDegree = 0 := by rw [hp0, Polynomial.natDegree_one]
  have h1 : (p 1).natDegree = 1 := by rw [hp1, Polynomial.natDegree_X_sub_C]
  suffices hall : ∀ n, (p n).natDegree = n ∧ (p (n + 1)).natDegree = n + 1 from
    fun n => (hall n).1
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih => exact ⟨ih.2, step n ih.1 ih.2⟩

/-- Orthogonality from the recurrence: with `L` killing every `p n` for
`n ≠ 0`, nested induction on the total degree (outer) and the first index
(inner) shows `L (p i * p j) = 0` for `i ≠ j` and `≠ 0` on the diagonal.
The recurrence is used in both directions: `p i` is lowered through
`X * p (i-1)` while `X * p j` is raised, keeping every needed pair at a
smaller total degree or the same total with a smaller first index. -/
private theorem favard_rev_key (R : Type*) [Field R] (p : ℕ → Polynomial R)
    (α β : ℕ → R) (L : Polynomial R →ₗ[R] R)
    (hp0 : p 0 = 1)
    (hLp : ∀ n, L (p n) = if n = 0 then 1 else 0)
    (hXp : ∀ k, Polynomial.X * p (k + 1) =
      p (k + 2) + Polynomial.C (α (k + 1)) * p (k + 1) +
        Polynomial.C (β (k + 1)) * p k)
    (hp1 : p 1 = Polynomial.X * p 0 - Polynomial.C (α 0) * p 0)
    (hpg : ∀ k, p (k + 2) = Polynomial.X * p (k + 1) -
      Polynomial.C (α (k + 1)) * p (k + 1) -
        Polynomial.C (β (k + 1)) * p k)
    (hβ : ∀ n, β (n + 1) ≠ 0) :
    ∀ i j, i ≤ j → (i ≠ j → L (p i * p j) = 0) ∧ (i = j → L (p i * p j) ≠ 0) := by
  have hCsmul : ∀ (a : R) (q : Polynomial R), L (Polynomial.C a * q) = a • L q := by
    intro a q
    rw [← Polynomial.smul_eq_C_mul, map_smul]
  have H : ∀ T : ℕ, ∀ i j : ℕ, i ≤ j → i + j ≤ T →
      (i ≠ j → L (p i * p j) = 0) ∧ (i = j → L (p i * p j) ≠ 0) := by
    intro T
    induction T using Nat.strong_induction_on with
    | h T outer =>
      intro i
      induction i with
      | zero =>
        intro j _ hT
        have hLj : L (p 0 * p j) = (if j = 0 then 1 else 0) := by
          rw [hp0, one_mul, hLp j]
        constructor
        · intro hne
          rw [hLj, ite_eq_right (Ne.symm hne)]
        · intro heq
          rw [hLj, ite_eq_left heq.symm]
          exact one_ne_zero
      | succ n ihn =>
        intro j hnj hT
        have hj1 : j ≠ 0 := by omega
        obtain ⟨u, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hj1
        have e2 := hXp u
        rcases eq_or_ne n 0 with rfl | hn0
        · have e01 : (0 : ℕ) + 1 = 1 := by omega
          rw [e01] at hnj hT ⊢
          have peq1 : p 1 * p (u + 1) = p 0 * p (u + 2) +
              Polynomial.C (α (u + 1)) * (p 0 * p (u + 1)) +
              Polynomial.C (β (u + 1)) * (p 0 * p u) -
              Polynomial.C (α 0) * (p 0 * p (u + 1)) := by
            linear_combination (p (u + 1)) * hp1 + (p 0) * e2
          have F1 := ihn (u + 2) (Nat.zero_le _) (by omega)
          have F2 := ihn (u + 1) (Nat.zero_le _) (by omega)
          have F3 := ihn u (Nat.zero_le _) (by omega)
          rw [peq1]
          simp only [map_add, map_sub, hCsmul]
          constructor
          · intro hne
            have z1 := F1.1 (by omega : (0 : ℕ) ≠ u + 2)
            have z2 := F2.1 (by omega : (0 : ℕ) ≠ u + 1)
            have z3 := F3.1 (by omega : (0 : ℕ) ≠ u)
            rw [z1, z2, z3]
            simp
          · intro heq
            have z1 := F1.1 (by omega : (0 : ℕ) ≠ u + 2)
            have z2 := F2.1 (by omega : (0 : ℕ) ≠ u + 1)
            have z3 := F3.2 (by omega : (0 : ℕ) = u)
            have hb' : β (u + 1) ≠ 0 := by
              have hu1 : u + 1 = 1 := by omega
              rw [hu1]
              exact hβ 0
            rw [z1, z2]
            simp only [smul_eq_mul, mul_zero, add_zero, zero_add, sub_zero]
            exact mul_ne_zero hb' z3
        · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
          have enrm : t + 1 + 1 = t + 2 := by omega
          rw [enrm] at hnj hT ⊢
          have peq : p (t + 2) * p (u + 1) = p (t + 1) * p (u + 2) +
              Polynomial.C (α (u + 1)) * (p (t + 1) * p (u + 1)) +
              Polynomial.C (β (u + 1)) * (p (t + 1) * p u) -
              Polynomial.C (α (t + 1)) * (p (t + 1) * p (u + 1)) -
              Polynomial.C (β (t + 1)) * (p t * p (u + 1)) := by
            linear_combination (p (u + 1)) * hpg t + (p (t + 1)) * e2
          have F1 := ihn (u + 2) (by omega) (by omega)
          have F2 := outer (t + 1 + (u + 1)) (by omega) (t + 1) (u + 1) (by omega)
            (by omega)
          have F3 := outer (t + 1 + u) (by omega) (t + 1) u (by omega) (by omega)
          have F4 := outer (t + (u + 1)) (by omega) t (u + 1) (by omega) (by omega)
          rw [peq]
          simp only [map_add, map_sub, hCsmul]
          constructor
          · intro hne
            have z1 := F1.1 (by omega : t + 1 ≠ u + 2)
            have z2 := F2.1 (by omega : t + 1 ≠ u + 1)
            have z3 := F3.1 (by omega : t + 1 ≠ u)
            have z4 := F4.1 (by omega : t ≠ u + 1)
            rw [z1, z2, z3, z4]
            simp
          · intro heq
            have z1 := F1.1 (by omega : t + 1 ≠ u + 2)
            have z2 := F2.1 (by omega : t + 1 ≠ u + 1)
            have htu : t + 1 = u := by omega
            have z3 := F3.2 htu
            have z4 := F4.1 (by omega : t ≠ u + 1)
            have hb' : β (u + 1) ≠ 0 := by
              have e3 : u + 1 = t + 1 + 1 := by omega
              rw [e3]
              exact hβ (t + 1)
            rw [z1, z2, z4]
            simp only [smul_eq_mul, mul_zero, add_zero, zero_add, sub_zero]
            exact mul_ne_zero hb' z3
  intro i j hij
  exact H (i + j) i j hij le_rfl

/-- **Favard's theorem.** Let $R$ be a field and let $(p_n)_{n \ge 0}$ be a family of monic
polynomials in $R[x]$. Then $(p_n)$ is formally orthogonal if and only if there are sequences
$(\alpha_n)_{n \ge 0}$ and $(\beta_n)_{n \ge 0}$ in $R$ with $\beta_n \ne 0$ for all $n \ge 1$
such that $p_0 = 1$, $p_1 = x - \alpha_0$, and
$p_{n+1} = (x - \alpha_n) \, p_n - \beta_n \, p_{n-1}$ for all $n \ge 1$.

Source: Paul Barry, "Riordan Arrays, Orthogonal Polynomials as Moments, and Hankel
Transforms," Journal of Integer Sequences 14 (2011), Article 11.2.2.
Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry1/barry97r2.tex
Actual Favard theorem: lines 346–352.
Source SHA-256: `390bd7d75055d92085e8cd502df8b435fc1e45b1bbf8920038605d3fa1d1fe80`.
Theorem-span SHA-256: `636f9c2d5233070dc92150b854d33ace8d01e246fc385d8a80fee32dc8f218ab`.
Stable concept ID: `jis_grounded_fa98ab71d0d207da0e58a1fe`.
-/
theorem favard_iff
    {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic) :
    Polynomial.IsFormallyOrthogonal p ↔
      ∃ (α β : ℕ → R), (∀ n, β (n + 1) ≠ 0) ∧ p 0 = 1 ∧
        p 1 = Polynomial.X - Polynomial.C (α 0) ∧
        ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
          p (n + 1) - Polynomial.C (β (n + 1)) * p n := by
  constructor
  · exact favard_forward p hmonic
  · rintro ⟨α, β, hβ, hp0, hp1, hrec⟩
    have hdeg := favard_rev_deg R p α β hmonic hp0 hp1 hrec
    let S : Polynomial.Sequence R :=
      ⟨p, fun n => by rw [degree_eq_natDegree (hmonic n).ne_zero, hdeg n]⟩
    have hCoeff : ∀ n, IsUnit (S n).leadingCoeff := fun n => by
      change IsUnit (p n).leadingCoeff
      rw [(hmonic n).leadingCoeff]
      exact isUnit_one
    set b : Module.Basis ℕ R (Polynomial R) := S.basis hCoeff
    have hbn : ∀ n, b n = p n := S.basis_eq_self hCoeff
    set L : Polynomial R →ₗ[R] R :=
      b.constr R (fun n => if n = 0 then (1 : R) else 0) with hLdef
    have hLp : ∀ n, L (p n) = (if n = 0 then 1 else 0) := by
      intro n
      rw [hLdef, ← hbn n]
      exact Module.Basis.constr_basis b R (fun n => if n = 0 then (1 : R) else 0) n
    have hXp : ∀ k, Polynomial.X * p (k + 1) =
        p (k + 2) + Polynomial.C (α (k + 1)) * p (k + 1) +
          Polynomial.C (β (k + 1)) * p k := by
      intro k
      have hk := hrec k
      linear_combination -hk
    have hp1e : p 1 = Polynomial.X * p 0 - Polynomial.C (α 0) * p 0 := by
      rw [hp1, hp0]
      ring
    have hpg : ∀ k, p (k + 2) = Polynomial.X * p (k + 1) -
        Polynomial.C (α (k + 1)) * p (k + 1) -
          Polynomial.C (β (k + 1)) * p k := by
      intro k
      have hk := hrec k
      linear_combination hk
    have key := favard_rev_key R p α β L hp0 hLp hXp hp1e hpg hβ
    refine ⟨L, hdeg, ?_, ?_⟩
    · intro n m hnm
      rcases lt_or_gt_of_ne hnm with h | h
      · exact (key n m (le_of_lt h)).1 (ne_of_lt h)
      · rw [mul_comm (p n) (p m)]
        exact (key m n (le_of_lt h)).1 (ne_of_lt h)
    · intro n
      have h2 := (key n n le_rfl).2 rfl
      rwa [← pow_two] at h2

end MetaMathlibExt
