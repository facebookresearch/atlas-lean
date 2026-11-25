/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma natDegree_sub_lt_of_coeff_eq {R : Type*} [Ring R] {p q : Polynomial R} {n : ℕ}
    (hn : n ≠ 0) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : p.coeff n = q.coeff n) :
    (p - q).natDegree < n := by
  have hle : (p - q).natDegree ≤ n :=
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hp hq)
  have hcoeff : (p - q).coeff n = 0 := by
    rw [Polynomial.coeff_sub, h, sub_self]
  by_contra hlt
  rw [not_lt] at hlt
  have heq : (p - q).natDegree = n := le_antisymm hle hlt
  have hne0 : p - q ≠ 0 := by
    rintro h0
    rw [h0, Polynomial.natDegree_zero] at heq
    exact hn heq.symm
  have hne : (p - q).coeff ((p - q).natDegree) ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne0
  rw [heq] at hne
  exact hne hcoeff

/-- **Mestre's square decomposition, including the quadratic case.** Let $K$ be a field of
characteristic different from $2$ and let $d \ge 0$ be an integer. Every monic polynomial
$P \in K[X]$ of degree $2d + 2$ can be written as $P = Q^2 - R$ with $Q, R \in K[X]$, $Q$ monic
of degree $d + 1$ and $R$ of degree at most $d$ (possibly $R = 0$), and the pair $(Q, R)$ is
unique.

Source: `mestre_monic_square_decomposition` is the source-shaped form, which assumes $d \ge 1$. -/
theorem mestre_monic_square_decomposition_general
    {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    {d : ℕ} {P : Polynomial K} (hPmonic : P.Monic) (hPdeg : P.natDegree = 2 * d + 2) :
    ∃! p : Polynomial K × Polynomial K,
      p.1.Monic ∧ p.1.natDegree = d + 1 ∧ P = p.1 ^ 2 - p.2 ∧ p.2.degree ≤ ↑d := by
  have hPis : P.IsMonicOfDegree (2 * d + 2) := by
    rw [Polynomial.isMonicOfDegree_iff]
    exact ⟨hPdeg.le, by rw [← hPdeg]; exact hPmonic.coeff_natDegree⟩
  suffices aux : ∀ (e : ℕ) (Q0 : Polynomial K), Q0.Monic → Q0.natDegree = d + 1 →
      (P - Q0 ^ 2).natDegree ≤ e →
      ∃ Q : Polynomial K, Q.Monic ∧ Q.natDegree = d + 1 ∧ (P - Q ^ 2).natDegree ≤ d by
    have hXis : ((Polynomial.X : Polynomial K) ^ (2 * d + 2)).IsMonicOfDegree
        (2 * d + 2) := by
      rw [Polynomial.isMonicOfDegree_iff]
      refine ⟨?_, ?_⟩
      · rw [Polynomial.natDegree_X_pow]
      · simp [Polynomial.coeff_X_pow]
    have hX2 : ((Polynomial.X : Polynomial K) ^ (d + 1)) ^ 2 =
        Polynomial.X ^ (2 * d + 2) := by
      rw [← pow_mul]
      congr 1
      ring
    have hlt : (P - ((Polynomial.X : Polynomial K) ^ (d + 1)) ^ 2).natDegree <
        2 * d + 2 := by
      rw [hX2]
      exact Polynomial.IsMonicOfDegree.natDegree_sub_lt (by omega) hPis hXis
    obtain ⟨Q, hQm, hQd, hQle⟩ := aux (2 * d + 1)
      ((Polynomial.X : Polynomial K) ^ (d + 1)) (Polynomial.monic_X_pow (d + 1))
      (Polynomial.natDegree_X_pow (d + 1)) (by omega)
    set R : Polynomial K := Q ^ 2 - P with hR_def
    have hPeq : P = Q ^ 2 - R := by
      rw [hR_def]
      abel
    have hRdeg : R.degree ≤ ↑d := by
      rw [hR_def, ← neg_sub, Polynomial.degree_neg]
      exact le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hQle)
    have hwit : Q.Monic ∧ Q.natDegree = d + 1 ∧ P = Q ^ 2 - R ∧ R.degree ≤ ↑d :=
      ⟨hQm, hQd, hPeq, hRdeg⟩
    refine ⟨(Q, R), hwit, ?_⟩
    rintro ⟨Q2, R2⟩ ⟨h2m, h2d, h2eq, h2deg⟩
    have hQQ : Q2 ^ 2 - Q ^ 2 = R2 - R := by
      have h1 : Q2 ^ 2 - R2 = Q ^ 2 - R := by rw [← h2eq, ← hPeq]
      calc Q2 ^ 2 - Q ^ 2 = (Q2 ^ 2 - R2) + (R2 - Q ^ 2) := by abel
        _ = (Q ^ 2 - R) + (R2 - Q ^ 2) := by rw [h1]
        _ = R2 - R := by abel
    have hQeq : Q2 = Q := by
      by_contra hne
      have hD0 : Q2 - Q ≠ 0 := sub_ne_zero.mpr hne
      have hc2 : Q2.coeff (d + 1) = 1 := by
        rw [← h2d]
        exact h2m.coeff_natDegree
      have hcQ : Q.coeff (d + 1) = 1 := by
        rw [← hQd]
        exact hQm.coeff_natDegree
      have hDlt : (Q2 - Q).natDegree < d + 1 :=
        natDegree_sub_lt_of_coeff_eq (by omega) h2d.le hQd.le (by rw [hc2, hcQ])
      have hS2coeff : (Q2 + Q).coeff (d + 1) = 2 := by
        rw [Polynomial.coeff_add, hc2, hcQ, one_add_one_eq_two]
      have hS2le : (Q2 + Q).natDegree ≤ d + 1 :=
        le_trans (Polynomial.natDegree_add_le _ _) (by rw [h2d, hQd, max_self])
      have hS2eq : (Q2 + Q).natDegree = d + 1 :=
        Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hS2le
          (by rw [hS2coeff]; exact hchar)
      have hS20 : Q2 + Q ≠ 0 := by
        rintro h0
        rw [h0, Polynomial.natDegree_zero] at hS2eq
        omega
      have hR2le : R2.natDegree ≤ d := Polynomial.natDegree_le_of_degree_le h2deg
      have hRle : R.natDegree ≤ d := Polynomial.natDegree_le_of_degree_le hRdeg
      have hRle2 : (R2 - R).natDegree ≤ d :=
        le_trans (Polynomial.natDegree_sub_le _ _) (max_le hR2le hRle)
      have hDS : (Q2 - Q) * (Q2 + Q) = R2 - R := by
        rw [mul_comm, ← sq_sub_sq]
        exact hQQ
      have hcon : d + 1 ≤ (R2 - R).natDegree := by
        rw [← hDS, Polynomial.natDegree_mul hD0 hS20, hS2eq]
        exact Nat.le_add_left _ _
      omega
    have hReq : R2 = R := by
      have h0 : R2 - R = 0 := by
        have h := hQQ
        rw [hQeq, sub_self] at h
        exact h.symm
      exact sub_eq_zero.mp h0
    exact Prod.ext hQeq hReq
  intro e
  induction e with
  | zero =>
    intro Q0 hQ0m hQ0d hle
    exact ⟨Q0, hQ0m, hQ0d, by omega⟩
  | succ e ih =>
    intro Q0 hQ0m hQ0d hle
    by_cases hle_d : (P - Q0 ^ 2).natDegree ≤ d
    · exact ⟨Q0, hQ0m, hQ0d, hle_d⟩
    · set S : Polynomial K := P - Q0 ^ 2 with hS_def
      have he'_gt : d < S.natDegree := not_le.mp hle_d
      have hS0 : S ≠ 0 := by
        rintro h0
        rw [h0, Polynomial.natDegree_zero] at he'_gt
        omega
      have hQ0sq_monic : (Q0 ^ 2).Monic := hQ0m.pow 2
      have hQ0sq_deg : (Q0 ^ 2).natDegree = 2 * d + 2 := by
        rw [Polynomial.natDegree_pow, hQ0d]
        ring
      have hQ0sq_is : (Q0 ^ 2).IsMonicOfDegree (2 * d + 2) := by
        rw [Polynomial.isMonicOfDegree_iff]
        exact ⟨hQ0sq_deg.le, by rw [← hQ0sq_deg]; exact hQ0sq_monic.coeff_natDegree⟩
      have hsub_lt : S.natDegree < 2 * d + 2 := by
        have h := Polynomial.IsMonicOfDegree.natDegree_sub_lt (n := 2 * d + 2)
          (by omega) hPis hQ0sq_is
        rw [hS_def]
        exact h
      have hdk : d + 1 ≤ S.natDegree := by omega
      set k := S.natDegree - (d + 1) with hk_def
      have hk_mem : k + (d + 1) = S.natDegree := by
        rw [hk_def]
        exact Nat.sub_add_cancel hdk
      have hk_le : k ≤ d := by omega
      have hk_lt : k < d + 1 := by omega
      set s : K := S.leadingCoeff with hs_def
      have hs_ne : s ≠ 0 := by
        rw [hs_def]
        exact Polynomial.leadingCoeff_ne_zero.mpr hS0
      set c : K := s / 2 with hc_def
      have hc_ne : c ≠ 0 := by
        rw [hc_def]
        exact div_ne_zero hs_ne hchar
      set m : Polynomial K := Polynomial.C c * Polynomial.X ^ k with hm_def
      have hm_ne : m ≠ 0 := by
        rw [hm_def]
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne)
          (pow_ne_zero k Polynomial.X_ne_zero)
      have hm_deg : m.natDegree = k := by
        rw [hm_def]
        exact Polynomial.natDegree_C_mul_X_pow k c hc_ne
      set Q1 : Polynomial K := Q0 + m with hQ1_def
      have hm_coeff : m.coeff (d + 1) = 0 := by
        rw [hm_def, Polynomial.coeff_C_mul_X_pow]
        split_ifs with h
        · exact absurd h (ne_of_gt hk_lt)
        · rfl
      have hQ0_coeff : Q0.coeff (d + 1) = 1 := by
        rw [← hQ0d]
        exact hQ0m.coeff_natDegree
      have hQ1_coeff : Q1.coeff (d + 1) = 1 := by
        rw [hQ1_def, Polynomial.coeff_add, hQ0_coeff, hm_coeff, add_zero]
      have hm_nat_le : m.natDegree ≤ d := le_trans hm_deg.le hk_le
      have hQ1_le : Q1.natDegree ≤ d + 1 := by
        calc Q1.natDegree = (Q0 + m).natDegree := by rw [hQ1_def]
          _ ≤ max Q0.natDegree m.natDegree := Polynomial.natDegree_add_le _ _
          _ ≤ d + 1 := by omega
      have hQ1m : Q1.Monic :=
        Polynomial.monic_of_natDegree_le_of_coeff_eq_one (d + 1) hQ1_le hQ1_coeff
      have hQ1d : Q1.natDegree = d + 1 :=
        Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hQ1_le
          (by rw [hQ1_coeff]; exact one_ne_zero)
      have h2c : (2 : K) * c = s := by
        rw [hc_def, mul_comm]
        exact div_mul_cancel₀ s hchar
      have hQ0_ne : Q0 ≠ 0 := hQ0m.ne_zero
      have hQ0m_deg : (Q0 * m).natDegree = d + 1 + k := by
        rw [Polynomial.natDegree_mul hQ0_ne hm_ne, hQ0d, hm_deg]
      have hC2 : (2 : Polynomial K) = Polynomial.C 2 := rfl
      have h2eq : (2 : Polynomial K) * Q0 * m = Polynomial.C 2 * (Q0 * m) := by
        rw [hC2, mul_assoc]
      have h2Q0m_deg : ((2 : Polynomial K) * Q0 * m).natDegree = S.natDegree := by
        rw [h2eq, Polynomial.natDegree_C_mul hchar, hQ0m_deg]
        omega
      have h2Q0m_coeff : ((2 : Polynomial K) * Q0 * m).coeff S.natDegree = s := by
        rw [← h2Q0m_deg, Polynomial.coeff_natDegree, h2eq,
          Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
          Polynomial.leadingCoeff_C, hQ0m.leadingCoeff, hm_def,
          Polynomial.leadingCoeff_C_mul_X_pow, one_mul]
        exact h2c
      have hS_coeff : S.coeff S.natDegree = s := by
        rw [hs_def]
        exact Polynomial.coeff_natDegree
      have hsub1 : (S - 2 * Q0 * m).natDegree < S.natDegree :=
        natDegree_sub_lt_of_coeff_eq (by omega) le_rfl h2Q0m_deg.le
          (by rw [hS_coeff, h2Q0m_coeff])
      have hm2 : (m ^ 2).natDegree < S.natDegree := by
        rw [Polynomial.natDegree_pow, hm_deg]
        omega
      have hQ1sq : Q1 ^ 2 = Q0 ^ 2 + (2 * Q0 * m + m ^ 2) := by
        rw [hQ1_def, add_sq, add_assoc]
      have hPS : P - Q1 ^ 2 = (S - 2 * Q0 * m) - m ^ 2 := by
        rw [hQ1sq, hS_def]
        abel
      have hnew : (P - Q1 ^ 2).natDegree < S.natDegree := by
        rw [hPS]
        exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hsub1 hm2)
      have hnew_le : (P - Q1 ^ 2).natDegree ≤ e := by omega
      obtain ⟨Q, hQm, hQd, hQle⟩ := ih Q1 hQ1m hQ1d hnew_le
      exact ⟨Q, hQm, hQd, hQle⟩

set_option linter.unusedVariables false in
/-- **Mestre's square decomposition.** Let $K$ be a field of characteristic different from $2$
and let $d \ge 1$ be an integer. Every monic polynomial $P \in K[X]$ of degree $2d + 2$ can be
written as $P = Q^2 - R$ with $Q, R \in K[X]$, $Q$ monic of degree $d + 1$ and $R$ of degree at
most $d$ (possibly $R = 0$), and the pair $(Q, R)$ is unique.

Source: Arvind Suresh, "Constructing curves of high rank via composite polynomials",
arXiv:2102.02113v2, <https://arxiv.org/abs/2102.02113>, TeX lines 1158-1179,
Lemma `lem:sqroot`; there coefficient comparison induces a `k`-algebra isomorphism.
Follows from `mestre_monic_square_decomposition_general`; the hypothesis `hd` is unused and
keeps the source's shape. Proves `Wanted` entry `mestre_monic_square_decomposition`.
-/
theorem mestre_monic_square_decomposition
    {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    {d : ℕ} (hd : 0 < d)
    {P : Polynomial K} (hPmonic : P.Monic) (hPdeg : P.natDegree = 2 * d + 2) :
    ∃! p : Polynomial K × Polynomial K,
      p.1.Monic ∧ p.1.natDegree = d + 1 ∧ P = p.1 ^ 2 - p.2 ∧ p.2.degree ≤ ↑d := by
  exact mestre_monic_square_decomposition_general hchar hPmonic hPdeg

end MetaMathlibExt
