/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.FormalOrthogonality
import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

open _root_.Polynomial

namespace MetaMathlibExt

variable {R : Type*} [Field R]

/-- `p 0 = 1` for a monic family indexed by degree. -/
private theorem favard_p_zero (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic) (hdeg : ∀ n, (p n).natDegree = n) :
    p 0 = 1 := by
  have hC : p 0 = C ((p 0).coeff 0) := eq_C_of_natDegree_eq_zero (hdeg 0)
  have h1 : (p 0).coeff 0 = 1 := by
    have h := (hmonic 0).coeff_natDegree
    rwa [hdeg 0] at h
  rw [hC, h1, C_1]

/-- Every polynomial is a combination of `p 0, .., p d` when the monic family
is indexed by degree. Induction on a degree bound. -/
private theorem favard_expand (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic) (hdeg : ∀ n, (p n).natDegree = n) :
    ∀ (d : ℕ) (q : Polynomial R), q.natDegree ≤ d →
      ∃ c : ℕ → R, q = ∑ i ∈ Finset.range (d + 1), c i • p i := by
  intro d
  induction d with
  | zero =>
    intro q hq
    have h0 : q.natDegree = 0 := Nat.le_zero.mp hq
    refine ⟨fun _ => q.coeff 0, ?_⟩
    change q = ∑ i ∈ Finset.range 1, (fun _ => q.coeff 0) i • p i
    rw [Finset.sum_range_one]
    change q = q.coeff 0 • p 0
    have hC0 : q.coeff 0 • (1 : Polynomial R) = C (q.coeff 0) := by
      rw [smul_eq_C_mul, mul_one]
    rw [favard_p_zero p hmonic hdeg]
    exact (eq_C_of_natDegree_eq_zero h0).trans hC0.symm
  | succ d ih =>
    intro q hq
    set a : R := q.coeff (d + 1) with ha
    set q' : Polynomial R := q - C a * p (d + 1) with hq'
    have h1 : (p (d + 1)).coeff (d + 1) = 1 := by
      have h := (hmonic (d + 1)).coeff_natDegree
      rwa [hdeg (d + 1)] at h
    have htop : q'.coeff (d + 1) = 0 := by
      rw [hq', coeff_sub, coeff_C_mul, h1, mul_one, sub_self]
    have hCp : (C a * p (d + 1)).natDegree ≤ d + 1 := by
      have h1 : (C a * p (d + 1)).natDegree ≤ (C a).natDegree + (p (d + 1)).natDegree :=
        natDegree_mul_le
      have h2 : (C a).natDegree = 0 := natDegree_C a
      have h3 : (p (d + 1)).natDegree = d + 1 := hdeg (d + 1)
      omega
    have hle : q'.natDegree ≤ d + 1 :=
      (natDegree_sub_le _ _).trans (max_le hq hCp)
    have hqd : q'.natDegree ≤ d := by
      rcases eq_or_ne q' 0 with h0 | hne
      · rw [h0, natDegree_zero]; exact Nat.zero_le d
      · by_contra hcon
        have hge : d + 1 ≤ q'.natDegree :=
          not_lt.mp (fun h => hcon (Nat.le_of_lt_succ h))
        have heq : q'.natDegree = d + 1 := Nat.le_antisymm hle hge
        have hlc : q'.coeff (d + 1) = q'.leadingCoeff := by
          change q'.coeff (d + 1) = q'.coeff q'.natDegree
          rw [heq]
        rw [hlc] at htop
        exact (leadingCoeff_ne_zero.mpr hne) htop
    obtain ⟨c, hc⟩ := ih q' hqd
    refine ⟨fun i => if i = d + 1 then a else c i, ?_⟩
    have hsum : (∑ i ∈ Finset.range (d + 1), (if i = d + 1 then a else c i) • p i)
        = ∑ i ∈ Finset.range (d + 1), c i • p i := by
      apply Finset.sum_congr rfl
      intro i hi
      show ((if i = d + 1 then a else c i) • p i) = c i • p i
      rw [ite_eq_right (ne_of_lt (Finset.mem_range.mp hi))]
    rw [Finset.sum_range_succ]
    simp only []
    rw [ite_true, hsum, ← hc, hq', smul_eq_C_mul]
    exact (sub_add_cancel q (C a * p (d + 1))).symm

/-- `L` kills `p m * r` when `r` has degree below `m`. -/
private theorem favard_linear_vanishing (p : ℕ → Polynomial R)
    (L : Polynomial R →ₗ[R] R)
    (hmonic : ∀ n, (p n).Monic) (hdeg : ∀ n, (p n).natDegree = n)
    (horth : ∀ n m, n ≠ m → L (p n * p m) = 0) :
    ∀ (m : ℕ) (r : Polynomial R), r.natDegree < m → L (p m * r) = 0 := by
  intro m r hr
  obtain ⟨c, hc⟩ := favard_expand p hmonic hdeg r.natDegree r le_rfl
  have hi : ∀ i ∈ Finset.range (r.natDegree + 1), i ≠ m := by
    intro i hii
    exact ne_of_lt (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hii)) hr)
  rw [hc, Finset.mul_sum, map_sum L _ _]
  refine Finset.sum_eq_zero ?_
  intro i hii
  calc L (p m * (c i • p i)) = c i • L (p m * p i) := by
          rw [smul_eq_C_mul, ← mul_assoc, mul_comm (p m), mul_assoc,
            ← smul_eq_C_mul, LinearMapClass.map_smul L _ _]
    _ = 0 := by rw [horth m i (Ne.symm (hi i hii)), smul_zero]

/-- `X * p k - p (k+1)` has degree at most `k`: both top coefficients are 1. -/
private theorem favard_top_sub (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic) (hdeg : ∀ n, (p n).natDegree = n) (k : ℕ) :
    (X * p k - p (k + 1)).natDegree ≤ k := by
  have hXk : (X * p k).natDegree = k + 1 := by
    rw [natDegree_X_mul (hmonic k).ne_zero, hdeg k]
  have htop : (X * p k - p (k + 1)).coeff (k + 1) = 0 := by
    rw [coeff_sub, coeff_X_mul]
    have h1 : (p k).coeff k = 1 := by
      have h := (hmonic k).coeff_natDegree
      rwa [hdeg k] at h
    have h2 : (p (k + 1)).coeff (k + 1) = 1 := by
      have h := (hmonic (k + 1)).coeff_natDegree
      rwa [hdeg (k + 1)] at h
    rw [h1, h2, sub_self]
  have hle : (X * p k - p (k + 1)).natDegree ≤ k + 1 :=
    (natDegree_sub_le _ _).trans (max_le hXk.le (hdeg (k + 1)).le)
  rcases eq_or_ne (X * p k - p (k + 1)) 0 with h0 | hne
  · rw [h0, natDegree_zero]; exact Nat.zero_le k
  · by_contra hcon
    have hge : k + 1 ≤ (X * p k - p (k + 1)).natDegree :=
      not_lt.mp (fun h => hcon (Nat.le_of_lt_succ h))
    have heq : (X * p k - p (k + 1)).natDegree = k + 1 :=
      Nat.le_antisymm hle hge
    have hlc : (X * p k - p (k + 1)).coeff (k + 1) =
        (X * p k - p (k + 1)).leadingCoeff := by
      change (X * p k - p (k + 1)).coeff (k + 1) =
        (X * p k - p (k + 1)).coeff (X * p k - p (k + 1)).natDegree
      rw [heq]
    rw [hlc] at htop
    exact (leadingCoeff_ne_zero.mpr hne) htop

/-- `p 1 = X + C a`: a monic degree-1 polynomial. -/
private theorem favard_p_one (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic) (hdeg : ∀ n, (p n).natDegree = n) :
    ∃ a : R, p 1 = X + C a := by
  have htop : (p 1 - X).coeff 1 = 0 := by
    rw [coeff_sub]
    have h1 : (p 1).coeff 1 = 1 := by
      have h := (hmonic 1).coeff_natDegree
      rwa [hdeg 1] at h
    have hX : (X : Polynomial R).coeff 1 = 1 := by
      rw [coeff_X, ite_eq_left rfl]
    rw [h1, hX, sub_self]
  have hle : (p 1 - X).natDegree ≤ 0 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rcases eq_or_ne N 1 with rfl | hne
    · exact htop
    · rw [coeff_sub]
      have h1 : (p 1).coeff N = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [hdeg 1]
        omega
      have hX : (X : Polynomial R).coeff N = 0 := by
        rw [coeff_X, ite_eq_right (Ne.symm hne)]
      rw [h1, hX, sub_zero]
  have h0 : (p 1 - X).natDegree = 0 := Nat.le_zero.mp hle
  refine ⟨(p 1 - X).coeff 0, ?_⟩
  have hC : p 1 - X = C ((p 1 - X).coeff 0) := eq_C_of_natDegree_eq_zero h0
  have h2 : p 1 = C ((p 1 - X).coeff 0) + X := by
    rw [← hC]
    exact (sub_add_cancel _ _).symm
  conv_lhs => rw [h2]
  exact add_comm _ _

/-- Per-level data: recurrence coefficients with `b ≠ 0`. -/
private theorem favard_step (p : ℕ → Polynomial R)
    (L : Polynomial R →ₗ[R] R)
    (hmonic : ∀ n, (p n).Monic) (hdeg : ∀ n, (p n).natDegree = n)
    (horth : ∀ n m, n ≠ m → L (p n * p m) = 0)
    (hsq0 : ∀ k, L (p k ^ 2) ≠ 0) (n : ℕ) :
    ∃ a b : R, b ≠ 0 ∧ p (n + 2) = (X - C a) * p (n + 1) - C b * p n := by
  set e : Polynomial R := X * p (n + 1) - p (n + 2) with he
  have hle : e.natDegree ≤ n + 1 := by
    rw [he]
    exact favard_top_sub p hmonic hdeg (n + 1)
  obtain ⟨c, hc⟩ := favard_expand p hmonic hdeg (n + 1) e hle
  have hc2 : e = ∑ i ∈ Finset.range (n + 2), c i • p i := hc
  have hterm : ∀ i k, L ((c i • p i) * p k) = c i • L (p i * p k) := by
    intro i k
    conv_lhs => rw [smul_eq_C_mul, mul_assoc, ← smul_eq_C_mul,
      LinearMapClass.map_smul L _ _]
  have hexpandL : ∀ k, L (e * p k)
      = ∑ i ∈ Finset.range (n + 2), c i • L (p i * p k) := by
    intro k
    rw [hc2, Finset.sum_mul, map_sum L _ _]
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i k
  have hdirect : ∀ k, k < n → L (e * p k) = 0 := by
    intro k hk
    have hXk : (X * p k).natDegree = k + 1 := by
      rw [natDegree_X_mul (hmonic k).ne_zero, hdeg k]
    have e1 : (X * p (n + 1)) * p k = p (n + 1) * (X * p k) := by ring
    have hA : L ((X * p (n + 1)) * p k) = 0 := by
      rw [e1]
      exact favard_linear_vanishing p L hmonic hdeg horth (n + 1) (X * p k) (by
        rw [hXk]; omega)
    have hB : L (p (n + 2) * p k) = 0 := horth (n + 2) k (by omega)
    have hdecomp : e * p k = (X * p (n + 1)) * p k - p (n + 2) * p k := by
      rw [he, sub_mul]
    rw [hdecomp, map_sub L _ _, hA, hB, sub_zero]
  have hsingle : ∀ k, k < n → (∑ i ∈ Finset.range (n + 2), c i • L (p i * p k))
      = c k • L (p k * p k) := by
    intro k hk
    have hmem : k ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hmem]
    have hz : (∑ i ∈ (Finset.range (n + 2)).erase k, c i • L (p i * p k)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hii
      have hik : i ≠ k := Finset.ne_of_mem_erase hii
      rw [horth i k hik, smul_zero]
    rw [hz, add_zero]
  have ckill : ∀ k, k < n → c k = 0 := by
    intro k hk
    have h00 : c k • L (p k * p k) = 0 := by
      rw [← hsingle k hk, ← hexpandL k, hdirect k hk]
    have hsq : L (p k * p k) ≠ 0 := by
      rw [← pow_two]
      exact hsq0 k
    rcases smul_eq_zero.mp h00 with hC0 | hy
    · exact hC0
    · exact absurd hy hsq
  have hred : e = c n • p n + c (n + 1) • p (n + 1) := by
    rw [hc2]
    have hz : (∑ i ∈ Finset.range n, c i • p i) = 0 :=
      Finset.sum_eq_zero (fun i hii => by
        rw [ckill i (Finset.mem_range.mp hii), zero_smul])
    simp only [Finset.sum_range_succ, hz, zero_add]
  have hLform : ∀ k, L (e * p k)
      = c n • L (p n * p k) + c (n + 1) • L (p (n + 1) * p k) := by
    intro k
    rw [hred, add_mul, map_add L _ _, hterm n k, hterm (n + 1) k]
  have hdirectN : L (e * p n) = L (p (n + 1) * p (n + 1)) := by
    have e1 : (X * p (n + 1)) * p n = p (n + 1) * (X * p n) := by ring
    have hsplit : X * p n = p (n + 1) + (X * p n - p (n + 1)) := by
      conv_lhs => rw [← sub_add_cancel (X * p n) (p (n + 1))]
      exact add_comm _ _
    have hvan : L (p (n + 1) * (X * p n - p (n + 1))) = 0 :=
      favard_linear_vanishing p L hmonic hdeg horth (n + 1) (X * p n - p (n + 1))
        (lt_of_le_of_lt (favard_top_sub p hmonic hdeg n) (Nat.lt_succ_self n))
    have hB : L (p (n + 2) * p n) = 0 := horth (n + 2) n (by omega)
    have hdecomp : e * p n = p (n + 1) * (X * p n) - p (n + 2) * p n := by
      rw [he, sub_mul, e1]
    rw [hdecomp, map_sub L _ _, hB, sub_zero, hsplit, mul_add, map_add L _ _,
      hvan, add_zero]
  have hcn : c n ≠ 0 := by
    intro hcz
    have h0 : L (e * p n) = 0 := by
      rw [hLform n, hcz, zero_smul, zero_add, horth (n + 1) n (by omega),
        smul_zero]
    rw [hdirectN] at h0
    rw [← pow_two] at h0
    exact (hsq0 (n + 1)) h0
  have hpn : p (n + 2)
      = (X - C (c (n + 1))) * p (n + 1) - C (c n) * p n := by
    have h1 : p (n + 2) = X * p (n + 1) - e := by
      rw [he]; ring
    rw [h1, hred, smul_eq_C_mul, smul_eq_C_mul]
    ring
  exact ⟨c (n + 1), c n, hcn, hpn⟩

/-- **Favard's theorem, forward direction.** Let $R$ be a field and let $(p_n)_{n \ge 0}$ be a
formally orthogonal family of monic polynomials over $R$. Then there are sequences
$(\alpha_n)_{n \ge 0}$ and $(\beta_n)_{n \ge 0}$ in $R$ with $\beta_n \ne 0$ for all $n \ge 1$
such that $p_0 = 1$, $p_1 = x - \alpha_0$, and
$p_{n+1} = (x - \alpha_n) \, p_n - \beta_n \, p_{n-1}$ for all $n \ge 1$.

Source: Barry, JIS VOL14 (`Barry1/barry97r2.tex`), lines 346-352.
URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry1/barry97r2.tex
Source SHA-256:
390bd7d75055d92085e8cd502df8b435fc1e45b1bbf8920038605d3fa1d1fe80
Span SHA-256 (lines 346-352):
636f9c2d5233070dc92150b854d33ace8d01e246fc385d8a80fee32dc8f218ab
Stable ID: jis_grounded_fa98ab71d0d207da0e58a1fe -/
public theorem favard_forward
    {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal p) :
    ∃ (α β : ℕ → R), (∀ n, β (n + 1) ≠ 0) ∧ p 0 = 1 ∧
      p 1 = Polynomial.X - Polynomial.C (α 0) ∧
      ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
        p (n + 1) - Polynomial.C (β (n + 1)) * p n := by
  have hdef : ∃ L : Polynomial R →ₗ[R] R, (∀ n, (p n).natDegree = n) ∧
      (∀ n m, n ≠ m → L (p n * p m) = 0) ∧ ∀ n, L (p n ^ 2) ≠ 0 := horth
  obtain ⟨L, hdeg, horth2, hsq0⟩ := hdef
  obtain ⟨a0, ha0⟩ := favard_p_one p hmonic hdeg
  choose A B hAB using fun n => favard_step p L hmonic hdeg horth2 hsq0 n
  set α : ℕ → R := fun m => match m with | 0 => -a0 | n + 1 => A n with hα
  set β : ℕ → R := fun m => match m with | 0 => 0 | n + 1 => B n with hβ
  have hα0 : α 0 = -a0 := rfl
  have hαS : ∀ n, α (n + 1) = A n := fun n => rfl
  have hβS : ∀ n, β (n + 1) = B n := fun n => rfl
  refine ⟨α, β, fun n => ?_, favard_p_zero p hmonic hdeg, ?_, fun n => ?_⟩
  · rw [hβS n]; exact (hAB n).1
  · rw [hα0, C_neg, sub_neg_eq_add]
    exact ha0
  · rw [hαS n, hβS n]
    exact (hAB n).2

end MetaMathlibExt
