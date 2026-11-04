/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Hadamard matrices of order `n + 1` with circulant core, for the Paley case
(`n` prime with `n % 4 = 3`) and the twin-prime case (`n = p * (p + 2)`
with `p` and `p + 2` prime). Proves `Wanted` entry
`exists_hadamard_matrix_with_circulant_core`.
-/

module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

namespace MetaMathlibExt

@[expose] public section

/-- **Hadamard matrix.** For a natural number $m$, an $m \times m$ matrix $H$ with integer
entries is a Hadamard matrix when every entry of $H$ is $1$ or $-1$ and
$H^{\mathsf T} H = m I$, where $I$ is the $m \times m$ identity matrix.

This predicate is used for Hadamard matrices of order $n + 1$ with circulant core, which exist
when $n$ is a prime congruent to $3$ mod $4$ (Paley) or $n = p(p + 2)$ with $p$ and $p + 2$
both prime (Stanton–Sprott/Whiteman).

Source: Richard P. Brent and Adam B. Yedidia, "Computation of Maximal
Determinants of Binary Circulant Matrices," Journal of Integer Sequences 21
(2018), Article 18.5.6, Theorem (label thm:circulant_core), lines 684–695,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Brent/brent11.tex
quoting Kotsireas et al.; attributions at lines 698–704. The prime-power
versions of cases (1)–(2), if the source allows them, and cases (3)–(4) of
the source theorem (Singer, Hall) are not formalized here. -/
public def isHadamardMatrix (m : ℕ) (H : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    (Matrix.transpose H) * H = (m : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ)

public def hasCirculantCore (n : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Prop :=
  ∃ v : Fin n → ℤ, ∀ i j : Fin n, H (Fin.succ i) (Fin.succ j) = v (i - j)

/-- Diagonal autocorrelation: entries squaring to one sum to `n`. -/
private lemma hcDiag {n : ℕ} (v : Fin n → ℤ)
    (hv : ∀ t, v t = 1 ∨ v t = -1) :
    ∑ t, v t * v t = (n : ℤ) := by
  classical
  have h1 : ∀ t : Fin n, v t * v t = 1 := by
    intro t
    rcases hv t with h | h <;> rw [h] <;> ring
  calc ∑ t, v t * v t = ∑ _t : Fin n, (1 : ℤ) := Finset.sum_congr rfl (fun x _ => h1 x)
    _ = (n : ℤ) := by simp [Finset.sum_const, Finset.card_univ]

/-- Column `0` against column `j + 1`: shift-invariance of the full sum. -/
private lemma hcShiftSum {n : ℕ} [NeZero n] (v : Fin n → ℤ) (j : Fin n) :
    ∑ i, v (i - j) = ∑ t, v t := by
  classical
  exact (Equiv.subRight j).sum_comp v

/-- Two core columns: reindexing reduces to a nonzero-shift autocorrelation. -/
private lemma hcTwoCol {n : ℕ} [NeZero n] (v : Fin n → ℤ) (j k : Fin n) :
    ∑ i, v (i - j) * v (i - k) = ∑ t, v t * v (t + (j - k)) := by
  classical
  have hstep : ∀ i : Fin n,
      v (i - j) * v (i - k) = (fun t => v t * v (t + (j - k))) ((Equiv.subRight j) i) := by
    intro i
    change v (i - j) * v (i - k) = v (i - j) * v ((i - j) + (j - k))
    congr 1
    congr 1
    abel
  calc ∑ i, v (i - j) * v (i - k)
      = ∑ i, (fun t => v t * v (t + (j - k))) ((Equiv.subRight j) i) :=
        Finset.sum_congr rfl (fun x _ => hstep x)
    _ = ∑ t, v t * v (t + (j - k)) :=
        (Equiv.subRight j).sum_comp (fun t => v t * v (t + (j - k)))

/-- Generic matrix assembly from a `±1` sequence with the right correlations. -/
private lemma hcMatrix {n : ℕ} [NeZero n] (v : Fin n → ℤ)
    (hv : ∀ t, v t = 1 ∨ v t = -1)
    (hsum : ∑ t, v t = -1)
    (haut : ∀ d : Fin n, d ≠ 0 → ∑ t, v t * v (t + d) = -1) :
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      isHadamardMatrix (n + 1) H ∧ hasCirculantCore n H := by
  classical
  set H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    (fun i j => Fin.cases 1 (fun i' => Fin.cases 1 (fun j' => v (i' - j')) j) i) with hH
  have hdiag : ∑ t : Fin n, v t * v t = (n : ℤ) := hcDiag v hv
  have h0 : ∀ j' : Fin n, ∑ i : Fin n, v (i - j') = -1 := by
    intro j'
    rw [hcShiftSum v j']
    exact hsum
  have hcol : ∀ j k : Fin n, j ≠ k → ∑ i : Fin n, v (i - j) * v (i - k) = -1 := by
    intro j k hjk
    rw [hcTwoCol v j k]
    exact haut (j - k) (sub_ne_zero.mpr hjk)
  have hdd : ∀ j' : Fin n, ∑ i : Fin n, v (i - j') * v (i - j') = (n : ℤ) := by
    intro j'
    have hstep : ∀ i : Fin n, v (i - j') * v (i - j') =
        (fun t => v t * v t) ((Equiv.subRight j') i) := by
      intro i
      rfl
    calc ∑ i, v (i - j') * v (i - j')
        = ∑ i, (fun t => v t * v t) ((Equiv.subRight j') i) :=
          Finset.sum_congr rfl (fun x _ => hstep x)
      _ = ∑ t, v t * v t := (Equiv.subRight j').sum_comp (fun t => v t * v t)
      _ = (n : ℤ) := hdiag
  have hself : ∑ _t : Fin n, (1 : ℤ) = (n : ℤ) := by
    simp [Finset.sum_const, Finset.card_univ]
  refine ⟨H, ⟨?_, ?_⟩, v, ?_⟩
  · intro i j
    refine Fin.cases ?_ ?_ i
    · refine Or.inl ?_
      simp only [hH, Fin.cases_zero]
    · intro i'
      refine Fin.cases ?_ ?_ j
      · refine Or.inl ?_
        simp only [hH, Fin.cases_succ, Fin.cases_zero]
      · intro j'
        simp only [hH, Fin.cases_succ]
        exact hv (i' - j')
  · ext i j
    refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
    · rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Matrix.transpose_apply]
      rw [hH]
      simp only [Fin.cases_zero, Fin.cases_succ, mul_one]
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hself]
      push_cast
      omega
    · intro j'
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Matrix.transpose_apply]
      rw [hH]
      simp only [Fin.cases_zero, Fin.cases_succ, one_mul]
      rw [h0 j']
      have hne : (0 : Fin (n + 1)) ≠ j'.succ := (Fin.succ_ne_zero _).symm
      rw [Matrix.smul_apply, Matrix.one_apply_ne hne, smul_eq_mul, mul_zero]
      norm_num
    · intro i'
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Matrix.transpose_apply]
      rw [hH]
      simp only [Fin.cases_zero, Fin.cases_succ, mul_one]
      rw [h0 i']
      have hne : i'.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
      rw [Matrix.smul_apply, Matrix.one_apply_ne hne, smul_eq_mul, mul_zero]
      norm_num
    · intro j' i'
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Matrix.transpose_apply]
      rw [hH]
      simp only [Fin.cases_zero, Fin.cases_succ, mul_one]
      by_cases hij : i' = j'
      · subst hij
        rw [hdd _, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        push_cast
        omega
      · have hentry : ∑ k' : Fin n, v (k' - i') * v (k' - j') = -1 :=
          hcol i' j' hij
        rw [hentry]
        have hne : i'.succ ≠ j'.succ := fun hcon => hij (Fin.succ_inj.mp hcon)
        rw [Matrix.smul_apply, Matrix.one_apply_ne hne, smul_eq_mul, mul_zero]
        norm_num
  · intro i j
    rw [hH]
    simp only [Fin.cases_succ]

/-- Transport of the sequence hypotheses along an additive equivalence. -/
private lemma hcTransport {n : ℕ} [NeZero n] {G : Type*} [AddCommGroup G] [Fintype G]
    (e : Fin n ≃+ G) (ψ : G → ℤ)
    (hval : ∀ x, ψ x = 1 ∨ ψ x = -1)
    (hsum : ∑ x, ψ x = -1)
    (haut : ∀ d : G, d ≠ 0 → ∑ x, ψ x * ψ (x + d) = -1) :
    (∀ t, (ψ ∘ e) t = 1 ∨ (ψ ∘ e) t = -1) ∧
      (∑ t, (ψ ∘ e) t = -1) ∧
      (∀ d : Fin n, d ≠ 0 → ∑ t, (ψ ∘ e) t * (ψ ∘ e) (t + d) = -1) := by
  classical
  refine ⟨fun t => hval (e t), ?_, ?_⟩
  · calc ∑ t, (ψ ∘ e) t = ∑ x, ψ x := e.toEquiv.sum_comp ψ
      _ = -1 := hsum
  · intro d hd
    have hed : e d ≠ 0 := fun hcon => hd ((AddEquiv.map_eq_zero_iff e).mp hcon)
    calc ∑ t, (ψ ∘ e) t * (ψ ∘ e) (t + d)
        = ∑ t, ψ (e t) * ψ (e t + e d) := by
          apply Finset.sum_congr rfl
          intro t _
          change ψ (e t) * ψ (e (t + d)) = ψ (e t) * ψ (e t + e d)
          rw [map_add]
      _ = ∑ x, ψ x * ψ (x + e d) :=
          e.toEquiv.sum_comp (fun x => ψ x * ψ (x + e d))
      _ = -1 := haut (e d) hed

/-- Sign of the quadratic character at `-1` for primes `1` or `3` mod `4`. -/
private lemma hcChiNegOne (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 3 ∨ p % 4 = 1) :
    quadraticChar (ZMod p) (-1) = if p % 4 = 3 then (-1 : ℤ) else 1 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rw [quadraticChar_neg_one hF, ZMod.card]
  rcases hmod with h | h
  · rw [ite_eq_left h]
    exact ZMod.χ₄_nat_three_mod_four h
  · rw [ite_eq_right (by omega)]
    exact ZMod.χ₄_nat_one_mod_four h

/-- Shifted quadratic character sum equals `-1` for nonzero shift. -/
private lemma hcShift {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ y : F, quadraticChar F y * quadraticChar F (y + d) = -1 := by
  classical
  have hχ1 : quadraticChar F ≠ 1 := quadraticChar_ne_one hF
  have hInv : (quadraticChar F)⁻¹ = quadraticChar F :=
    (quadraticChar_isQuadratic F).inv
  have hJ : jacobiSum (quadraticChar F) (quadraticChar F)
      = -(quadraticChar F (-1)) := by
    have h := jacobiSum_nontrivial_inv hχ1
    rwa [hInv] at h
  have hdsq : quadraticChar F d * quadraticChar F d = 1 := by
    have h := quadraticChar_sq_one hd
    rwa [pow_two] at h
  have hterm : ∀ x : F, quadraticChar F ((-d) * x) * quadraticChar F ((-d) * x + d)
      = quadraticChar F (-1) * (quadraticChar F x * quadraticChar F (1 - x)) := by
    intro x
    have e1 : (-d) * x = (-1) * (d * x) := by ring
    have e2 : (-d) * x + d = d * (1 - x) := by ring
    have m1 : quadraticChar F ((-1) * (d * x)) =
        quadraticChar F (-1) * (quadraticChar F d * quadraticChar F x) := by
      rw [map_mul (quadraticChar F) (-1) (d * x), map_mul (quadraticChar F) d x]
    have m2 : quadraticChar F (d * (1 - x)) =
        quadraticChar F d * quadraticChar F (1 - x) :=
      map_mul (quadraticChar F) d (1 - x)
    rw [e2, e1, m1, m2]
    linear_combination
      (quadraticChar F (-1) * quadraticChar F x * quadraticChar F (1 - x)) * hdsq
  have hnd : -d ≠ 0 := neg_ne_zero.mpr hd
  have hsum : ∑ y : F, quadraticChar F y * quadraticChar F (y + d)
      = quadraticChar F (-1) * jacobiSum (quadraticChar F) (quadraticChar F) := by
    calc ∑ y : F, quadraticChar F y * quadraticChar F (y + d)
        = ∑ x : F, quadraticChar F ((-d) * x) * quadraticChar F ((-d) * x + d) :=
          (Fintype.sum_bijective (fun x : F => (-d) * x) (mulLeft_bijective₀ (-d) hnd)
            (fun x : F => quadraticChar F ((-d) * x) * quadraticChar F ((-d) * x + d))
            (fun y : F => quadraticChar F y * quadraticChar F (y + d))
            (fun x => rfl)).symm
      _ = ∑ x : F, quadraticChar F (-1) *
            (quadraticChar F x * quadraticChar F (1 - x)) :=
          Finset.sum_congr rfl (fun x _ => hterm x)
      _ = quadraticChar F (-1) *
            ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) := by
          rw [Finset.mul_sum]
      _ = quadraticChar F (-1) * jacobiSum (quadraticChar F) (quadraticChar F) := by
          rfl
  have hnsq : quadraticChar F (-1) * quadraticChar F (-1) = 1 := by
    have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h := quadraticChar_sq_one hneg
    rwa [pow_two] at h
  rw [hsum, hJ, mul_neg, hnsq]

/-- Paley sequence values are `±1`. -/
private lemma hcPaleyVal (p : ℕ) [Fact p.Prime]
    (ψ : ZMod p → ℤ)
    (hψ : ∀ x, ψ x = quadraticChar (ZMod p) x - (if x = 0 then (1 : ℤ) else 0)) :
    ∀ x, ψ x = 1 ∨ ψ x = -1 := by
  classical
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [hψ 0, ite_eq_left rfl, quadraticChar_zero]
    refine Or.inr ?_
    norm_num
  · rw [hψ x, ite_eq_right hx, sub_zero]
    exact quadraticChar_dichotomy hx

/-- Paley sequence: sum and autocorrelations. -/
private lemma hcPaley (p : ℕ) [Fact p.Prime]
    (hmod : p % 4 = 3) (hF : ringChar (ZMod p) ≠ 2)
    (ψ : ZMod p → ℤ)
    (hψ : ∀ x, ψ x = quadraticChar (ZMod p) x - (if x = 0 then (1 : ℤ) else 0)) :
    (∑ x, ψ x = -1) ∧
      (∀ d : ZMod p, d ≠ 0 → ∑ x, ψ x * ψ (x + d) = -1) := by
  classical
  have hchi : quadraticChar (ZMod p) (-1) = -1 := by
    have h := hcChiNegOne p (Or.inl hmod)
    rwa [ite_eq_left hmod] at h
  have hind : ∑ _x : ZMod p, (if _x = 0 then (1 : ℤ) else 0) = 1 := by
    rw [Finset.sum_ite_eq']
    simp
  have hsum : ∑ x, ψ x = -1 := by
    calc ∑ x, ψ x
        = ∑ x : ZMod p, (quadraticChar (ZMod p) x -
            (if x = 0 then (1 : ℤ) else 0)) :=
          Finset.sum_congr rfl (fun x _ => hψ x)
      _ = (∑ x : ZMod p, quadraticChar (ZMod p) x) -
            (∑ x : ZMod p, (if x = 0 then (1 : ℤ) else 0)) :=
          Finset.sum_sub_distrib _ _
      _ = 0 - 1 := by rw [quadraticChar_sum_zero hF, hind]
      _ = -1 := by norm_num
  have haut : ∀ d : ZMod p, d ≠ 0 → ∑ x, ψ x * ψ (x + d) = -1 := by
    intro d hd
    have hexpand : ∀ y : ZMod p, ψ y * ψ (y + d)
        = (quadraticChar (ZMod p) y * quadraticChar (ZMod p) (y + d)) -
          (quadraticChar (ZMod p) y * (if y + d = 0 then (1 : ℤ) else 0)) -
          ((if y = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod p) (y + d)) +
          ((if y = 0 then (1 : ℤ) else 0) * (if y + d = 0 then (1 : ℤ) else 0)) := by
      intro y
      rw [hψ y, hψ (y + d)]
      ring
    have hS2 : ∑ y : ZMod p, quadraticChar (ZMod p) y *
          (if y + d = 0 then (1 : ℤ) else 0) = quadraticChar (ZMod p) (-d) := by
      have hstep : ∀ y : ZMod p, quadraticChar (ZMod p) y *
            (if y + d = 0 then (1 : ℤ) else 0)
            = (if y = -d then quadraticChar (ZMod p) y else 0) := by
        intro y
        by_cases hy : y = -d
        · rw [hy]
          simp
        · have hy2 : ¬ y + d = 0 := by
            intro hcon
            exact hy (add_eq_zero_iff_eq_neg.mp hcon)
          simp [hy, hy2]
      rw [Finset.sum_congr rfl (fun y _ => hstep y)]
      rw [Finset.sum_ite_eq']
      simp
    have hS3 : ∑ y : ZMod p, (if y = 0 then (1 : ℤ) else 0) *
          quadraticChar (ZMod p) (y + d) = quadraticChar (ZMod p) d := by
      have hstep : ∀ y : ZMod p, (if y = 0 then (1 : ℤ) else 0) *
            quadraticChar (ZMod p) (y + d)
            = (if y = 0 then quadraticChar (ZMod p) (y + d) else 0) := by
        intro y
        by_cases hy : y = 0
        · rw [hy]
          simp
        · simp [hy]
      rw [Finset.sum_congr rfl (fun y _ => hstep y)]
      rw [Finset.sum_ite_eq']
      simp
    have hS4 : ∑ y : ZMod p, (if y = 0 then (1 : ℤ) else 0) *
          (if y + d = 0 then (1 : ℤ) else 0) = 0 := by
      have hstep : ∀ y : ZMod p, (if y = 0 then (1 : ℤ) else 0) *
            (if y + d = 0 then (1 : ℤ) else 0)
            = (if y = 0 then (if y + d = 0 then (1 : ℤ) else 0) else 0) := by
        intro y
        by_cases hy : y = 0
        · rw [hy]
          simp
        · simp [hy]
      rw [Finset.sum_congr rfl (fun y _ => hstep y)]
      rw [Finset.sum_ite_eq']
      simp [hd]
    have hneg : quadraticChar (ZMod p) (-d) = -quadraticChar (ZMod p) d := by
      have e : (-d : ZMod p) = (-1) * d := by ring
      rw [e, map_mul (quadraticChar (ZMod p)) (-1) d, hchi, neg_one_mul]
    rw [Finset.sum_congr rfl (fun y _ => hexpand y)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [hcShift hF hd, hS2, hS3, hS4, hneg]
    ring
  exact ⟨hsum, haut⟩

/-- Pin: character times a shifted indicator. -/
private lemma hcPinChiAdd (r : ℕ) [Fact r.Prime] (t : ZMod r) :
    ∑ b : ZMod r, quadraticChar (ZMod r) b * (if b + t = 0 then (1 : ℤ) else 0)
      = quadraticChar (ZMod r) (-t) := by
  classical
  have hstep : ∀ b : ZMod r, quadraticChar (ZMod r) b *
      (if b + t = 0 then (1 : ℤ) else 0)
      = (if b = -t then quadraticChar (ZMod r) b else 0) := by
    intro b
    by_cases hy : b = -t
    · rw [hy]
      simp
    · have hy2 : ¬ b + t = 0 := by
        intro hcon
        exact hy (add_eq_zero_iff_eq_neg.mp hcon)
      simp [hy, hy2]
  rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_ite_eq']
  simp

/-- Pin: character times a point indicator. -/
private lemma hcPinChiPt (r : ℕ) [Fact r.Prime] (c : ZMod r) :
    ∑ b : ZMod r, quadraticChar (ZMod r) b * (if b = c then (1 : ℤ) else 0)
      = quadraticChar (ZMod r) c := by
  classical
  have hstep : ∀ b : ZMod r, quadraticChar (ZMod r) b * (if b = c then (1 : ℤ) else 0)
      = (if b = c then quadraticChar (ZMod r) b else 0) := by
    intro b
    by_cases hy : b = c
    · rw [hy]
      simp
    · simp [hy]
  rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_ite_eq']
  simp

/-- Pin: a shifted indicator sums to one. -/
private lemma hcPinOneAdd (r : ℕ) [Fact r.Prime] (t : ZMod r) :
    ∑ b : ZMod r, (if b + t = 0 then (1 : ℤ) else 0) = 1 := by
  classical
  have hstep : ∀ b : ZMod r, (if b + t = 0 then (1 : ℤ) else 0)
      = (if b = -t then (1 : ℤ) else 0) := by
    intro b
    by_cases hy : b = -t
    · rw [hy]
      simp
    · have hy2 : ¬ b + t = 0 := by
        intro hcon
        exact hy (add_eq_zero_iff_eq_neg.mp hcon)
      simp [hy, hy2]
  rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_ite_eq']
  simp

/-- A shifted character sum vanishes. -/
private lemma hcSumChiShift (r : ℕ) [Fact r.Prime]
    (hF : ringChar (ZMod r) ≠ 2) (t : ZMod r) :
    ∑ b : ZMod r, quadraticChar (ZMod r) (b + t) = 0 := by
  classical
  have hcoe : ⇑(Equiv.addRight t) = fun b : ZMod r => b + t := Equiv.coe_addRight t
  calc ∑ b : ZMod r, quadraticChar (ZMod r) (b + t)
      = ∑ b : ZMod r, quadraticChar (ZMod r) ((Equiv.addRight t) b) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hcoe]
    _ = ∑ b : ZMod r, quadraticChar (ZMod r) b :=
        Equiv.sum_comp (Equiv.addRight t) (quadraticChar (ZMod r))
    _ = 0 := quadraticChar_sum_zero hF

/-- A constant-one sum over `ZMod`. -/
private lemma hcSumOne (r : ℕ) [NeZero r] : ∑ _b : ZMod r, (1 : ℤ) = (r : ℤ) := by
  classical
  simp [Finset.sum_const, Finset.card_univ, ZMod.card]

/-- A point indicator over `ZMod` sums to one. -/
private lemma hcSumIndZero (r : ℕ) [Fact r.Prime] :
    ∑ a : ZMod r, (if a = 0 then (1 : ℤ) else 0) = 1 := by
  classical
  rw [Finset.sum_ite_eq']
  simp

/-- A double sum of split factors over a product. -/
private lemma hcProdSum (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (F : ZMod p → ℤ) (G : ZMod q → ℤ) :
    ∑ x : ZMod p × ZMod q, F x.1 * G x.2 = (∑ a, F a) * (∑ b, G b) := by
  classical
  calc ∑ x : ZMod p × ZMod q, F x.1 * G x.2
      = ∑ a : ZMod p, ∑ b : ZMod q, F a * G b := by
        simp only [Fintype.sum_prod_type]
    _ = _ := (Finset.sum_mul_sum _ _ _ _).symm

/-- Twin-prime sequence values are `±1`. -/
private lemma hcTwinVal (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (ψ : ZMod p × ZMod q → ℤ)
    (hψ : ∀ x, ψ x = quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2 +
      ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
        (if x.1 = 0 then (1 : ℤ) else 0))) :
    ∀ x, ψ x = 1 ∨ ψ x = -1 := by
  classical
  intro x
  by_cases ha : x.1 = 0 <;> by_cases hb : x.2 = 0
  · rw [hψ x, ha, hb]
    simp only [ite_true, quadraticChar_zero]
    refine Or.inl ?_
    norm_num
  · rw [hψ x, ha]
    simp only [hb, ite_true, ite_false, quadraticChar_zero]
    refine Or.inr ?_
    norm_num
  · rw [hψ x, hb]
    simp only [ha, ite_true, ite_false, quadraticChar_zero]
    refine Or.inl ?_
    norm_num
  · rw [hψ x]
    simp only [ha, hb, ite_false]
    rcases quadraticChar_dichotomy ha with h1 | h1 <;>
      rcases quadraticChar_dichotomy hb with h2 | h2 <;>
      simp [h1, h2]

/-- Twin-prime diagonal character product: `J(s) * J(t)` piece. -/
private lemma hcTwinAA (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (s : ZMod p) (t : ZMod q) :
    ∑ x : ZMod p × ZMod q, (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
      ((quadraticChar (ZMod p) (x.1 + s)) * quadraticChar (ZMod q) (x.2 + t)) =
      (∑ a : ZMod p, quadraticChar (ZMod p) a * quadraticChar (ZMod p) (a + s)) *
        (∑ b : ZMod q, quadraticChar (ZMod q) b * quadraticChar (ZMod q) (b + t)) := by
  classical
  calc ∑ x : ZMod p × ZMod q, (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
        ((quadraticChar (ZMod p) (x.1 + s)) * quadraticChar (ZMod q) (x.2 + t))
      = ∑ x : ZMod p × ZMod q, (quadraticChar (ZMod p) x.1 *
          quadraticChar (ZMod p) (x.1 + s)) *
          (quadraticChar (ZMod q) x.2 * quadraticChar (ZMod q) (x.2 + t)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = _ := hcProdSum p q
      (fun a : ZMod p => quadraticChar (ZMod p) a * quadraticChar (ZMod p) (a + s))
      (fun b : ZMod q => quadraticChar (ZMod q) b * quadraticChar (ZMod q) (b + t))

/-- Twin-prime cross terms vanish. -/
private lemma hcTwinCross (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hFp : ringChar (ZMod p) ≠ 2) (hFq : ringChar (ZMod q) ≠ 2)
    (ψA : ZMod p × ZMod q → ℤ)
    (ψE : ZMod p × ZMod q → ℤ)
    (hA : ∀ x, ψA x = quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2)
    (hE : ∀ x, ψE x = (if x.2 = 0 then (1 : ℤ) else 0) *
      (1 + (if x.1 = 0 then (1 : ℤ) else 0)) - (if x.1 = 0 then (1 : ℤ) else 0))
    (s : ZMod p) (t : ZMod q)
    (hprod : quadraticChar (ZMod p) (-1) * quadraticChar (ZMod q) (-1) = -1) :
    (∑ x, ψA x * ψE (x + (s, t))) + (∑ x, ψE x * ψA (x + (s, t))) = 0 := by
  classical
  have hC1 : ∑ x : ZMod p × ZMod q,
      (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
      ((if x.2 + t = 0 then (1 : ℤ) else 0) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0)))
      = quadraticChar (ZMod p) (-s) * quadraticChar (ZMod q) (-t) := by
    have hinner : ∀ a : ZMod p, ∑ b : ZMod q,
        (quadraticChar (ZMod p) a * quadraticChar (ZMod q) b) *
        ((if b + t = 0 then (1 : ℤ) else 0) * (1 + (if a + s = 0 then (1 : ℤ) else 0)))
        = (quadraticChar (ZMod p) a * (1 + (if a + s = 0 then (1 : ℤ) else 0))) *
          quadraticChar (ZMod q) (-t) := by
      intro a
      calc ∑ b : ZMod q, (quadraticChar (ZMod p) a * quadraticChar (ZMod q) b) *
            ((if b + t = 0 then (1 : ℤ) else 0) * (1 + (if a + s = 0 then (1 : ℤ) else 0)))
          = (quadraticChar (ZMod p) a * (1 + (if a + s = 0 then (1 : ℤ) else 0))) *
            (∑ b : ZMod q, quadraticChar (ZMod q) b *
              (if b + t = 0 then (1 : ℤ) else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ = _ := by rw [hcPinChiAdd q t]
    have houter : ∑ a : ZMod p, quadraticChar (ZMod p) a *
        (1 + (if a + s = 0 then (1 : ℤ) else 0))
        = quadraticChar (ZMod p) (-s) := by
      have hsplit : ∀ a : ZMod p, quadraticChar (ZMod p) a *
          (1 + (if a + s = 0 then (1 : ℤ) else 0))
          = quadraticChar (ZMod p) a +
            quadraticChar (ZMod p) a * (if a + s = 0 then (1 : ℤ) else 0) := by
        intro a
        ring
      rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
      rw [Finset.sum_add_distrib, quadraticChar_sum_zero hFp, zero_add]
      exact hcPinChiAdd p s
    calc ∑ x : ZMod p × ZMod q, (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
          ((if x.2 + t = 0 then (1 : ℤ) else 0) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0)))
        = ∑ a : ZMod p, ∑ b : ZMod q, (quadraticChar (ZMod p) a * quadraticChar (ZMod q) b) *
          ((if b + t = 0 then (1 : ℤ) else 0) * (1 + (if a + s = 0 then (1 : ℤ) else 0))) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ a : ZMod p, (quadraticChar (ZMod p) a * (1 + (if a + s = 0 then (1 : ℤ) else 0))) *
          quadraticChar (ZMod q) (-t) :=
          Finset.sum_congr rfl (fun a _ => hinner a)
      _ = (∑ a : ZMod p, quadraticChar (ZMod p) a * (1 + (if a + s = 0 then (1 : ℤ) else 0))) *
          quadraticChar (ZMod q) (-t) := by
          rw [Finset.sum_mul]
      _ = _ := by rw [houter]
  have hC2 : ∑ x : ZMod p × ZMod q,
      (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
      (if x.1 + s = 0 then (1 : ℤ) else 0) = 0 := by
    have hinner : ∀ a : ZMod p, ∑ b : ZMod q,
        (quadraticChar (ZMod p) a * quadraticChar (ZMod q) b) *
        (if a + s = 0 then (1 : ℤ) else 0)
        = (quadraticChar (ZMod p) a * (if a + s = 0 then (1 : ℤ) else 0)) *
          (∑ b : ZMod q, quadraticChar (ZMod q) b) := by
      intro a
      calc ∑ b : ZMod q, (quadraticChar (ZMod p) a * quadraticChar (ZMod q) b) *
            (if a + s = 0 then (1 : ℤ) else 0)
          = (quadraticChar (ZMod p) a * (if a + s = 0 then (1 : ℤ) else 0)) *
            (∑ b : ZMod q, quadraticChar (ZMod q) b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ = _ := by rw [quadraticChar_sum_zero hFq, mul_zero]
    calc ∑ x : ZMod p × ZMod q, (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
          (if x.1 + s = 0 then (1 : ℤ) else 0)
        = ∑ a : ZMod p, ∑ b : ZMod q, (quadraticChar (ZMod p) a * quadraticChar (ZMod q) b) *
          (if a + s = 0 then (1 : ℤ) else 0) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ a : ZMod p, (quadraticChar (ZMod p) a * (if a + s = 0 then (1 : ℤ) else 0)) *
          (∑ b : ZMod q, quadraticChar (ZMod q) b) :=
          Finset.sum_congr rfl (fun a _ => hinner a)
      _ = (∑ a : ZMod p, quadraticChar (ZMod p) a * (if a + s = 0 then (1 : ℤ) else 0)) *
          (∑ b : ZMod q, quadraticChar (ZMod q) b) := by
          rw [Finset.sum_mul]
      _ = 0 := by rw [quadraticChar_sum_zero hFq, mul_zero]
  have hC3 : ∑ x : ZMod p × ZMod q,
      ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) *
      (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod q) (x.2 + t))
      = quadraticChar (ZMod p) s * quadraticChar (ZMod q) t := by
    have hinner : ∀ a : ZMod p, ∑ b : ZMod q,
        ((if b = 0 then (1 : ℤ) else 0) * (1 + (if a = 0 then (1 : ℤ) else 0))) *
        (quadraticChar (ZMod p) (a + s) * quadraticChar (ZMod q) (b + t))
        = ((1 + (if a = 0 then (1 : ℤ) else 0)) * quadraticChar (ZMod p) (a + s)) *
          quadraticChar (ZMod q) t := by
      intro a
      have hpin : ∑ b : ZMod q, (if b = 0 then (1 : ℤ) else 0) *
          quadraticChar (ZMod q) (b + t) = quadraticChar (ZMod q) t := by
        have hstep : ∀ b : ZMod q, (if b = 0 then (1 : ℤ) else 0) *
            quadraticChar (ZMod q) (b + t)
            = (if b = 0 then quadraticChar (ZMod q) (b + t) else 0) := by
          intro b
          by_cases hy : b = 0
          · rw [hy]
            simp
          · simp [hy]
        rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_ite_eq']
        simp
      calc ∑ b : ZMod q, ((if b = 0 then (1 : ℤ) else 0) * (1 + (if a = 0 then (1 : ℤ) else 0))) *
            (quadraticChar (ZMod p) (a + s) * quadraticChar (ZMod q) (b + t))
          = ((1 + (if a = 0 then (1 : ℤ) else 0)) * quadraticChar (ZMod p) (a + s)) *
            (∑ b : ZMod q, (if b = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod q) (b + t)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ = _ := by rw [hpin]
    have houter : ∑ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
        quadraticChar (ZMod p) (a + s) = quadraticChar (ZMod p) s := by
      have hsplit : ∀ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
          quadraticChar (ZMod p) (a + s)
          = quadraticChar (ZMod p) (a + s) +
            (if a = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod p) (a + s) := by
        intro a
        ring
      have hpin : ∑ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) *
          quadraticChar (ZMod p) (a + s) = quadraticChar (ZMod p) s := by
        have hstep : ∀ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) *
            quadraticChar (ZMod p) (a + s)
            = (if a = 0 then quadraticChar (ZMod p) (a + s) else 0) := by
          intro a
          by_cases hy : a = 0
          · rw [hy]
            simp
          · simp [hy]
        rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_ite_eq']
        simp
      rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
      rw [Finset.sum_add_distrib, hcSumChiShift p hFp s, zero_add]
      exact hpin
    calc ∑ x : ZMod p × ZMod q, ((if x.2 = 0 then (1 : ℤ) else 0) *
          (1 + (if x.1 = 0 then (1 : ℤ) else 0))) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod q) (x.2 + t))
        = ∑ a : ZMod p, ∑ b : ZMod q, ((if b = 0 then (1 : ℤ) else 0) *
          (1 + (if a = 0 then (1 : ℤ) else 0))) *
          (quadraticChar (ZMod p) (a + s) * quadraticChar (ZMod q) (b + t)) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ a : ZMod p, ((1 + (if a = 0 then (1 : ℤ) else 0)) *
          quadraticChar (ZMod p) (a + s)) * quadraticChar (ZMod q) t :=
          Finset.sum_congr rfl (fun a _ => hinner a)
      _ = (∑ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
          quadraticChar (ZMod p) (a + s)) * quadraticChar (ZMod q) t := by
          rw [Finset.sum_mul]
      _ = _ := by rw [houter]
  have hC4 : ∑ x : ZMod p × ZMod q,
      (if x.1 = 0 then (1 : ℤ) else 0) *
      (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod q) (x.2 + t)) = 0 := by
    have hinner : ∀ a : ZMod p, ∑ b : ZMod q,
        (if a = 0 then (1 : ℤ) else 0) *
        (quadraticChar (ZMod p) (a + s) * quadraticChar (ZMod q) (b + t))
        = ((if a = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod p) (a + s)) *
          (∑ b : ZMod q, quadraticChar (ZMod q) (b + t)) := by
      intro a
      calc ∑ b : ZMod q, (if a = 0 then (1 : ℤ) else 0) *
            (quadraticChar (ZMod p) (a + s) * quadraticChar (ZMod q) (b + t))
          = ((if a = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod p) (a + s)) *
            (∑ b : ZMod q, quadraticChar (ZMod q) (b + t)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ = _ := by rw [hcSumChiShift q hFq t, mul_zero]
    calc ∑ x : ZMod p × ZMod q, (if x.1 = 0 then (1 : ℤ) else 0) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod q) (x.2 + t))
        = ∑ a : ZMod p, ∑ b : ZMod q, (if a = 0 then (1 : ℤ) else 0) *
          (quadraticChar (ZMod p) (a + s) * quadraticChar (ZMod q) (b + t)) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ a : ZMod p, ((if a = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod p) (a + s)) *
          (∑ b : ZMod q, quadraticChar (ZMod q) (b + t)) :=
          Finset.sum_congr rfl (fun a _ => hinner a)
      _ = (∑ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) * quadraticChar (ZMod p) (a + s)) *
          (∑ b : ZMod q, quadraticChar (ZMod q) (b + t)) := by
          rw [Finset.sum_mul]
      _ = 0 := by rw [hcSumChiShift q hFq t, mul_zero]
  have e1 : ∀ x : ZMod p × ZMod q, (x + (s, t)).1 = x.1 + s := fun x => rfl
  have e2 : ∀ x : ZMod p × ZMod q, (x + (s, t)).2 = x.2 + t := fun x => rfl
  have hexpand1 : ∀ x : ZMod p × ZMod q, ψA x * ψE (x + (s, t))
      = ((quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
        ((if x.2 + t = 0 then (1 : ℤ) else 0) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0)))) -
        ((quadraticChar (ZMod p) x.1 * quadraticChar (ZMod q) x.2) *
        (if x.1 + s = 0 then (1 : ℤ) else 0)) := by
    intro x
    rw [hA x, hE (x + (s, t)), e1 x, e2 x]
    ring
  have hexpand2 : ∀ x : ZMod p × ZMod q, ψE x * ψA (x + (s, t))
      = (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) *
        (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod q) (x.2 + t))) -
        ((if x.1 = 0 then (1 : ℤ) else 0) *
        (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod q) (x.2 + t))) := by
    intro x
    rw [hE x, hA (x + (s, t)), e1 x, e2 x]
    ring
  have hm1 : quadraticChar (ZMod p) (-s)
      = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) s := by
    have e : (-s : ZMod p) = (-1) * s := by ring
    rw [e, map_mul (quadraticChar (ZMod p)) (-1) s]
  have hm2 : quadraticChar (ZMod q) (-t)
      = quadraticChar (ZMod q) (-1) * quadraticChar (ZMod q) t := by
    have e : (-t : ZMod q) = (-1) * t := by ring
    rw [e, map_mul (quadraticChar (ZMod q)) (-1) t]
  have hfin : (quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) s) *
      (quadraticChar (ZMod q) (-1) * quadraticChar (ZMod q) t) +
      (quadraticChar (ZMod p) s * quadraticChar (ZMod q) t) = 0 := by
    have hfactor : (quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) s) *
        (quadraticChar (ZMod q) (-1) * quadraticChar (ZMod q) t)
        = (quadraticChar (ZMod p) (-1) * quadraticChar (ZMod q) (-1)) *
          (quadraticChar (ZMod p) s * quadraticChar (ZMod q) t) := by
      ring
    rw [hfactor, hprod]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hexpand1 x)]
  rw [Finset.sum_congr rfl (fun x _ => hexpand2 x)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hC1, hC2, hC3, hC4, hm1, hm2]
  linear_combination hfin

/-- Twin-prime error-term autocorrelation. -/
private lemma hcTwinEE (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (ψE : ZMod p × ZMod q → ℤ)
    (hE : ∀ x, ψE x = (if x.2 = 0 then (1 : ℤ) else 0) *
      (1 + (if x.1 = 0 then (1 : ℤ) else 0)) - (if x.1 = 0 then (1 : ℤ) else 0))
    (s : ZMod p) (t : ZMod q) :
    ∑ x, ψE x * ψE (x + (s, t)) =
      ((if t = 0 then (1 : ℤ) else 0) * ((p : ℤ) + 2 + (if s = 0 then 1 else 0)) -
        2 * (1 + (if s = 0 then (1 : ℤ) else 0)) +
        (if s = 0 then (1 : ℤ) else 0) * (q : ℤ)) := by
  classical
  have hF4pin : ∑ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) *
      (if a + s = 0 then (1 : ℤ) else 0) = (if s = 0 then (1 : ℤ) else 0) := by
    have hstep : ∀ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) *
        (if a + s = 0 then (1 : ℤ) else 0)
        = (if a = 0 then (if a + s = 0 then (1 : ℤ) else 0) else 0) := by
      intro a
      by_cases hy : a = 0
      · rw [hy]
        simp
      · simp [hy]
    rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_ite_eq']
    simp
  have hFsum : ∑ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
      (1 + (if a + s = 0 then (1 : ℤ) else 0))
      = (p : ℤ) + 2 + (if s = 0 then (1 : ℤ) else 0) := by
    have hsplit : ∀ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
        (1 + (if a + s = 0 then (1 : ℤ) else 0))
        = 1 + (if a = 0 then (1 : ℤ) else 0) + (if a + s = 0 then (1 : ℤ) else 0) +
          ((if a = 0 then (1 : ℤ) else 0) * (if a + s = 0 then (1 : ℤ) else 0)) := by
      intro a
      ring
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hcSumOne p, hcSumIndZero p, hcPinOneAdd p s, hF4pin]
    ring
  have hGsum : ∑ b : ZMod q, (if b = 0 then (1 : ℤ) else 0) *
      (if b + t = 0 then (1 : ℤ) else 0) = (if t = 0 then (1 : ℤ) else 0) := by
    have hstep : ∀ b : ZMod q, (if b = 0 then (1 : ℤ) else 0) *
        (if b + t = 0 then (1 : ℤ) else 0)
        = (if b = 0 then (if b + t = 0 then (1 : ℤ) else 0) else 0) := by
      intro b
      by_cases hy : b = 0
      · rw [hy]
        simp
      · simp [hy]
    rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_ite_eq']
    simp
  have hF2 : ∑ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
      (if a + s = 0 then (1 : ℤ) else 0)
      = 1 + (if s = 0 then (1 : ℤ) else 0) := by
    have hsplit : ∀ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0)) *
        (if a + s = 0 then (1 : ℤ) else 0)
        = (if a + s = 0 then (1 : ℤ) else 0) +
          ((if a = 0 then (1 : ℤ) else 0) * (if a + s = 0 then (1 : ℤ) else 0)) := by
      intro a
      ring
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [Finset.sum_add_distrib, hcPinOneAdd p s, hF4pin]
  have hF3 : ∑ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) *
      (1 + (if a + s = 0 then (1 : ℤ) else 0))
      = 1 + (if s = 0 then (1 : ℤ) else 0) := by
    have hstep : ∀ a : ZMod p, (if a = 0 then (1 : ℤ) else 0) *
        (1 + (if a + s = 0 then (1 : ℤ) else 0))
        = (if a = 0 then (1 + (if a + s = 0 then (1 : ℤ) else 0)) else 0) := by
      intro a
      by_cases hy : a = 0
      · rw [hy]
        simp
      · simp [hy]
    rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_ite_eq']
    simp
  have hV1 : ∑ x : ZMod p × ZMod q,
      ((if x.2 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) *
      ((1 + (if x.1 = 0 then (1 : ℤ) else 0)) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0)))
      = (if t = 0 then (1 : ℤ) else 0) * ((p : ℤ) + 2 + (if s = 0 then 1 else 0)) := by
    calc ∑ x : ZMod p × ZMod q,
          ((if x.2 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) *
          ((1 + (if x.1 = 0 then (1 : ℤ) else 0)) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0)))
        = ∑ x : ZMod p × ZMod q,
            ((1 + (if x.1 = 0 then (1 : ℤ) else 0)) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) *
            ((if x.2 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = _ := by
          rw [hcProdSum p q
            (fun a : ZMod p => (1 + (if a = 0 then (1 : ℤ) else 0)) *
              (1 + (if a + s = 0 then (1 : ℤ) else 0)))
            (fun b : ZMod q => (if b = 0 then (1 : ℤ) else 0) *
              (if b + t = 0 then (1 : ℤ) else 0))]
          rw [hFsum, hGsum, mul_comm]
  have hV2 : ∑ x : ZMod p × ZMod q,
      ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) *
      (if x.1 + s = 0 then (1 : ℤ) else 0)
      = 1 + (if s = 0 then (1 : ℤ) else 0) := by
    calc ∑ x : ZMod p × ZMod q,
          ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) *
          (if x.1 + s = 0 then (1 : ℤ) else 0)
        = ∑ x : ZMod p × ZMod q,
            ((1 + (if x.1 = 0 then (1 : ℤ) else 0)) * (if x.1 + s = 0 then (1 : ℤ) else 0)) *
            (if x.2 = 0 then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = _ := by
          rw [hcProdSum p q
            (fun a : ZMod p => (1 + (if a = 0 then (1 : ℤ) else 0)) *
              (if a + s = 0 then (1 : ℤ) else 0))
            (fun b : ZMod q => (if b = 0 then (1 : ℤ) else 0))]
          rw [hF2, hcSumIndZero q, mul_one]
  have hV3 : ∑ x : ZMod p × ZMod q,
      ((if x.1 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) *
      (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))
      = 1 + (if s = 0 then (1 : ℤ) else 0) := by
    calc ∑ x : ZMod p × ZMod q,
          ((if x.1 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) *
          (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))
        = ∑ x : ZMod p × ZMod q,
            ((if x.1 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) *
            (if x.2 + t = 0 then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = _ := by
          rw [hcProdSum p q
            (fun a : ZMod p => (if a = 0 then (1 : ℤ) else 0) *
              (1 + (if a + s = 0 then (1 : ℤ) else 0)))
            (fun b : ZMod q => (if b + t = 0 then (1 : ℤ) else 0))]
          rw [hF3, hcPinOneAdd q t, mul_one]
  have hV4 : ∑ x : ZMod p × ZMod q,
      (if x.1 = 0 then (1 : ℤ) else 0) * (if x.1 + s = 0 then (1 : ℤ) else 0)
      = (if s = 0 then (1 : ℤ) else 0) * (q : ℤ) := by
    calc ∑ x : ZMod p × ZMod q,
          (if x.1 = 0 then (1 : ℤ) else 0) * (if x.1 + s = 0 then (1 : ℤ) else 0)
        = ∑ x : ZMod p × ZMod q,
            ((if x.1 = 0 then (1 : ℤ) else 0) * (if x.1 + s = 0 then (1 : ℤ) else 0)) * 1 := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = _ := by
          rw [hcProdSum p q
            (fun a : ZMod p => (if a = 0 then (1 : ℤ) else 0) *
              (if a + s = 0 then (1 : ℤ) else 0))
            (fun _ : ZMod q => (1 : ℤ))]
          rw [hF4pin, hcSumOne q]
  have e1 : ∀ x : ZMod p × ZMod q, (x + (s, t)).1 = x.1 + s := fun x => rfl
  have e2 : ∀ x : ZMod p × ZMod q, (x + (s, t)).2 = x.2 + t := fun x => rfl
  have hexpand : ∀ x : ZMod p × ZMod q, ψE x * ψE (x + (s, t))
      = (((if x.2 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) *
        ((1 + (if x.1 = 0 then (1 : ℤ) else 0)) * (1 + (if x.1 + s = 0 then (1 : ℤ) else 0)))) -
        (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) *
        (if x.1 + s = 0 then (1 : ℤ) else 0)) -
        (((if x.1 = 0 then (1 : ℤ) else 0) * (if x.2 + t = 0 then (1 : ℤ) else 0)) *
        (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) +
        ((if x.1 = 0 then (1 : ℤ) else 0) * (if x.1 + s = 0 then (1 : ℤ) else 0)) := by
    intro x
    rw [hE x, hE (x + (s, t)), e1 x, e2 x]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hexpand x)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hV1, hV2, hV3, hV4]
  ring

/-- Character diagonal sum at shift zero: `card - 1`. -/
private lemma hcDiagZero (r : ℕ) [Fact r.Prime] :
    ∑ a : ZMod r, quadraticChar (ZMod r) a * quadraticChar (ZMod r) a
      = (r : ℤ) - 1 := by
  classical
  have hterm : ∀ a : ZMod r, quadraticChar (ZMod r) a * quadraticChar (ZMod r) a
      = 1 - (if a = 0 then (1 : ℤ) else 0) := by
    intro a
    by_cases ha : a = 0
    · rw [ha, quadraticChar_zero]
      simp
    · have h := quadraticChar_sq_one ha
      rw [pow_two] at h
      rw [ite_eq_right ha, h, sub_zero]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_sub_distrib, hcSumOne r, hcSumIndZero r]

/-- Twin-prime sequence: sum and autocorrelations. -/
private lemma hcTwin (p : ℕ) [Fact p.Prime] [Fact (p + 2).Prime]
    (hFp : ringChar (ZMod p) ≠ 2) (hFq : ringChar (ZMod (p + 2)) ≠ 2)
    (hprod : quadraticChar (ZMod p) (-1) * quadraticChar (ZMod (p + 2)) (-1) = -1)
    (ψ : ZMod p × ZMod (p + 2) → ℤ)
    (hψ : ∀ x, ψ x = quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2 +
      ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
        (if x.1 = 0 then (1 : ℤ) else 0))) :
    (∑ x, ψ x = -1) ∧
      (∀ d : ZMod p × ZMod (p + 2), d ≠ 0 → ∑ x, ψ x * ψ (x + d) = -1) := by
  classical
  have hA0 : (∑ x : ZMod p × ZMod (p + 2),
      quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) = 0 := by
    calc _ = (∑ a : ZMod p, quadraticChar (ZMod p) a) *
          (∑ b : ZMod (p + 2), quadraticChar (ZMod (p + 2)) b) :=
        hcProdSum p (p + 2) (fun a => quadraticChar (ZMod p) a)
          (fun b => quadraticChar (ZMod (p + 2)) b)
      _ = 0 := by rw [quadraticChar_sum_zero hFp, zero_mul]
  have hE1 : (∑ x : ZMod p × ZMod (p + 2),
      (if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0)))
      = ((p : ℤ) + 1) * 1 := by
    calc _ = ∑ x : ZMod p × ZMod (p + 2),
            (1 + (if x.1 = 0 then (1 : ℤ) else 0)) * (if x.2 = 0 then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (∑ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0))) *
          (∑ b : ZMod (p + 2), (if b = 0 then (1 : ℤ) else 0)) :=
          hcProdSum p (p + 2) (fun a : ZMod p => (1 + (if a = 0 then (1 : ℤ) else 0)))
            (fun b : ZMod (p + 2) => (if b = 0 then (1 : ℤ) else 0))
      _ = _ := by
          have h1 : (∑ a : ZMod p, (1 + (if a = 0 then (1 : ℤ) else 0))) = (p : ℤ) + 1 := by
            rw [Finset.sum_add_distrib, hcSumOne p, hcSumIndZero p]
          rw [h1, hcSumIndZero (p + 2)]
  have hE2 : (∑ x : ZMod p × ZMod (p + 2), (if x.1 = 0 then (1 : ℤ) else 0))
      = 1 * (((p + 2 : ℕ)) : ℤ) := by
    calc _ = ∑ x : ZMod p × ZMod (p + 2), (if x.1 = 0 then (1 : ℤ) else 0) * 1 := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (∑ a : ZMod p, (if a = 0 then (1 : ℤ) else 0)) *
          (∑ _b : ZMod (p + 2), (1 : ℤ)) :=
          hcProdSum p (p + 2) (fun a : ZMod p => (if a = 0 then (1 : ℤ) else 0))
            (fun _ : ZMod (p + 2) => (1 : ℤ))
      _ = _ := by rw [hcSumIndZero p, hcSumOne (p + 2)]
  have hsum : ∑ x, ψ x = -1 := by
    rw [Finset.sum_congr rfl (fun x _ => hψ x)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hA0, hE1, hE2]
    push_cast
    ring
  have haut : ∀ d : ZMod p × ZMod (p + 2), d ≠ 0 → ∑ x, ψ x * ψ (x + d) = -1 := by
    intro d hd
    obtain ⟨s, t⟩ := d
    have e1 : ∀ x : ZMod p × ZMod (p + 2), (x + (s, t)).1 = x.1 + s := fun x => rfl
    have e2 : ∀ x : ZMod p × ZMod (p + 2), (x + (s, t)).2 = x.2 + t := fun x => rfl
    have hexpand : ∀ x : ZMod p × ZMod (p + 2), ψ x * ψ (x + (s, t))
        = ((quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t))) +
          ((quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
          (((if x.2 + t = 0 then (1 : ℤ) else 0) *
            (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
            (if x.1 + s = 0 then (1 : ℤ) else 0))) +
          ((((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
            (if x.1 = 0 then (1 : ℤ) else 0)) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t))) +
          ((((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
            (if x.1 = 0 then (1 : ℤ) else 0)) *
          (((if x.2 + t = 0 then (1 : ℤ) else 0) *
            (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
            (if x.1 + s = 0 then (1 : ℤ) else 0))) := by
      intro x
      rw [hψ x, hψ (x + (s, t)), e1 x, e2 x]
      ring
    have hAA : (∑ x : ZMod p × ZMod (p + 2),
        (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
        (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t)))
        = (∑ a : ZMod p, quadraticChar (ZMod p) a * quadraticChar (ZMod p) (a + s)) *
          (∑ b : ZMod (p + 2), quadraticChar (ZMod (p + 2)) b *
            quadraticChar (ZMod (p + 2)) (b + t)) :=
      hcTwinAA p (p + 2) s t
    have hcross : (∑ x : ZMod p × ZMod (p + 2),
          (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
          (((if x.2 + t = 0 then (1 : ℤ) else 0) *
            (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
            (if x.1 + s = 0 then (1 : ℤ) else 0))) +
        (∑ x : ZMod p × ZMod (p + 2),
          (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
            (if x.1 = 0 then (1 : ℤ) else 0)) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t))) = 0 :=
      hcTwinCross p (p + 2) hFp hFq
        (fun x => quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2)
        (fun x => (if x.2 = 0 then (1 : ℤ) else 0) *
          (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
          (if x.1 = 0 then (1 : ℤ) else 0))
        (fun x => rfl) (fun x => rfl) s t hprod
    have hEE : (∑ x : ZMod p × ZMod (p + 2),
        (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
          (if x.1 = 0 then (1 : ℤ) else 0)) *
        (((if x.2 + t = 0 then (1 : ℤ) else 0) *
          (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
          (if x.1 + s = 0 then (1 : ℤ) else 0))) =
        ((if t = 0 then (1 : ℤ) else 0) * ((p : ℤ) + 2 + (if s = 0 then 1 else 0)) -
          2 * (1 + (if s = 0 then (1 : ℤ) else 0)) +
          (if s = 0 then (1 : ℤ) else 0) * (((p + 2 : ℕ)) : ℤ)) :=
      hcTwinEE p (p + 2)
        (fun x => (if x.2 = 0 then (1 : ℤ) else 0) *
          (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
          (if x.1 = 0 then (1 : ℤ) else 0))
        (fun x => rfl) s t
    rw [Finset.sum_congr rfl (fun x _ => hexpand x)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    by_cases hs : s ≠ 0 <;> by_cases ht : t ≠ 0
    · have eAA : (∑ x : ZMod p × ZMod (p + 2),
          (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t))) = 1 := by
        rw [hAA, hcShift hFp hs, hcShift hFq ht]
        ring
      have eEE : (∑ x : ZMod p × ZMod (p + 2),
          (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
            (if x.1 = 0 then (1 : ℤ) else 0)) *
          (((if x.2 + t = 0 then (1 : ℤ) else 0) *
            (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
            (if x.1 + s = 0 then (1 : ℤ) else 0))) = -2 := by
        rw [hEE]
        simp only [hs, ht, ite_false]
        ring
      linear_combination hcross + eAA + eEE
    · rw [not_not] at ht
      have hJq0 : (∑ b : ZMod (p + 2),
          quadraticChar (ZMod (p + 2)) b * quadraticChar (ZMod (p + 2)) (b + t))
          = ((((p + 2 : ℕ))) : ℤ) - 1 := by
        have h0 : ∀ b : ZMod (p + 2),
            quadraticChar (ZMod (p + 2)) b * quadraticChar (ZMod (p + 2)) (b + t)
            = quadraticChar (ZMod (p + 2)) b * quadraticChar (ZMod (p + 2)) b := by
          intro b
          rw [ht, add_zero]
        rw [Finset.sum_congr rfl (fun b _ => h0 b)]
        exact hcDiagZero (p + 2)
      have eAA : (∑ x : ZMod p × ZMod (p + 2),
          (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t)))
          = 1 - ((p : ℤ) + 2) := by
        rw [hAA, hcShift hFp hs, hJq0]
        push_cast
        ring
      have eEE : (∑ x : ZMod p × ZMod (p + 2),
          (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
            (if x.1 = 0 then (1 : ℤ) else 0)) *
          (((if x.2 + t = 0 then (1 : ℤ) else 0) *
            (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
            (if x.1 + s = 0 then (1 : ℤ) else 0))) = (p : ℤ) := by
        rw [hEE]
        simp only [ht, hs, ite_true, ite_false]
        push_cast
        ring
      linear_combination hcross + eAA + eEE
    · rw [not_not] at hs
      have hJp0 : (∑ a : ZMod p,
          quadraticChar (ZMod p) a * quadraticChar (ZMod p) (a + s)) = (p : ℤ) - 1 := by
        have h0 : ∀ a : ZMod p,
            quadraticChar (ZMod p) a * quadraticChar (ZMod p) (a + s)
            = quadraticChar (ZMod p) a * quadraticChar (ZMod p) a := by
          intro a
          rw [hs, add_zero]
        rw [Finset.sum_congr rfl (fun a _ => h0 a)]
        exact hcDiagZero p
      have eAA : (∑ x : ZMod p × ZMod (p + 2),
          (quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2) *
          (quadraticChar (ZMod p) (x.1 + s) * quadraticChar (ZMod (p + 2)) (x.2 + t)))
          = 1 - (p : ℤ) := by
        rw [hAA, hJp0, hcShift hFq ht]
        ring
      have eEE : (∑ x : ZMod p × ZMod (p + 2),
          (((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0))) -
            (if x.1 = 0 then (1 : ℤ) else 0)) *
          (((if x.2 + t = 0 then (1 : ℤ) else 0) *
            (1 + (if x.1 + s = 0 then (1 : ℤ) else 0))) -
            (if x.1 + s = 0 then (1 : ℤ) else 0))) = (p : ℤ) - 2 := by
        rw [hEE]
        simp only [hs, ht, ite_true, ite_false]
        push_cast
        ring
      linear_combination hcross + eAA + eEE
    · rw [not_not] at hs ht
      have h00 : (s, t) = (0 : ZMod p × ZMod (p + 2)) := Prod.ext_iff.mpr ⟨hs, ht⟩
      exact absurd h00 hd
  exact ⟨hsum, haut⟩

/-- **Hadamard matrices with circulant core: Paley and twin-prime cases.** Let $n$ be a natural
number such that either $n$ is a prime with $n \equiv 3 \pmod 4$, or $n = p(p + 2)$ for some
natural number $p$ with $p$ and $p + 2$ both prime. Then there is an $(n + 1) \times (n + 1)$
Hadamard matrix $H$ with integer entries, rows and columns indexed by $0, 1, \dots, n$ (so every
entry of $H$ is $1$ or $-1$ and $H^{\mathsf T} H = (n + 1) I$), that has a circulant core: there
is a function $v \colon \{0, \dots, n - 1\} \to \mathbb{Z}$ with $H_{i+1, j+1} = v(i - j)$ for
all $i, j \in \{0, \dots, n - 1\}$, where $i - j$ is taken modulo $n$.

Proves `Wanted` entry `exists_hadamard_matrix_with_circulant_core`. -/
public theorem exists_hadamard_matrix_with_circulant_core :
    ∀ (n : ℕ),
      ((Nat.Prime n ∧ n % 4 = 3) ∨
          (∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) ∧ n = p * (p + 2))) →
        ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
          isHadamardMatrix (n + 1) H ∧ hasCirculantCore n H := by
  classical
  intro n hn
  rcases hn with ⟨hp, hmod⟩ | ⟨p, hpp, hpq, rfl⟩
  · have _ := Fact.mk hp
    have hF : ringChar (ZMod n) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hval := hcPaleyVal n
      (fun x => quadraticChar (ZMod n) x - (if x = 0 then (1 : ℤ) else 0)) (fun x => rfl)
    have hpal := hcPaley n hmod hF
      (fun x => quadraticChar (ZMod n) x - (if x = 0 then (1 : ℤ) else 0)) (fun x => rfl)
    have htr := hcTransport (ZMod.finEquiv n).toAddEquiv
      (fun x => quadraticChar (ZMod n) x - (if x = 0 then (1 : ℤ) else 0))
      hval hpal.1 hpal.2
    exact hcMatrix
      ((fun x => quadraticChar (ZMod n) x - (if x = 0 then (1 : ℤ) else 0)) ∘
        (ZMod.finEquiv n).toAddEquiv)
      htr.1 htr.2.1 htr.2.2
  · have _ := Fact.mk hpp
    have _ := Fact.mk hpq
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hpq (by decide)
    have hmod4 : p % 4 = 3 ∨ p % 4 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · omega
    have hFp : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp2
    have hFq : ringChar (ZMod (p + 2)) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      have h2 := hpp.two_le
      omega
    have hqmod : (p + 2) % 4 = 3 ∨ (p + 2) % 4 = 1 := by omega
    have hprod : quadraticChar (ZMod p) (-1) * quadraticChar (ZMod (p + 2)) (-1) = -1 := by
      have hpneg := hcChiNegOne p hmod4
      have hqneg := hcChiNegOne (p + 2) hqmod
      rw [hpneg, hqneg]
      rcases hmod4 with h | h
      · have hq : ¬ (p + 2) % 4 = 3 := by omega
        rw [ite_eq_left h, ite_eq_right hq]
        ring
      · have hq : (p + 2) % 4 = 3 := by omega
        have hn : ¬ p % 4 = 3 := by omega
        rw [ite_eq_right hn, ite_eq_left hq]
        ring
    have hpos : 0 < p * (p + 2) := by
      have h2 := hpp.two_le
      exact Nat.mul_pos (by omega) (by omega)
    have _ : NeZero (p * (p + 2)) := ⟨by omega⟩
    have hcop : Nat.Coprime p (p + 2) := by
      rw [Nat.coprime_primes hpp hpq]
      omega
    have hval := hcTwinVal p (p + 2)
      (fun x => quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2 +
        ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
          (if x.1 = 0 then (1 : ℤ) else 0))) (fun x => rfl)
    have htwin := hcTwin p hFp hFq hprod
      (fun x => quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2 +
        ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
          (if x.1 = 0 then (1 : ℤ) else 0))) (fun x => rfl)
    have e := ((ZMod.finEquiv (p * (p + 2))).trans
      (ZMod.chineseRemainder hcop)).toAddEquiv
    have htr := hcTransport e
      (fun x => quadraticChar (ZMod p) x.1 * quadraticChar (ZMod (p + 2)) x.2 +
        ((if x.2 = 0 then (1 : ℤ) else 0) * (1 + (if x.1 = 0 then (1 : ℤ) else 0)) -
          (if x.1 = 0 then (1 : ℤ) else 0)))
      hval htwin.1 htwin.2
    exact hcMatrix _ htr.1 htr.2.1 htr.2.2

/-- **One-sided orthogonality characterizes Hadamard matrices.** Let $m$ be a natural number and
let $H$ be an $m \times m$ integer matrix. Then every entry of $H$ is $1$ or $-1$ and
$H^{\mathsf T} H = m I$ if and only if every entry of $H$ is a unitary element of $\mathbb{Z}$
(that is, $1$ or $-1$), $H H^{\mathsf T} = m I$ and $H^{\mathsf T} H = m I$. The right-hand side
is the general notion of a Hadamard matrix, with entries unitary and $H H^{*} = H^{*} H = m I$;
over $\mathbb{Z}$ the conjugate transpose $H^{*}$ is the transpose. -/
public theorem isHadamardMatrix_iff_isHadamard {m : ℕ} {H : Matrix (Fin m) (Fin m) ℤ} :
    isHadamardMatrix m H ↔ H.IsHadamard := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · constructor
    · intro _
      rw [Matrix.isHadamard_iff]
      exact ⟨fun i => i.elim0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    · intro _
      exact ⟨fun i => i.elim0, Subsingleton.elim _ _⟩
  · have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
    have hreg : IsRegular ((Fintype.card (Fin m) : ℤ)) := by
      rw [hcard]
      exact IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hmpos))
    constructor
    · rintro ⟨hentry, hmul⟩
      have hT : (Matrix.transpose H).IsHadamard :=
        Matrix.IsHadamard.of_mul_conjTranspose
        (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (by
          rw [Matrix.transpose_apply]
          exact hentry j i))
        (by
          rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
            hcard]
          exact hmul)
        hreg
      exact Matrix.isHadamard_transpose_iff.mp hT
    · intro h
      obtain ⟨hentry, -, hconj⟩ := (Matrix.isHadamard_iff H).mp h
      refine ⟨fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hentry i j), ?_⟩
      have hHT : Matrix.conjTranspose H = Matrix.transpose H :=
        Matrix.conjTranspose_eq_transpose_of_trivial H
      rw [hHT, hcard] at hconj
      exact hconj

/-- **A circulant core is a circulant submatrix.** Let $n$ be a natural number and let $H$ be an
$(n + 1) \times (n + 1)$ integer matrix with rows and columns indexed by $0, 1, \dots, n$. Then
$H$ has a circulant core, meaning that there is a function
$v \colon \{0, \dots, n - 1\} \to \mathbb{Z}$ with $H_{i+1, j+1} = v(i - j)$ for all
$i, j \in \{0, \dots, n - 1\}$, if and only if there is a function
$v \colon \{0, \dots, n - 1\} \to \mathbb{Z}$ such that the submatrix
$(H_{i+1, j+1})_{0 \le i, j \le n - 1}$ equals the circulant matrix of $v$, whose $(i, j)$
entry is $v(i - j)$. In both conditions $i - j$ is taken modulo $n$. -/
public theorem hasCirculantCore_iff_circulant {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} :
    hasCirculantCore n H ↔
      ∃ v : Fin n → ℤ, H.submatrix Fin.succ Fin.succ = Matrix.circulant v := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Matrix.ext_iff.mp (fun i j => by
      rw [Matrix.submatrix_apply, Matrix.circulant_apply]
      exact hv i j)⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, fun i j => by
      have h := Matrix.ext_iff.mpr hv i j
      rwa [Matrix.submatrix_apply, Matrix.circulant_apply] at h⟩

/-- **Circulant-core Hadamard matrices with orthogonal rows and columns.** Let $n$ be a natural
number such that either $n$ is a prime with $n \equiv 3 \pmod 4$, or $n = p(p + 2)$ for some
natural number $p$ with $p$ and $p + 2$ both prime. Then there is an $(n + 1) \times (n + 1)$
integer matrix $H$, with rows and columns indexed by $0, 1, \dots, n$, such that every entry of
$H$ is $1$ or $-1$, $H H^{\mathsf T} = (n + 1) I$ and $H^{\mathsf T} H = (n + 1) I$, and there
is a function $v \colon \{0, \dots, n - 1\} \to \mathbb{Z}$ such that the submatrix
$(H_{i+1, j+1})_{0 \le i, j \le n - 1}$ obtained by deleting row $0$ and column $0$ equals the
circulant matrix of $v$, whose $(i, j)$ entry is $v(i - j)$ with $i - j$ taken modulo $n$. -/
public theorem exists_isHadamard_with_circulant_core :
    ∀ (n : ℕ),
      ((Nat.Prime n ∧ n % 4 = 3) ∨
          (∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) ∧ n = p * (p + 2))) →
        ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
          H.IsHadamard ∧ ∃ v : Fin n → ℤ,
            H.submatrix Fin.succ Fin.succ = Matrix.circulant v := by
  intro n hn
  obtain ⟨H, hH, hC⟩ := exists_hadamard_matrix_with_circulant_core n hn
  exact ⟨H, isHadamardMatrix_iff_isHadamard.mp hH, hasCirculantCore_iff_circulant.mp hC⟩

end

end MetaMathlibExt
