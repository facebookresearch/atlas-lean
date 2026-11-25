/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.PatternContainment
public import MathlibExt.Combinatorics.Enumerative.PermutationStatistics
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Double ascents and double descents of pattern-avoiding permutations

`dascDdesGF_231_312` computes the joint generating function by splitting the avoiders
according to the direction of their first comparison.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

@[expose] public section

/-- **Length-three pattern from one-line values.** Given a bijection $v$ from $\{0, 1, 2\}$ to
itself, this is the permutation of $\{0, 1, 2\}$ that sends $i$ to $v(i)$. The values are listed
zero-based, so $v = (0, 2, 1)$ gives the pattern $132$ in the usual one-based one-line notation.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
public def pattern3 (v : Fin 3 → Fin 3) (hv : Function.Bijective v := by decide) :
    Equiv.Perm (Fin 3) where
  toFun := v
  invFun := Fintype.bijInv hv
  left_inv := Fintype.leftInverse_bijInv hv
  right_inv := Fintype.rightInverse_bijInv hv

/-- Classical pattern containment `HasPattern σ π` is decidable.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
public instance {n k : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin k → Fin k) :
    Decidable (HasPattern σ π) := by
  unfold HasPattern
  infer_instance

/-- **Ascent number of a permutation.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$,
$\operatorname{asc}(\sigma)$ is the number of positions $i$ with $i + 1 < n$ and
$\sigma(i) < \sigma(i + 1)$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public def permAscents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, σ i < σ ⟨i.val + 1, h⟩).card

/-- **Ascent–descent generating function of a pair of patterns.** For permutations $\tau$ and
$\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations of
$\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
ascent–descent generating function of $(\tau, \rho)$ is the formal power series
$$\sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)}
x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)}$$
in $x$ with coefficients in the polynomial ring $\mathbb{Q}[p, q]$, where $\mathrm{asc}(\sigma)$
and $\mathrm{des}(\sigma)$ are the numbers of ascents and descents of $\sigma$. The empty
permutation ($n = 0$) contributes the constant term $1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public noncomputable def ascDesGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 2) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permAscents σ * MvPolynomial.X 1 ^ permDescents σ

/-- **Double ascent–double descent generating function of a pair of patterns.** For
permutations $\tau$ and $\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations
of $\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
double ascent–double descent generating function of $(\tau, \rho)$ is the formal power series
$$\sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)}
x^n y^{\mathrm{dasc}(\sigma)} z^{\mathrm{ddes}(\sigma)}$$
in $x$ with coefficients in the polynomial ring $\mathbb{Q}[y, z]$, where $\mathrm{dasc}(\sigma)$
and $\mathrm{ddes}(\sigma)$ are the numbers of double ascents and double descents of $\sigma$.
The empty permutation ($n = 0$) contributes the constant term $1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`, `ddes`). -/
public noncomputable def dascDdesGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 2) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permDoubleAscents σ * MvPolynomial.X 1 ^ permDoubleDescents σ

namespace dascDdesGF_231_312

open Equiv.Perm

private abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

-- In an avoider, every entry between the endpoints of an inversion lies between their values.
private def Good {n : ℕ} (σ : Perm n) : Prop :=
  ∀ i j k, i < j → j < k → σ k < σ i → σ k < σ j ∧ σ j < σ i

private theorem good_iff {n : ℕ} (σ : Perm n) :
    Good σ ↔ ¬ HasPattern σ (pattern3 ![1, 2, 0]) ∧ ¬ HasPattern σ (pattern3 ![2, 0, 1]) := by
  constructor
  · intro h
    constructor
    · rintro ⟨e, he, hv⟩
      have hki := (hv 2 0).2 (by decide)
      have hij := (hv 0 1).2 (by decide)
      exact (h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide)) hki).2.asymm hij
    · rintro ⟨e, he, hv⟩
      have hki := (hv 2 0).2 (by decide)
      have hjk := (hv 1 2).2 (by decide)
      exact (h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide)) hki).1.asymm hjk
  · rintro ⟨h231, h312⟩ i j k hij hjk hki
    have he : StrictMono (![i, j, k] : Fin 3 → Fin n) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      fin_cases a <;> assumption
    have hne₁ := σ.injective.ne hij.ne
    have hne₂ := σ.injective.ne hjk.ne
    constructor
    · by_contra! h
      have hj := lt_of_le_of_ne h hne₂
      apply h312
      refine ⟨![i, j, k], fun _ _ hlt => he hlt, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;> simp [pattern3, hki, hj, hj.trans hki,
        hki.not_gt, hj.not_gt, (hj.trans hki).not_gt]
    · by_contra! h
      have hi := lt_of_le_of_ne h hne₁
      apply h231
      refine ⟨![i, j, k], fun _ _ hlt => he hlt, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;> simp [pattern3, hki, hi, hki.trans hi,
        hki.not_gt, hi.not_gt, (hki.trans hi).not_gt]

private noncomputable abbrev insert {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :=
  decomposeFin'Symm p σ

private theorem good_insert {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :
    Good (insert p σ) ↔ Good σ ∧ (p = 0 ∨ p = (σ 0).succ) := by
  constructor
  · intro h
    constructor
    · intro i j k hij hjk hki
      simpa [insert] using h i.succ j.succ k.succ (by simpa) (by simpa)
        (by simpa [insert] using hki)
    · cases p using Fin.cases with
      | zero => exact Or.inl rfl
      | succ q =>
        right
        suffices σ.symm q = 0 by simp [← this]
        by_contra hne
        have hp := h 0 (0 : Fin (n + 1)).succ (σ.symm q).succ (Fin.succ_pos _)
          (Fin.succ_lt_succ_iff.mpr (Fin.pos_iff_ne_zero.mpr hne))
          (by simp [insert])
        simp only [insert, decomposeFin'Symm_zero, decomposeFin'Symm_succ,
          Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_iff_succ_le,
          Fin.succ_le_succ_iff, Equiv.apply_symm_apply] at hp
        exact hp.1.not_ge hp.2
  · rintro ⟨h, hp⟩ i j k hij hjk hki
    cases k using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hjk).elim
    | succ k =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j =>
        have hjk' := Fin.succ_lt_succ_iff.mp hjk
        cases i using Fin.cases with
        | succ i =>
          simpa [insert] using h i j k (Fin.succ_lt_succ_iff.mp hij) hjk'
            (by simpa [insert] using hki)
        | zero =>
          rcases hp with rfl | rfl
          · simp [insert] at hki
          · simp only [insert, decomposeFin'Symm_zero, decomposeFin'Symm_succ,
              Fin.succAbove_lt_iff_succ_le, Fin.succ_le_succ_iff,
              Fin.succAbove_lt_succAbove_iff] at hki ⊢
            by_cases hj : j = 0
            · subst j
              exact ⟨lt_of_le_of_ne hki (σ.injective.ne hjk'.ne'), le_rfl⟩
            · have h0j := Fin.pos_iff_ne_zero.mpr hj
              have hk := lt_of_le_of_ne hki (σ.injective.ne (h0j.trans hjk').ne')
              obtain ⟨hkj, hj0⟩ := h 0 j k h0j hjk' hk
              exact ⟨hkj, hj0.le⟩

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev Y : R := MvPolynomial.X 0
private noncomputable abbrev Z : R := MvPolynomial.X 1

private noncomputable def weight {n : ℕ} (σ : Perm n) : R :=
  Y ^ permDoubleAscents σ * Z ^ permDoubleDescents σ

private noncomputable def total {n : ℕ} (f : Perm n → R) : R := by
  classical exact ∑ σ, if Good σ then f σ else 0

private theorem total_insert {n : ℕ} (f : Perm (n + 2) → R) :
    total f = total (fun σ => f (insert 0 σ)) + total (fun σ => f (insert (σ 0).succ σ)) := by
  classical
  unfold total
  rw [← (decomposeFin' (n := n)).symm.sum_comp, Fintype.sum_prod_type_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [decomposeFin'_symm, good_insert]
  by_cases h : Good σ
  · simp only [h, true_and, ite_true]
    have hne := Fin.succ_ne_zero (σ 0)
    calc
      _ = ∑ p : Fin (n + 2), ((if p = 0 then f (insert p σ) else 0) +
            (if p = (σ 0).succ then f (insert p σ) else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p = 0 <;> by_cases hq : p = (σ 0).succ <;> simp_all
      _ = _ := by simp [Finset.sum_add_distrib]
  · simp [h]

private theorem ascent_succ {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) (i : Fin (n + 1)) :
    IsDoubleAscentAt (insert p σ) i.succ ↔ IsDoubleAscentAt σ i := by
  unfold IsDoubleAscentAt
  constructor <;> rintro ⟨h, h₁, h₂⟩ <;>
    refine ⟨by simp only [Fin.val_succ] at h ⊢; omega, ?_⟩
  · change p.succAbove _ < p.succAbove _ at h₁ h₂
    exact ⟨Fin.succAbove_lt_succAbove_iff.mp h₁, Fin.succAbove_lt_succAbove_iff.mp h₂⟩
  · exact ⟨(Fin.strictMono_succAbove p) h₁, (Fin.strictMono_succAbove p) h₂⟩

private theorem descent_succ {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) (i : Fin (n + 1)) :
    IsDoubleDescentAt (insert p σ) i.succ ↔ IsDoubleDescentAt σ i := by
  unfold IsDoubleDescentAt
  constructor <;> rintro ⟨h, h₁, h₂⟩ <;>
    refine ⟨by simp only [Fin.val_succ] at h ⊢; omega, ?_⟩
  · change p.succAbove _ < p.succAbove _ at h₁ h₂
    exact ⟨Fin.succAbove_lt_succAbove_iff.mp h₁, Fin.succAbove_lt_succAbove_iff.mp h₂⟩
  · exact ⟨(Fin.strictMono_succAbove p) h₁, (Fin.strictMono_succAbove p) h₂⟩

private theorem weight_insert {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :
    weight (insert p σ) =
      (if IsDoubleAscentAt (insert p σ) 0 then Y else 1) *
      (if IsDoubleDescentAt (insert p σ) 0 then Z else 1) * weight σ := by
  simp only [weight, permDoubleAscents, permDoubleDescents, Finset.card_filter,
    Fin.sum_univ_succ (n := n + 1), ascent_succ, descent_succ, pow_add]
  split_ifs <;> simp_all <;> ring

-- The two possible insertions start respectively with an ascent and a descent.
private noncomputable abbrev up {n : ℕ} (σ : Perm (n + 1)) := insert 0 σ
private noncomputable abbrev down {n : ℕ} (σ : Perm (n + 1)) := insert (σ 0).succ σ

private theorem ascent_zero {n : ℕ} (p : Fin (n + 3)) (σ : Perm (n + 2)) :
    IsDoubleAscentAt (insert p σ) 0 ↔ p ≤ (σ 0).castSucc ∧ σ 0 < σ (Fin.succ 0) := by
  change (∃ _ : 0 + 2 < n + 3, p < p.succAbove (σ 0) ∧
    p.succAbove (σ 0) < p.succAbove (σ (Fin.succ 0))) ↔ _
  simp [Fin.lt_succAbove_iff_le_castSucc, show 0 + 2 < n + 3 by omega]

private theorem descent_zero {n : ℕ} (p : Fin (n + 3)) (σ : Perm (n + 2)) :
    IsDoubleDescentAt (insert p σ) 0 ↔ (σ 0).castSucc < p ∧ σ (Fin.succ 0) < σ 0 := by
  change (∃ _ : 0 + 2 < n + 3, p.succAbove (σ 0) < p ∧
    p.succAbove (σ (Fin.succ 0)) < p.succAbove (σ 0)) ↔ _
  simp [show 0 + 2 < n + 3 by omega]

private theorem weights {n : ℕ} (σ : Perm (n + 1)) :
    weight (up (up σ)) = Y * weight (up σ) ∧
    weight (up (down σ)) = weight (down σ) ∧
    weight (down (up σ)) = weight (up σ) ∧
    weight (down (down σ)) = Z * weight (down σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [weight_insert] <;>
    simp only [ascent_zero, descent_zero, up, down, insert, decomposeFin'Symm_succ,
      decomposeFin'Symm_zero, Fin.zero_succAbove, Fin.succAbove_succ_self] <;>
    simp [(σ 0).castSucc_lt_succ.not_gt]

private noncomputable def rising (n : ℕ) : R := total fun σ : Perm (n + 1) => weight (up σ)
private noncomputable def falling (n : ℕ) : R := total fun σ : Perm (n + 1) => weight (down σ)

private theorem total_mul {n : ℕ} (c : R) (f : Perm n → R) :
    (total fun σ => c * f σ) = c * total f := by
  classical simp [total, Finset.mul_sum, mul_ite]

private theorem rising_succ (n : ℕ) : rising (n + 1) = Y * rising n + falling n := by
  unfold rising falling
  rw [total_insert]
  simp_rw [fun σ => (weights σ).1, fun σ => (weights σ).2.1]
  rw [total_mul]

private theorem falling_succ (n : ℕ) : falling (n + 1) = rising n + Z * falling n := by
  unfold rising falling
  rw [total_insert]
  simp_rw [fun σ => (weights σ).2.2.1, fun σ => (weights σ).2.2.2]
  rw [total_mul]

private theorem weight_small {n : ℕ} (h : n ≤ 2) (σ : Perm n) : weight σ = 1 := by
  have ha (i : Fin n) : ¬ IsDoubleAscentAt σ i := fun ⟨hi, _⟩ => by omega
  have hd (i : Fin n) : ¬ IsDoubleDescentAt σ i := fun ⟨hi, _⟩ => by omega
  simp [weight, permDoubleAscents, permDoubleDescents, ha, hd]

private theorem good_small {n : ℕ} (h : n ≤ 1) (σ : Perm n) : Good σ := by
  intro i j k hij hjk
  have := k.isLt
  change i.val < j.val at hij
  change j.val < k.val at hjk
  omega

private theorem initial : rising 0 = 1 ∧ falling 0 = 1 := by
  classical
  simp [rising, falling, total, weight_small (by decide : 2 ≤ 2), good_small (by decide : 1 ≤ 1)]

open PowerSeries

private noncomputable abbrev H := dascDdesGF (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1])

private theorem coeff_H (n : ℕ) : coeff n H = total (@weight n) := by
  classical
  simp only [H, dascDdesGF, coeff_mk, Finset.sum_filter, total, weight, good_iff]

private theorem series_eq :
    H = 1 + X + X ^ 2 * (mk rising + mk falling) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_H]
  match n with
  | 0 | 1 =>
    simp [total, good_small, weight_small, coeff_one, coeff_X, coeff_X_pow_mul']
  | n + 2 =>
    rw [total_insert]
    simp [coeff_one, coeff_X, rising, falling]

private theorem rising_series :
    mk rising = 1 + X * (C Y * mk rising + mk falling) := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [coeff_one, initial.1, rising_succ, coeff_C_mul]

private theorem falling_series :
    mk falling = 1 + X * (mk rising + C Z * mk falling) := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [coeff_one, initial.2, falling_succ, coeff_C_mul]

end dascDdesGF_231_312

open dascDdesGF_231_312

-- Keep the default bijectivity proofs for the two patterns inline in the statement.
set_option backward.proofsInPublic true in
/-- **Double ascents and double descents over permutations avoiding $231$ and $312$.** Let
$$H = \sum_{n \ge 0} \sum_{\sigma} x^n y^{\mathrm{dasc}(\sigma)} z^{\mathrm{ddes}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$231$ and $312$, and $\mathrm{dasc}(\sigma)$ and $\mathrm{ddes}(\sigma)$ are the numbers of
double ascents and double descents of $\sigma$; $H$ is a formal power series in $x$ with
coefficients in $\mathbb{Q}[y, z]$. Then
$$(1 - x(y + z) - x^2(1 - yz))\, H = 1 + x^2(1 + x)(1 - y)(1 - z) + x(1 - y - z).$$

The source's Corollary 3 also gives an identity (22) for ascents and descents, marked by $p$
and $q$, and an identity (24) for peaks and valleys, marked by $\ell$ and $m$, over this class;
both are false as printed (at $p = 2$, $q = 1$ the coefficient of $x^5$ in (22) is $75$, the true
value $81$; at $\ell = 2$, $m = 1$ the coefficient of $x^5$ in (24) is $28$, the true value
$29$).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 3
(`integers-2026-A18-cor-3`). -/
public theorem dascDdesGF_231_312 :
    let x : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.X
    let y : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let z : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - x * (y + z) - x ^ 2 * (1 - y * z)) *
        dascDdesGF (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1]) =
      1 + x ^ 2 * (1 + x) * (1 - y) * (1 - z) + x * (1 - y - z) := by
  dsimp only
  rw [show dascDdesGF _ _ = _ from series_eq]
  linear_combination
    PowerSeries.X ^ 2 * (1 + PowerSeries.X * (1 - PowerSeries.C Z)) * rising_series +
    PowerSeries.X ^ 2 * (1 + PowerSeries.X * (1 - PowerSeries.C Y)) * falling_series

end

end MetaMathlibExt
