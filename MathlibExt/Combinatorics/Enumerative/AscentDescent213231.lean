/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.DoubleAscentDescent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Ascents and descents of permutations avoiding 213 and 231

The first value of a nonempty avoider is either the minimum or the maximum. For lengths at
least two these two prefixes add one ascent or one descent, respectively, to the standardized tail.

## References

* Tian Han, *Joint Distributions of 10 Classical Statistics over Permutations Avoiding Two
  Patterns of Length 3*, INTEGERS 26 (2026), Article A18, pp. 1–22, §2.4 and Corollary 4,
  equation (30).
* Michael Bukata, Ryan Kulwicki, Nicholas Lewandowski, Lara Pudwell, Jacob Roth, and Teresa
  Wheeland, *Distributions of Statistics Over Pattern-Avoiding Permutations*, Journal of
  Integer Sequences 22 (2019), Article 19.2.6, pp. 1–22, §4.2 and Proposition 10
  (<https://cs.uwaterloo.ca/journals/JIS/VOL22/Pudwell/pudwell6.pdf>). The first-entry
  minimum/maximum argument and its correspondence with ascents and descents are used here.
* Tian Han and Sergey Kitaev, *Joint distributions of statistics over permutations avoiding
  two patterns of length 3*, Discrete Mathematics and Theoretical Computer Science 26(1)
  (2024), Article 4, pp. 1–25, §2.4, Theorem 2.22 (the earlier joint distribution).
* Rodica Simion and Frank W. Schmidt, *Restricted Permutations*, European Journal of
  Combinatorics 6 (1985), 383–406, the two-pattern enumeration recalled in Han's Theorem 1(d).
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace ascDesGF_213_231

open Equiv.Perm

private abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

-- Neither order of the two later entries can put the first value strictly between them.
private def Avoids {n : ℕ} (σ : Perm n) : Prop :=
  ∀ i j k, i < j → j < k →
    ¬ ((σ j < σ i ∧ σ i < σ k) ∨ (σ k < σ i ∧ σ i < σ j))

private theorem avoids_iff {n : ℕ} (σ : Perm n) :
    Avoids σ ↔ ¬ HasPattern σ (pattern3 ![1, 0, 2]) ∧ ¬ HasPattern σ (pattern3 ![1, 2, 0]) := by
  constructor
  · intro h
    constructor
    · rintro ⟨e, he, hv⟩
      exact h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide))
        (Or.inl ⟨(hv 1 0).2 (by decide), (hv 0 2).2 (by decide)⟩)
    · rintro ⟨e, he, hv⟩
      exact h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide))
        (Or.inr ⟨(hv 2 0).2 (by decide), (hv 0 1).2 (by decide)⟩)
  · rintro ⟨h213, h231⟩ i j k hij hjk hvals
    have he : StrictMono (![i, j, k] : Fin 3 → Fin n) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      fin_cases a <;> assumption
    rcases hvals with ⟨hji, hik⟩ | ⟨hki, hij'⟩
    · apply h213
      refine ⟨![i, j, k], fun _ _ h => he h, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [pattern3, hji, hik, hji.trans hik, hji.not_gt, hik.not_gt, (hji.trans hik).not_gt]
    · apply h231
      refine ⟨![i, j, k], fun _ _ h => he h, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [pattern3, hki, hij', hki.trans hij', hki.not_gt, hij'.not_gt, (hki.trans hij').not_gt]

private theorem first_extreme {n : ℕ} {σ : Perm (n + 1)} (h : Avoids σ) :
    σ 0 = 0 ∨ σ 0 = Fin.last n := by
  by_contra! hne
  have hmin : (0 : Fin (n + 1)) < σ 0 := Fin.pos_iff_ne_zero.mpr hne.1
  have hmax : σ 0 < Fin.last n := Fin.lt_last_iff_ne_last.mpr hne.2
  let i := σ.symm 0
  let j := σ.symm (Fin.last n)
  have hi : 0 < i := Fin.pos_iff_ne_zero.mpr (fun hi => hne.1 ((σ.symm_apply_eq.mp hi).symm))
  have hj : 0 < j := Fin.pos_iff_ne_zero.mpr (fun hj => hne.2 ((σ.symm_apply_eq.mp hj).symm))
  obtain hij | hji := lt_or_gt_of_ne (show i ≠ j from fun hij =>
    (hmin.trans hmax).ne (σ.symm.injective hij))
  · exact h 0 i j hi hij (Or.inl (by simpa [i, j] using And.intro hmin hmax))
  · exact h 0 j i hj hji (Or.inr (by simpa [i, j] using And.intro hmin hmax))

-- The inverse of `decomposeFin'` prepends a value and standardizes the other values.
private noncomputable abbrev prepend {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) : Perm (n + 2) :=
  decomposeFin'Symm p σ

private theorem avoids_prepend {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :
    Avoids (prepend p σ) ↔ Avoids σ ∧ (p = 0 ∨ p = Fin.last (n + 1)) := by
  constructor
  · intro h
    refine ⟨?_, by simpa [decomposeFin'Symm_zero] using first_extreme h⟩
    intro i j k hij hjk
    simpa [decomposeFin'Symm_succ, Fin.succAbove_lt_succAbove_iff] using
      h i.succ j.succ k.succ (Fin.succ_lt_succ_iff.mpr hij) (Fin.succ_lt_succ_iff.mpr hjk)
  · rintro ⟨h, hp⟩ i j k hij hjk
    cases k using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hjk).elim
    | succ k =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j =>
        cases i using Fin.cases with
        | zero =>
          rcases hp with rfl | rfl
          · simp [decomposeFin'Symm_zero]
          · simp [decomposeFin'Symm_zero, not_lt_of_ge (Fin.le_last _)]
        | succ i =>
          simpa [decomposeFin'Symm_succ, Fin.succAbove_lt_succAbove_iff] using
            h i j k (Fin.succ_lt_succ_iff.mp hij) (Fin.succ_lt_succ_iff.mp hjk)

private theorem card_adjacent {n : ℕ} (r : Fin (n + 1) → Fin (n + 1) → Prop)
    [DecidableRel r] :
    (Finset.univ.filter fun i : Fin (n + 1) =>
      ∃ h : i.val + 1 < n + 1, r i ⟨i.val + 1, h⟩).card =
      ∑ i : Fin n, if r i.castSucc i.succ then 1 else 0 := by
  rw [Finset.card_filter, Fin.sum_univ_castSucc]
  simp
  rfl

private theorem ascents_eq_sum {n : ℕ} (σ : Perm (n + 1)) :
    permAscents σ = ∑ i : Fin n, if σ i.castSucc < σ i.succ then 1 else 0 :=
  card_adjacent (fun i j => σ i < σ j)

private theorem descents_eq_sum {n : ℕ} (σ : Perm (n + 1)) :
    permDescents σ = ∑ i : Fin n, if σ i.succ < σ i.castSucc then 1 else 0 :=
  card_adjacent (fun i j => σ j < σ i)

private theorem prepend_one {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :
    prepend p σ 1 = p.succAbove (σ 0) := decomposeFin'Symm_succ p σ 0

private theorem ascents_prepend {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :
    permAscents (prepend p σ) = permAscents σ +
      (if p < p.succAbove (σ 0) then 1 else 0) := by
  rw [ascents_eq_sum, Fin.sum_univ_succ, ascents_eq_sum, add_comm]
  simp [prepend_one]

private theorem descents_prepend {n : ℕ} (p : Fin (n + 2)) (σ : Perm (n + 1)) :
    permDescents (prepend p σ) = permDescents σ +
      (if p.succAbove (σ 0) < p then 1 else 0) := by
  rw [descents_eq_sum, Fin.sum_univ_succ, descents_eq_sum, add_comm]
  simp [prepend_one]

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev P : R := MvPolynomial.X 0
private noncomputable abbrev Q : R := MvPolynomial.X 1

private noncomputable def weight {n : ℕ} (σ : Perm n) : R :=
  P ^ permAscents σ * Q ^ permDescents σ

private noncomputable def total {n : ℕ} (f : Perm n → R) : R := by
  classical exact ∑ σ, if Avoids σ then f σ else 0

private theorem total_prepend {n : ℕ} (f : Perm (n + 2) → R) :
    total f = total (fun σ => f (prepend 0 σ)) +
      total (fun σ => f (prepend (Fin.last (n + 1)) σ)) := by
  classical
  unfold total
  rw [← (decomposeFin' (n := n)).symm.sum_comp, Fintype.sum_prod_type_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [decomposeFin'_symm, avoids_prepend]
  by_cases h : Avoids σ
  · simp only [h, true_and, ite_true]
    have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := (Fin.pos_iff_ne_zero.mp (by
      change 0 < n + 1
      omega)).symm
    calc
      _ = ∑ p : Fin (n + 2), ((if p = 0 then f (prepend p σ) else 0) +
          (if p = Fin.last (n + 1) then f (prepend p σ) else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p = 0 <;> by_cases hq : p = Fin.last (n + 1) <;> simp_all
      _ = _ := by simp [Finset.sum_add_distrib]
  · simp [h]

private theorem total_succ_succ (n : ℕ) :
    total (weight (n := n + 2)) = (P + Q) * total (weight (n := n + 1)) := by
  classical
  have hmin (σ : Perm (n + 1)) : weight (prepend 0 σ) = P * weight σ := by
    simp [weight, ascents_prepend, descents_prepend, pow_succ]
    ring
  have hmax (σ : Perm (n + 1)) : weight (prepend (Fin.last (n + 1)) σ) = Q * weight σ := by
    simp [weight, ascents_prepend, descents_prepend, Fin.succAbove_last, pow_succ,
      not_lt_of_ge (Fin.le_last _)]
    ring
  rw [total_prepend, add_mul]
  simp only [total, hmin, hmax, Finset.mul_sum, mul_ite, mul_zero]

private theorem total_small {n : ℕ} (hn : n ≤ 1) : total (weight (n := n)) = 1 := by
  classical
  have hav (σ : Perm n) : Avoids σ := by
    intro i j k hij hjk
    have := k.isLt
    change i.val < j.val at hij
    change j.val < k.val at hjk
    omega
  have hnext (i : Fin n) : ¬ i.val + 1 < n := by omega
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  simp [total, hav, weight, permAscents, permDescents, hnext]

open PowerSeries

private noncomputable abbrev G := ascDesGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0])

private theorem coeff_G (n : ℕ) : coeff n G = total (weight (n := n)) := by
  classical
  simp only [G, ascDesGF, coeff_mk, total, ← Finset.sum_filter, weight, avoids_iff]

end ascDesGF_213_231

open ascDesGF_213_231 PowerSeries

-- Keep the default bijectivity proofs for the patterns inline in the statement.
set_option backward.proofsInPublic true in
/-- **Ascents and descents over permutations avoiding $213$ and $231$.** Let
$$G = \sum_{n \ge 0} \sum_{\sigma} x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$213$ and $231$, and $\mathrm{asc}(\sigma)$ and $\mathrm{des}(\sigma)$ are the numbers of ascents
and descents of $\sigma$; $G$ is a formal power series in $x$ with coefficients in
$\mathbb{Q}[p, q]$. Then
$$(1 - px - qx)\, G = 1 + x - px - qx.$$

The lead-in of the source's Corollary 4 names the permutations avoiding $213$ and $312$ instead;
both classes have this distribution of ascents and descents.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 4
(`integers-2026-A18-cor-4`). -/
public theorem ascDesGF_213_231 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - p * PowerSeries.X - q * PowerSeries.X) *
        ascDesGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) =
      1 + PowerSeries.X - p * PowerSeries.X - q * PowerSeries.X := by
  change (1 - C P * X - C Q * X) * G = 1 + X - C P * X - C Q * X
  rw [sub_mul, sub_mul, one_mul, mul_assoc, mul_assoc]
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | n
  · have hzero : constantCoeff G = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_G, total_small (Nat.zero_le 1)]
    simp [hzero]
  · simp [coeff_G, total_small, coeff_C_mul]
  · simp [coeff_G, total_succ_succ, coeff_C_mul, coeff_X]
    ring

end MetaMathlibExt
