/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.Ring

@[expose] public section

section
open scoped BigOperators

namespace MetaMathlibExt

/-- The auxiliary series `q = 1 - x + x * y` appearing in the denominator factors. -/
private noncomputable def qSeries : MvPowerSeries (Fin 2) ℚ :=
  (1 : MvPowerSeries (Fin 2) ℚ) - MvPowerSeries.X 0 +
    MvPowerSeries.X 0 * MvPowerSeries.X 1

/-- The denominator factors `D_j = q ^ j - y`. -/
private noncomputable def dSeries (j : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  qSeries ^ j - MvPowerSeries.X 1

/-- The right-hand side of the main theorem, as a function of `k`. -/
private noncomputable def tSeries (k : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  let x : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 0
  let y : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 1
  x ^ k * y ^ (k - 1) * (1 - y) ^ k *
    (∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - y))⁻¹

private theorem qSeries_constantCoeff : MvPowerSeries.constantCoeff qSeries = 1 := by
  unfold qSeries
  simp [MvPowerSeries.constantCoeff_X]

private theorem dSeries_constantCoeff (j : ℕ) :
    MvPowerSeries.constantCoeff (dSeries j) = 1 := by
  unfold dSeries
  simp [qSeries_constantCoeff, MvPowerSeries.constantCoeff_X]

private theorem dSeries_constCoeff_ne (j : ℕ) :
    MvPowerSeries.constantCoeff (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)) ≠ 0 := by
  have h : MvPowerSeries.constantCoeff (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)) = 1 := by
    simp [qSeries, MvPowerSeries.constantCoeff_X]
  rw [h]
  exact one_ne_zero

-- Splitting the Icc product at the top (used for the `T_k` recurrence).
private theorem prod_Icc_split_top (k : ℕ) (hk : 2 ≤ k) :
    ∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)) =
      (∏ j ∈ Finset.Icc 1 (k - 1), (qSeries ^ j - MvPowerSeries.X (1 : Fin 2))) *
        (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) := by
  have hk1 : k - 1 + 1 = k := by omega
  conv_lhs => rw [← hk1]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k - 1 + 1), hk1]

-- Step 5 (analytic part): the right-hand side satisfies `T_k * D_k = x * y * (1 - y) * T_{k-1}`.
private theorem tSeries_recurrence (k : ℕ) (hk : 2 ≤ k) :
    tSeries k * (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        (1 - MvPowerSeries.X (1 : Fin 2)) * tSeries (k - 1) := by
  have hk1 : k - 1 + 1 = k := by omega
  have hD : MvPowerSeries.constantCoeff
      (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) ≠ 0 :=
    dSeries_constCoeff_ne k
  have hsplit : ∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)) =
      (∏ j ∈ Finset.Icc 1 (k - 1), (qSeries ^ j - MvPowerSeries.X (1 : Fin 2))) *
        (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) := by
    conv_lhs => rw [← hk1]
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k - 1 + 1), hk1]
  have hcancel : ((∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - MvPowerSeries.X (1 : Fin 2))))⁻¹ *
      (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) =
      ((∏ j ∈ Finset.Icc 1 (k - 1), (qSeries ^ j - MvPowerSeries.X (1 : Fin 2))))⁻¹ := by
    rw [hsplit, MvPowerSeries.mul_inv_rev,
      mul_comm ((qSeries ^ k - MvPowerSeries.X (1 : Fin 2))⁻¹) _,
      mul_assoc, MvPowerSeries.inv_mul_cancel _ hD, mul_one]
  unfold tSeries
  simp only
  have hx : ((MvPowerSeries.X (0 : Fin 2)) : MvPowerSeries (Fin 2) ℚ) ^ k =
      MvPowerSeries.X (0 : Fin 2) * (MvPowerSeries.X (0 : Fin 2)) ^ (k - 1) := by
    conv_lhs => rw [← hk1]
    rw [pow_succ']
  have hy : ((MvPowerSeries.X (1 : Fin 2)) : MvPowerSeries (Fin 2) ℚ) ^ (k - 1) =
      MvPowerSeries.X (1 : Fin 2) * (MvPowerSeries.X (1 : Fin 2)) ^ (k - 1 - 1) := by
    have : k - 1 = (k - 1 - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ']
  have h1y : ((1 - MvPowerSeries.X (1 : Fin 2)) : MvPowerSeries (Fin 2) ℚ) ^ k =
      (1 - MvPowerSeries.X (1 : Fin 2)) *
        (1 - MvPowerSeries.X (1 : Fin 2)) ^ (k - 1) := by
    conv_lhs => rw [← hk1]
    rw [pow_succ']
  have hcancelA : ∀ A : MvPowerSeries (Fin 2) ℚ,
      A * (∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)))⁻¹ *
        (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) =
        A * (∏ j ∈ Finset.Icc 1 (k - 1),
          (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)))⁻¹ := by
    intro A
    calc A * (∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)))⁻¹ *
          (qSeries ^ k - MvPowerSeries.X (1 : Fin 2))
        = A * ((∏ j ∈ Finset.Icc 1 k,
            (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)))⁻¹ *
            (qSeries ^ k - MvPowerSeries.X (1 : Fin 2))) := by rw [mul_assoc]
      _ = A * (∏ j ∈ Finset.Icc 1 (k - 1),
            (qSeries ^ j - MvPowerSeries.X (1 : Fin 2)))⁻¹ := by rw [hcancel]
  rw [hx, h1y, hcancelA]
  rw [hy]
  ring

-- Step 5 base case: `T_1 * D_1 = x * (1 - y)`.
private theorem tSeries_base :
    tSeries 1 * (qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) * (1 - MvPowerSeries.X (1 : Fin 2)) := by
  have hD : MvPowerSeries.constantCoeff
      (qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2)) ≠ 0 :=
    dSeries_constCoeff_ne 1
  have hprod : (∏ j ∈ Finset.Icc 1 1,
      (qSeries ^ j - MvPowerSeries.X (1 : Fin 2))) =
      (qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2)) := by
    rw [Finset.Icc_self]
    exact Finset.prod_singleton _ _
  have e1 : (1 - 1 : ℕ) = 0 := rfl
  unfold tSeries
  simp only
  rw [e1, pow_zero, mul_one, pow_one, pow_one, hprod, mul_assoc,
    MvPowerSeries.inv_mul_cancel _ hD, mul_one]

-- Step 4 (combinatorial preliminaries for `k = 1`):
-- every map into `Fin 1` is constant, so no rise ever occurs.
private theorem card_k1_rises (N : ℕ) :
    (Finset.univ.filter fun p : Fin N × Fin N =>
      p.2.val = p.1.val + 1 ∧ (fun _ : Fin N => (0 : Fin 1)) p.1 <
        (fun _ : Fin N => (0 : Fin 1)) p.2).card = 0 := by
  rw [Finset.filter_false_of_mem]
  · exact Finset.card_empty
  · intro p _
    exact fun h => lt_irrefl _ h.2

-- Any function into `Fin 1` equals the constant zero function.
private theorem fun_to_fin1_eq (N : ℕ) (π : Fin N → Fin 1) : π = fun _ => 0 := by
  funext i
  exact Subsingleton.elim _ _

-- Canonical all-zero word is surjective when `N ≥ 1`.
private theorem const0_surjective (N : ℕ) (hN : 1 ≤ N) :
    Function.Surjective (fun _ : Fin N => (0 : Fin 1)) := by
  intro b
  have hb : b = 0 := Subsingleton.elim _ _
  exact ⟨⟨0, by omega⟩, by simp [hb]⟩

-- The all-zero word satisfies the RG condition.
private theorem const0_rg (N : ℕ) :
    ∀ i : Fin N,
      ((fun _ : Fin N => (0 : Fin 1)) i).val ≤
        ((Finset.univ.filter fun j : Fin N => j < i).image
          (fun _ : Fin N => (0 : Fin 1))).card := by
  intro i
  exact Nat.zero_le _

-- Rises of any word into `Fin 1` equal zero.
private theorem rises_k1_eq_zero (N : ℕ) (π : Fin N → Fin 1) :
    (Finset.univ.filter fun p : Fin N × Fin N =>
      p.2.val = p.1.val + 1 ∧ π p.1 < π p.2).card = 0 := by
  have hπ : π = fun _ => (0 : Fin 1) := fun_to_fin1_eq N π
  rw [hπ]
  exact card_k1_rises N

-- Full `k = 1` counting identity: the only `1`-block RGFs are the all-zero
-- words of length `N ≥ 1`, which have `0` rises.
private theorem card_k1 (N r : ℕ) :
    Fintype.card {π : Fin N → Fin 1 //
      Function.Surjective π ∧
        (∀ i : Fin N,
          (π i).val ≤
            ((Finset.univ.filter fun j : Fin N => j < i).image π).card) ∧
        (Finset.univ.filter fun p : Fin N × Fin N =>
          p.2.val = p.1.val + 1 ∧ π p.1 < π p.2).card = r} =
      (if 1 ≤ N ∧ r = 0 then 1 else 0) := by
  by_cases h : 1 ≤ N ∧ r = 0
  · rw [ite_eq_left h]
    obtain ⟨hN, hr⟩ := h
    subst hr
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨_, const0_surjective N hN, const0_rg N, ?_⟩, fun y => ?_⟩
    · change (Finset.univ.filter fun p : Fin N × Fin N =>
        p.2.val = p.1.val + 1 ∧
          (fun _ : Fin N => (0 : Fin 1)) p.1 < (fun _ : Fin N => (0 : Fin 1)) p.2).card = 0
      exact card_k1_rises N
    · obtain ⟨π, hπ⟩ := y
      apply Subtype.ext
      exact fun_to_fin1_eq N π
  · rw [ite_eq_right h]
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun a => ?_⟩
    obtain ⟨π, hsurj, hrg, hrise⟩ := a
    have h0 : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.2.val = p.1.val + 1 ∧ π p.1 < π p.2).card = 0 :=
      rises_k1_eq_zero N π
    rw [h0] at hrise
    by_cases hN : 1 ≤ N
    · exact h ⟨hN, hrise.symm⟩
    · have hN0 : N = 0 := by omega
      subst hN0
      obtain ⟨a, _⟩ := hsurj 0
      exact Fin.elim0 a

-- Step 1 (one-letter extension, image part): the image of a `snoc` word is the
-- prefix image with the new letter inserted.
private theorem image_snoc (k n : ℕ) (p : Fin n → Fin k) (x : Fin k) :
    Finset.univ.image (Fin.snoc p x) = insert x (Finset.univ.image p) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hlast : i = Fin.last n
    · left
      rw [hlast] at hi
      rw [Fin.snoc_last] at hi
      exact hi.symm
    · right
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hlast
      refine ⟨j, ?_⟩
      rwa [Fin.snoc_castSucc] at hi
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨Fin.last n, by rw [Fin.snoc_last]⟩
    · exact ⟨j.castSucc, by rw [Fin.snoc_castSucc]; exact hj⟩

-- Step 1 (castSucc transport): composing a word with `Fin.castSucc` preserves
-- the rise count, since `castSucc` is strictly monotone.
private theorem rises_castSucc_comp (N k : ℕ) (p : Fin N → Fin (k + 1)) :
    (Finset.univ.filter fun q : Fin N × Fin N =>
      q.2.val = q.1.val + 1 ∧ (Fin.castSucc ∘ p) q.1 < (Fin.castSucc ∘ p) q.2).card =
    (Finset.univ.filter fun q : Fin N × Fin N =>
      q.2.val = q.1.val + 1 ∧ p q.1 < p q.2).card := by
  have h : (Finset.univ.filter fun q : Fin N × Fin N =>
      q.2.val = q.1.val + 1 ∧ (Fin.castSucc ∘ p) q.1 < (Fin.castSucc ∘ p) q.2) =
    (Finset.univ.filter fun q : Fin N × Fin N =>
      q.2.val = q.1.val + 1 ∧ p q.1 < p q.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Fin.castSucc_lt_castSucc_iff]
  rw [h]

-- Transport preserves the RG bound values.
private theorem val_castSucc_comp (k : ℕ) (a : Fin (k + 1)) :
    ((Fin.castSucc a : Fin (k + 2))).val = a.val := by
  rfl

-- Every value of a castSucc-transported word is below the top element.
private theorem castSucc_lt_last (k : ℕ) (a : Fin (k + 1)) :
    (Fin.castSucc a : Fin (k + 2)) < Fin.last (k + 1) :=
  Fin.castSucc_lt_last a

-- Step 1 (castSucc transport): the RG condition is preserved under `castSucc`,
-- since `castSucc` is injective and preserves values.
private theorem rg_castSucc_comp (N k : ℕ) (p : Fin N → Fin (k + 1))
    (h : ∀ i : Fin N, (p i).val ≤
      ((Finset.univ.filter fun j : Fin N => j < i).image p).card)
    (i : Fin N) :
    (((Fin.castSucc ∘ p) i : Fin (k + 2))).val ≤
      ((Finset.univ.filter fun j : Fin N => j < i).image (Fin.castSucc ∘ p)).card := by
  have himg : ((Finset.univ.filter fun j : Fin N => j < i).image (Fin.castSucc ∘ p)) =
      (((Finset.univ.filter fun j : Fin N => j < i).image p).image Fin.castSucc) :=
    (Finset.image_image).symm
  rw [himg, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  exact h i

-- Core counting definitions matching the main theorem predicate.
private def IsRGF (N k : ℕ) (π : Fin N → Fin k) : Prop :=
  Function.Surjective π ∧
    ∀ i : Fin N,
      (π i).val ≤
        ((Finset.univ.filter fun j : Fin N => j < i).image π).card

private def risesCount (N k : ℕ) (π : Fin N → Fin k) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N =>
    p.2.val = p.1.val + 1 ∧ π p.1 < π p.2).card

private def countRGF (N r k : ℕ) : ℕ :=
  Fintype.card
    {π : Fin N → Fin k //
      Function.Surjective π ∧
        (∀ i : Fin N,
          (π i).val ≤
            ((Finset.univ.filter fun j : Fin N => j < i).image π).card) ∧
        risesCount N k π = r}

private noncomputable def aSeries (k : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  fun d => (countRGF (d 0) (d 1) k : ℚ)

private def countLast (n r k : ℕ) (c : Fin k) : ℕ :=
  Fintype.card
    {π : Fin (n + 1) → Fin k //
      Function.Surjective π ∧
        (∀ i : Fin (n + 1),
          (π i).val ≤
            ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image π).card) ∧
        risesCount (n + 1) k π = r ∧ π (Fin.last n) = c}

private noncomputable def bSeries (k : ℕ) (c : Fin k) :
    MvPowerSeries (Fin 2) ℚ :=
  fun d => if d 0 = 0 then 0 else (countLast (d 0 - 1) (d 1) k c : ℚ)

private theorem coeff_aSeries (k : ℕ) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (aSeries k) = (countRGF (d 0) (d 1) k : ℚ) :=
  rfl

private theorem coeff_bSeries (k : ℕ) (c : Fin k) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (bSeries k c) =
      (if d 0 = 0 then (0 : ℚ) else (countLast (d 0 - 1) (d 1) k c : ℚ)) :=
  rfl

-- Finsupp index helpers for `Fin 2`.
private theorem single0_le_iff (d : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) (1 : ℕ) ≤ d ↔ 1 ≤ d 0 := by
  exact Finsupp.single_le_iff

private theorem single1_le_iff (d : Fin 2 →₀ ℕ) :
    Finsupp.single (1 : Fin 2) (1 : ℕ) ≤ d ↔ 1 ≤ d 1 := by
  exact Finsupp.single_le_iff

private theorem add_single_le_iff (d : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) (1 : ℕ) + Finsupp.single (1 : Fin 2) (1 : ℕ) ≤
        d ↔
      1 ≤ d 0 ∧ 1 ≤ d 1 := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    constructor
    · have h0 := h 0
      rw [Finsupp.add_apply, Finsupp.single_eq_same] at h0
      have hne : (1 : Fin 2) ≠ 0 := by decide
      rw [Finsupp.single_eq_of_ne' hne, add_zero] at h0
      exact h0
    · have h1 := h 1
      rw [Finsupp.add_apply] at h1
      have hne : (0 : Fin 2) ≠ 1 := by decide
      rw [Finsupp.single_eq_of_ne' hne, zero_add,
        Finsupp.single_eq_same] at h1
      exact h1
  · intro h i
    obtain ⟨h0, h1⟩ := h
    fin_cases i
    · change (Finsupp.single (0 : Fin 2) (1 : ℕ) +
        Finsupp.single (1 : Fin 2) (1 : ℕ)) 0 ≤ d 0
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      have hne : (1 : Fin 2) ≠ 0 := by decide
      rw [Finsupp.single_eq_of_ne' hne, add_zero]
      exact h0
    · change (Finsupp.single (0 : Fin 2) (1 : ℕ) +
        Finsupp.single (1 : Fin 2) (1 : ℕ)) 1 ≤ d 1
      rw [Finsupp.add_apply]
      have hne : (0 : Fin 2) ≠ 1 := by decide
      rw [Finsupp.single_eq_of_ne' hne, zero_add,
        Finsupp.single_eq_same]
      exact h1

private theorem sub_single0_eval0 (d : Fin 2 →₀ ℕ) :
    (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = d 0 - 1 := by
  rw [Finsupp.tsub_apply, Finsupp.single_eq_same]

private theorem sub_single0_eval1 (d : Fin 2 →₀ ℕ) :
    (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 = d 1 := by
  rw [Finsupp.tsub_apply]
  have hne : (0 : Fin 2) ≠ 1 := by decide
  rw [Finsupp.single_eq_of_ne' hne, Nat.sub_zero]

private theorem sub_single1_eval0 (d : Fin 2 →₀ ℕ) :
    (d - Finsupp.single (1 : Fin 2) (1 : ℕ)) 0 = d 0 := by
  rw [Finsupp.tsub_apply]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  rw [Finsupp.single_eq_of_ne' hne, Nat.sub_zero]

private theorem sub_single1_eval1 (d : Fin 2 →₀ ℕ) :
    (d - Finsupp.single (1 : Fin 2) (1 : ℕ)) 1 = d 1 - 1 := by
  rw [Finsupp.tsub_apply, Finsupp.single_eq_same]

private theorem sub_add_single_eval0 (d : Fin 2 →₀ ℕ) :
    (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
      Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = d 0 - 1 := by
  rw [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  rw [Finsupp.single_eq_of_ne' hne, add_zero]

private theorem sub_add_single_eval1 (d : Fin 2 →₀ ℕ) :
    (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
      Finsupp.single (1 : Fin 2) (1 : ℕ))) 1 = d 1 - 1 := by
  rw [Finsupp.tsub_apply, Finsupp.add_apply]
  have hne : (0 : Fin 2) ≠ 1 := by decide
  rw [Finsupp.single_eq_of_ne' hne, zero_add, Finsupp.single_eq_same]

-- Monomial coefficient helpers.
private theorem coeff_X0_mul (d : Fin 2 →₀ ℕ) (φ : MvPowerSeries (Fin 2) ℚ) :
    MvPowerSeries.coeff d (MvPowerSeries.X 0 * φ) =
      (if 1 ≤ d 0
        then MvPowerSeries.coeff (d - Finsupp.single 0 (1 : ℕ)) φ
        else 0) := by
  have hX : MvPowerSeries.X (0 : Fin 2) =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) (1 : ℕ))
        (1 : ℚ) := rfl
  rw [hX, MvPowerSeries.coeff_monomial_mul]
  by_cases h : Finsupp.single (0 : Fin 2) (1 : ℕ) ≤ d
  · rw [ite_eq_left h]
    have h1 : 1 ≤ d 0 := (Finsupp.single_le_iff.mp h)
    rw [ite_eq_left h1, one_mul]
  · rw [ite_eq_right h]
    have h1 : ¬ 1 ≤ d 0 := fun hh => h (Finsupp.single_le_iff.mpr hh)
    rw [ite_eq_right h1]

private theorem coeff_X1_mul (d : Fin 2 →₀ ℕ) (φ : MvPowerSeries (Fin 2) ℚ) :
    MvPowerSeries.coeff d (MvPowerSeries.X 1 * φ) =
      (if 1 ≤ d 1
        then MvPowerSeries.coeff (d - Finsupp.single 1 (1 : ℕ)) φ
        else 0) := by
  have hX : MvPowerSeries.X (1 : Fin 2) =
      MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) (1 : ℕ))
        (1 : ℚ) := rfl
  rw [hX, MvPowerSeries.coeff_monomial_mul]
  by_cases h : Finsupp.single (1 : Fin 2) (1 : ℕ) ≤ d
  · rw [ite_eq_left h]
    have h1 : 1 ≤ d 1 := (Finsupp.single_le_iff.mp h)
    rw [ite_eq_left h1, one_mul]
  · rw [ite_eq_right h]
    have h1 : ¬ 1 ≤ d 1 := fun hh => h (Finsupp.single_le_iff.mpr hh)
    rw [ite_eq_right h1]

private theorem X0_mul_X1_eq :
    MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) =
      MvPowerSeries.monomial
        (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))
        (1 : ℚ) := by
  have h0 : MvPowerSeries.X (0 : Fin 2) =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) (1 : ℕ))
        (1 : ℚ) := rfl
  have h1 : MvPowerSeries.X (1 : Fin 2) =
      MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) (1 : ℕ))
        (1 : ℚ) := rfl
  rw [h0, h1, MvPowerSeries.monomial_mul_monomial, mul_one]

private theorem coeff_X0X1_mul (d : Fin 2 →₀ ℕ)
    (φ : MvPowerSeries (Fin 2) ℚ) :
    MvPowerSeries.coeff d
        (MvPowerSeries.X 0 * MvPowerSeries.X 1 * φ) =
      (if 1 ≤ d 0 ∧ 1 ≤ d 1
        then MvPowerSeries.coeff
          (d - (Finsupp.single 0 (1 : ℕ) + Finsupp.single 1 (1 : ℕ))) φ
        else 0) := by
  have hmul : MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) * φ =
      MvPowerSeries.monomial
        (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))
        (1 : ℚ) * φ := by
    rw [X0_mul_X1_eq]
  rw [hmul, MvPowerSeries.coeff_monomial_mul]
  by_cases h :
    Finsupp.single (0 : Fin 2) (1 : ℕ) + Finsupp.single (1 : Fin 2) (1 : ℕ) ≤ d
  · rw [ite_eq_left h]
    have h1 : 1 ≤ d 0 ∧ 1 ≤ d 1 := (add_single_le_iff d).mp h
    rw [ite_eq_left h1, one_mul]
  · rw [ite_eq_right h]
    have h1 : ¬ (1 ≤ d 0 ∧ 1 ≤ d 1) :=
      fun hh => h ((add_single_le_iff d).mpr hh)
    rw [ite_eq_right h1]

-- Step 1 prefix-filter lemmas for the RG condition.
private theorem image_filter_snoc_castSucc (n k : ℕ) (p : Fin n → Fin k)
    (c : Fin k) (j : Fin n) :
    ((Finset.univ.filter fun t : Fin (n + 1) => t < j.castSucc).image
      (Fin.snoc p c)) =
      ((Finset.univ.filter fun t : Fin n => t < j).image p) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hlt : t < Fin.last n := lt_trans ht (Fin.castSucc_lt_last j)
    have hne : t ≠ Fin.last n := ne_of_lt hlt
    obtain ⟨t', rfl⟩ := Fin.exists_castSucc_eq.mpr hne
    have ht' : t' < j := Fin.castSucc_lt_castSucc_iff.mp ht
    exact ⟨t', ht', by rw [Fin.snoc_castSucc]⟩
  · rintro ⟨t', ht', rfl⟩
    refine ⟨t'.castSucc, ?_, by rw [Fin.snoc_castSucc]⟩
    exact Fin.castSucc_lt_castSucc_iff.mpr ht'

private theorem image_filter_snoc_last (n k : ℕ) (p : Fin n → Fin k)
    (c : Fin k) :
    ((Finset.univ.filter fun t : Fin (n + 1) => t < Fin.last n).image
      (Fin.snoc p c)) =
      Finset.univ.image p := by
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hne : t ≠ Fin.last n := ne_of_lt ht
    obtain ⟨t', rfl⟩ := Fin.exists_castSucc_eq.mpr hne
    exact ⟨t', by rw [Fin.snoc_castSucc]⟩
  · rintro ⟨t', rfl⟩
    refine ⟨t'.castSucc, Fin.castSucc_lt_last t', by rw [Fin.snoc_castSucc]⟩

-- Prefix of an RG word is RG.
private theorem rg_init_of_rg_snoc (n k : ℕ) (p : Fin n → Fin k)
    (c : Fin k)
    (h : ∀ i : Fin (n + 1),
      (Fin.snoc (α := fun _ => Fin k) p c i).val ≤
        ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image
          (Fin.snoc (α := fun _ => Fin k) p c)).card)
    (j : Fin n) :
    (p j).val ≤
      ((Finset.univ.filter fun t : Fin n => t < j).image p).card := by
  have hj := h j.castSucc
  rw [Fin.snoc_castSucc] at hj
  rw [image_filter_snoc_castSucc n k p c j] at hj
  exact hj

-- Extending an RG word preserves RG when the new letter is small.
private theorem rg_snoc_of_rg (n k : ℕ) (p : Fin n → Fin k) (c : Fin k)
    (hp : ∀ j : Fin n,
      (p j).val ≤
        ((Finset.univ.filter fun t : Fin n => t < j).image p).card)
    (hc : c.val ≤ (Finset.univ.image p).card) :
    ∀ i : Fin (n + 1),
      (Fin.snoc (α := fun _ => Fin k) p c i).val ≤
        ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image
          (Fin.snoc (α := fun _ => Fin k) p c)).card := by
  intro i
  by_cases hi : i = Fin.last n
  · subst hi
    rw [Fin.snoc_last, image_filter_snoc_last n k p c]
    exact hc
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    rw [Fin.snoc_castSucc, image_filter_snoc_castSucc n k p c j]
    exact hp j

-- Extending a surjective word preserves surjectivity.
private theorem surjective_snoc_of_surjective (n k : ℕ) (p : Fin n → Fin k)
    (c : Fin k) (hp : Function.Surjective p) :
    Function.Surjective (Fin.snoc (α := fun _ => Fin k) p c) := by
  intro b
  obtain ⟨a, ha⟩ := hp b
  exact ⟨a.castSucc, by rw [Fin.snoc_castSucc, ha]⟩

-- Extending a `k`-RGF by any letter gives a `k`-RGF.
private theorem isRGF_snoc_of_isRGF (n k : ℕ) (p : Fin n → Fin k)
    (c : Fin k) (hp : IsRGF n k p) :
    IsRGF (n + 1) k (Fin.snoc (α := fun _ => Fin k) p c) := by
  obtain ⟨hsurj, hrg⟩ := hp
  constructor
  · exact surjective_snoc_of_surjective n k p c hsurj
  · apply rg_snoc_of_rg n k p c hrg
    have himg : Finset.univ.image p = Finset.univ := by
      ext b
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro _
        exact trivial
      · intro _
        obtain ⟨a, ha⟩ := hsurj b
        exact ⟨a, ha⟩
    rw [himg, Finset.card_univ, Fintype.card_fin]
    exact c.isLt.le

-- RG words have all values below the image size.
private theorem rg_image_val_lt_card (k N : ℕ) :
    ∀ (π : Fin N → Fin k),
      (∀ i : Fin N,
        (π i).val ≤
          ((Finset.univ.filter fun j : Fin N => j < i).image π).card) →
      ∀ v : Fin k, v ∈ Finset.univ.image π →
        v.val < (Finset.univ.image π).card := by
  induction N with
  | zero =>
    intro π _ v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨a, _⟩ := hv
    exact Fin.elim0 a
  | succ n ih =>
    intro π h v hv
    set p : Fin n → Fin k := Fin.init π with hp
    set c : Fin k := π (Fin.last n) with hc
    have heq : Fin.snoc (α := fun _ => Fin k) p c = π := by
      rw [hp, hc]
      exact Fin.snoc_init_self _
    have hp_rg : ∀ j : Fin n,
        (p j).val ≤
          ((Finset.univ.filter fun t : Fin n => t < j).image p).card := by
      have h_snoc : ∀ i : Fin (n + 1),
          (Fin.snoc (α := fun _ => Fin k) p c i).val ≤
            ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image
              (Fin.snoc (α := fun _ => Fin k) p c)).card := by
        rw [heq]
        exact h
      exact fun j => rg_init_of_rg_snoc n k p c h_snoc j
    have himg : Finset.univ.image π =
        insert c (Finset.univ.image p) := by
      conv_lhs => rw [← heq]
      exact image_snoc k n p c
    rw [himg] at hv ⊢
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hvS
    · have hc_le : c.val ≤ (Finset.univ.image p).card := by
        have hlast := h (Fin.last n)
        have hfil : ((Finset.univ.filter fun j : Fin (n + 1) =>
            j < Fin.last n).image π) = Finset.univ.image p := by
          conv_lhs => rw [← heq]
          exact image_filter_snoc_last n k p c
        rw [hfil] at hlast
        have hval : (π (Fin.last n)).val = c.val := rfl
        rw [hval] at hlast
        exact hlast
      by_cases hmem : c ∈ Finset.univ.image p
      · have hTeq : insert c (Finset.univ.image p) =
            Finset.univ.image p :=
          Finset.insert_eq_of_mem hmem
        rw [hTeq]
        exact ih p hp_rg c hmem
      · have hcard : (insert c (Finset.univ.image p)).card =
            (Finset.univ.image p).card + 1 :=
          Finset.card_insert_of_notMem hmem
        rw [hcard]
        exact lt_of_le_of_lt hc_le (Nat.lt_succ_self _)
    · have hvlt : v.val < (Finset.univ.image p).card :=
        ih p hp_rg v hvS
      have hle : (Finset.univ.image p).card ≤
          (insert c (Finset.univ.image p)).card := by
        apply Finset.card_le_card
        exact Finset.subset_insert c _
      exact lt_of_lt_of_le hvlt hle

-- Rises base cases.
private theorem risesCount_zero (k : ℕ) (p : Fin 0 → Fin k) :
    risesCount 0 k p = 0 := by
  unfold risesCount
  rw [Finset.filter_false_of_mem]
  · exact Finset.card_empty
  · intro q _ _
    exact Fin.elim0 q.1

private theorem risesCount_one (k : ℕ) (π : Fin 1 → Fin k) :
    risesCount 1 k π = 0 := by
  unfold risesCount
  rw [Finset.filter_false_of_mem]
  · exact Finset.card_empty
  · intro q _
    rintro ⟨hadj, _⟩
    have h1 : q.1.val = 0 := Nat.lt_one_iff.mp q.1.isLt
    have h2 : q.2.val = 0 := Nat.lt_one_iff.mp q.2.isLt
    omega

private theorem castSucc_ne_last' (m : ℕ) (a : Fin (m + 1)) :
    a.castSucc ≠ Fin.last (m + 1) :=
  ne_of_lt (Fin.castSucc_lt_last a)

private theorem pred_last_unique (m : ℕ) (a : Fin (m + 2))
    (h : (Fin.last (m + 1)).val = a.val + 1) :
    a = (Fin.last m).castSucc := by
  have hval : a.val = m := by
    have hlast : (Fin.last (m + 1)).val = m + 1 := Fin.val_last _
    omega
  apply Fin.ext
  change a.val = ((Fin.last m).castSucc).val
  rw [Fin.val_castSucc, Fin.val_last]
  exact hval

private theorem ne_last_of_adj (m : ℕ) (a b : Fin (m + 2))
    (hadj : b.val = a.val + 1) : a ≠ Fin.last (m + 1) := by
  intro ha
  subst ha
  have hlast : (Fin.last (m + 1)).val = m + 1 := Fin.val_last _
  have hbLt : b.val < m + 2 := b.isLt
  omega

-- One-letter extension adds a rise iff the last step goes up.
private theorem risesCount_snoc (m k : ℕ) (p : Fin (m + 1) → Fin k)
    (c : Fin k) :
    risesCount (m + 2) k (Fin.snoc (α := fun _ => Fin k) p c) =
      risesCount (m + 1) k p + (if p (Fin.last m) < c then 1 else 0) := by
  by_cases h : p (Fin.last m) < c
  · let e : Fin (m + 1) × Fin (m + 1) ↪ Fin (m + 2) × Fin (m + 2) :=
      ⟨fun q => (q.1.castSucc, q.2.castSucc), by
        intro q1 q2 hq
        simp only [Prod.mk.injEq] at hq
        obtain ⟨h1, h2⟩ := hq
        have ha : q1.1 = q2.1 := Fin.castSucc_injective _ h1
        have hb : q1.2 = q2.2 := Fin.castSucc_injective _ h2
        exact Prod.ext ha hb⟩
    have hdisj : Disjoint
        ((Finset.univ.filter fun q : Fin (m + 1) × Fin (m + 1) =>
          q.2.val = q.1.val + 1 ∧ p q.1 < p q.2).map e)
        {((Fin.last m).castSucc, Fin.last (m + 1))} := by
      rw [Finset.disjoint_singleton_right]
      intro hmem
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and] at hmem
      obtain ⟨q, _, heq⟩ := hmem
      have h2 : q.2.castSucc = Fin.last (m + 1) := by
        have hpair : (q.1.castSucc, q.2.castSucc) =
            ((Fin.last m).castSucc, Fin.last (m + 1)) := heq
        have hconj : q.1.castSucc = (Fin.last m).castSucc ∧
            q.2.castSucc = Fin.last (m + 1) := by
          simpa only [Prod.mk.injEq] using hpair
        exact hconj.2
      exact castSucc_ne_last' m q.2 h2
    have heq : (Finset.univ.filter fun q : Fin (m + 2) × Fin (m + 2) =>
          q.2.val = q.1.val + 1 ∧
            (Fin.snoc (α := fun _ => Fin k) p c) q.1 <
              (Fin.snoc (α := fun _ => Fin k) p c) q.2) =
        ((Finset.univ.filter fun q : Fin (m + 1) × Fin (m + 1) =>
            q.2.val = q.1.val + 1 ∧ p q.1 < p q.2).map e) ∪
          {((Fin.last m).castSucc, Fin.last (m + 1))} := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, hlt⟩
        by_cases hb : b = Fin.last (m + 1)
        · subst hb
          have ha_eq : a = (Fin.last m).castSucc :=
            pred_last_unique m a hadj
          right
          exact Prod.ext ha_eq rfl
        · have ha_ne : a ≠ Fin.last (m + 1) :=
            ne_last_of_adj m a b hadj
          obtain ⟨a', ha'⟩ := Fin.exists_castSucc_eq.mpr ha_ne
          obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.mpr hb
          left
          refine ⟨(a', b'), ⟨?_, ?_⟩, ?_⟩
          · change b'.val = a'.val + 1
            have ha_val : a'.val = a.val := by
              simpa only [Fin.val_castSucc] using congrArg Fin.val ha'
            have hb_val : b'.val = b.val := by
              simpa only [Fin.val_castSucc] using congrArg Fin.val hb'
            omega
          · change p a' < p b'
            have ha_pi : (Fin.snoc (α := fun _ => Fin k) p c) a = p a' := by
              rw [← ha', Fin.snoc_castSucc]
            have hb_pi : (Fin.snoc (α := fun _ => Fin k) p c) b = p b' := by
              rw [← hb', Fin.snoc_castSucc]
            rw [ha_pi, hb_pi] at hlt
            exact hlt
          · exact Prod.ext ha' hb'
      · rintro (hmem | heq_single)
        · obtain ⟨q, ⟨hadj', hlt'⟩, heq'⟩ := hmem
          have heq_pair : (q.1.castSucc, q.2.castSucc) = (a, b) := heq'
          have hpair : q.1.castSucc = a ∧ q.2.castSucc = b := by
            simpa only [Prod.mk.injEq] using heq_pair
          obtain ⟨ha_eq, hb_eq⟩ := hpair
          constructor
          · have ha_val : q.1.val = a.val := by
              simpa only [Fin.val_castSucc] using congrArg Fin.val ha_eq
            have hb_val : q.2.val = b.val := by
              simpa only [Fin.val_castSucc] using congrArg Fin.val hb_eq
            omega
          · have ha_pi : (Fin.snoc (α := fun _ => Fin k) p c) a = p q.1 := by
              rw [← ha_eq, Fin.snoc_castSucc]
            have hb_pi : (Fin.snoc (α := fun _ => Fin k) p c) b = p q.2 := by
              rw [← hb_eq, Fin.snoc_castSucc]
            rw [ha_pi, hb_pi]
            exact hlt'
        · have hpair : a = (Fin.last m).castSucc ∧
            b = Fin.last (m + 1) := by
            simpa only [Prod.mk.injEq] using heq_single
          obtain ⟨ha_eq, hb_eq⟩ := hpair
          constructor
          · have ha_val : a.val = m := by
              rw [ha_eq, Fin.val_castSucc, Fin.val_last]
            have hb_val : b.val = m + 1 := by
              rw [hb_eq, Fin.val_last]
            omega
          · have ha_pi : (Fin.snoc (α := fun _ => Fin k) p c) a =
                p (Fin.last m) := by
              rw [ha_eq, Fin.snoc_castSucc]
            have hb_pi : (Fin.snoc (α := fun _ => Fin k) p c) b = c := by
              rw [hb_eq, Fin.snoc_last]
            rw [ha_pi, hb_pi]
            exact h
    unfold risesCount
    rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_map,
      Finset.card_singleton, ite_eq_left h]
  · let e : Fin (m + 1) × Fin (m + 1) ↪ Fin (m + 2) × Fin (m + 2) :=
      ⟨fun q => (q.1.castSucc, q.2.castSucc), by
        intro q1 q2 hq
        simp only [Prod.mk.injEq] at hq
        obtain ⟨h1, h2⟩ := hq
        have ha : q1.1 = q2.1 := Fin.castSucc_injective _ h1
        have hb : q1.2 = q2.2 := Fin.castSucc_injective _ h2
        exact Prod.ext ha hb⟩
    have heq : (Finset.univ.filter fun q : Fin (m + 2) × Fin (m + 2) =>
          q.2.val = q.1.val + 1 ∧
            (Fin.snoc (α := fun _ => Fin k) p c) q.1 <
              (Fin.snoc (α := fun _ => Fin k) p c) q.2) =
        ((Finset.univ.filter fun q : Fin (m + 1) × Fin (m + 1) =>
            q.2.val = q.1.val + 1 ∧ p q.1 < p q.2).map e) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map]
      constructor
      · rintro ⟨hadj, hlt⟩
        by_cases hb : b = Fin.last (m + 1)
        · subst hb
          have ha_eq : a = (Fin.last m).castSucc :=
            pred_last_unique m a hadj
          have ha_pi : (Fin.snoc (α := fun _ => Fin k) p c) a =
              p (Fin.last m) := by
            rw [ha_eq, Fin.snoc_castSucc]
          have hb_pi : (Fin.snoc (α := fun _ => Fin k) p c)
              (Fin.last (m + 1)) = c := by
            rw [Fin.snoc_last]
          rw [ha_pi, hb_pi] at hlt
          exact absurd hlt h
        · have ha_ne : a ≠ Fin.last (m + 1) :=
            ne_last_of_adj m a b hadj
          obtain ⟨a', ha'⟩ := Fin.exists_castSucc_eq.mpr ha_ne
          obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.mpr hb
          refine ⟨(a', b'), ⟨?_, ?_⟩, ?_⟩
          · change b'.val = a'.val + 1
            have ha_val : a'.val = a.val := by
              simpa only [Fin.val_castSucc] using congrArg Fin.val ha'
            have hb_val : b'.val = b.val := by
              simpa only [Fin.val_castSucc] using congrArg Fin.val hb'
            omega
          · change p a' < p b'
            have ha_pi : (Fin.snoc (α := fun _ => Fin k) p c) a = p a' := by
              rw [← ha', Fin.snoc_castSucc]
            have hb_pi : (Fin.snoc (α := fun _ => Fin k) p c) b = p b' := by
              rw [← hb', Fin.snoc_castSucc]
            rw [ha_pi, hb_pi] at hlt
            exact hlt
          · exact Prod.ext ha' hb'
      · rintro ⟨q, ⟨hadj', hlt'⟩, heq'⟩
        have heq_pair : (q.1.castSucc, q.2.castSucc) = (a, b) := heq'
        have hpair : q.1.castSucc = a ∧ q.2.castSucc = b := by
          simpa only [Prod.mk.injEq] using heq_pair
        obtain ⟨ha_eq, hb_eq⟩ := hpair
        constructor
        · have ha_val : q.1.val = a.val := by
            simpa only [Fin.val_castSucc] using congrArg Fin.val ha_eq
          have hb_val : q.2.val = b.val := by
            simpa only [Fin.val_castSucc] using congrArg Fin.val hb_eq
          omega
        · have ha_pi : (Fin.snoc (α := fun _ => Fin k) p c) a = p q.1 := by
            rw [← ha_eq, Fin.snoc_castSucc]
          have hb_pi : (Fin.snoc (α := fun _ => Fin k) p c) b = p q.2 := by
            rw [← hb_eq, Fin.snoc_castSucc]
          rw [ha_pi, hb_pi]
          exact hlt'
    unfold risesCount
    rw [heq, Finset.card_map, ite_eq_right h, add_zero]

-- Transport plus top letter always creates a rise.
private theorem risesCount_snoc_castSucc_top (m k : ℕ)
    (p' : Fin (m + 1) → Fin (k + 1)) :
    risesCount (m + 2) (k + 2)
        (Fin.snoc (α := fun _ => Fin (k + 2))
          (Fin.castSucc ∘ p') (Fin.last (k + 1))) =
      risesCount (m + 1) (k + 1) p' + 1 := by
  have hlt : ((Fin.castSucc ∘ p') (Fin.last m) : Fin (k + 2)) <
      Fin.last (k + 1) :=
    Fin.castSucc_lt_last (p' (Fin.last m))
  have hsnoc := risesCount_snoc m (k + 2) (Fin.castSucc ∘ p')
    (Fin.last (k + 1))
  rw [ite_eq_left hlt] at hsnoc
  have hcast : risesCount (m + 1) (k + 2) (Fin.castSucc ∘ p') =
      risesCount (m + 1) (k + 1) p' :=
    rises_castSucc_comp (m + 1) k p'
  rw [hcast] at hsnoc
  exact hsnoc

-- Extending a transported `(k+1)`-RGF by the top letter gives a `(k+2)`-RGF.
private theorem isRGF_snoc_castSucc_top (n k : ℕ)
    (p' : Fin n → Fin (k + 1)) (hp' : IsRGF n (k + 1) p') :
    IsRGF (n + 1) (k + 2)
      (Fin.snoc (α := fun _ => Fin (k + 2))
        (Fin.castSucc ∘ p') (Fin.last (k + 1))) := by
  obtain ⟨hsurj', hrg'⟩ := hp'
  constructor
  · intro b
    by_cases hb : b = Fin.last (k + 1)
    · subst hb
      exact ⟨Fin.last n, by rw [Fin.snoc_last]⟩
    · obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.mpr hb
      obtain ⟨a, ha⟩ := hsurj' b'
      refine ⟨a.castSucc, ?_⟩
      have h1 : (Fin.snoc (α := fun _ => Fin (k + 2))
          (Fin.castSucc ∘ p') (Fin.last (k + 1))) a.castSucc =
          (Fin.castSucc ∘ p') a := Fin.snoc_castSucc _ _ _
      rw [h1, Function.comp_apply, ha]
      exact hb'
  · apply rg_snoc_of_rg n (k + 2) (Fin.castSucc ∘ p')
      (Fin.last (k + 1)) _ _
    · intro i
      exact rg_castSucc_comp n k p' hrg' i
    · have himg : Finset.univ.image (Fin.castSucc ∘ p') =
          (Finset.univ.image p').image Fin.castSucc := by
        rw [Finset.image_image]
      have hsurj_img : Finset.univ.image p' = Finset.univ := by
        ext b
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · intro _
          exact trivial
        · intro _
          obtain ⟨a, ha⟩ := hsurj' b
          exact ⟨a, ha⟩
      rw [himg, hsurj_img, Finset.card_image_of_injective _
        (Fin.castSucc_injective _), Finset.card_univ, Fintype.card_fin,
        Fin.val_last]

-- Prefix of an RGF is an RGF when the last letter already occurs.
private theorem isRGF_init_of_mem (n k : ℕ) (p : Fin n → Fin k) (c : Fin k)
    (hπ : IsRGF (n + 1) k
      (Fin.snoc (α := fun _ => Fin k) p c))
    (hmem : c ∈ Finset.univ.image p) : IsRGF n k p := by
  obtain ⟨hsurj_π, hrg_π⟩ := hπ
  constructor
  · have himg_π : Finset.univ.image
        (Fin.snoc (α := fun _ => Fin k) p c) = Finset.univ := by
      ext b
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro _
        exact trivial
      · intro _
        obtain ⟨a, ha⟩ := hsurj_π b
        exact ⟨a, ha⟩
    have hsnoc := image_snoc k n p c
    rw [himg_π] at hsnoc
    have hins : insert c (Finset.univ.image p) = Finset.univ := hsnoc.symm
    have h_eq : Finset.univ.image p = Finset.univ := by
      have : insert c (Finset.univ.image p) = Finset.univ.image p :=
        Finset.insert_eq_of_mem hmem
      rw [this] at hins
      exact hins
    intro b
    have hb : b ∈ Finset.univ.image p := by
      rw [h_eq]
      exact Finset.mem_univ b
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, ha⟩
  · have h_snoc : ∀ i : Fin (n + 1),
        (Fin.snoc (α := fun _ => Fin k) p c i).val ≤
          ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image
            (Fin.snoc (α := fun _ => Fin k) p c)).card := hrg_π
    exact fun j => rg_init_of_rg_snoc n k p c h_snoc j

-- When the last letter is new, the prefix image has size `k+1`.
private theorem card_image_init_of_not_mem (n k : ℕ)
    (p : Fin n → Fin (k + 2)) (c : Fin (k + 2))
    (hπ : IsRGF (n + 1) (k + 2)
      (Fin.snoc (α := fun _ => Fin (k + 2)) p c))
    (hmem : c ∉ Finset.univ.image p) :
    (Finset.univ.image p).card = k + 1 := by
  obtain ⟨hsurj_π, _⟩ := hπ
  have himg_π : Finset.univ.image
      (Fin.snoc (α := fun _ => Fin (k + 2)) p c) = Finset.univ := by
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro _
      exact trivial
    · intro _
      obtain ⟨a, ha⟩ := hsurj_π b
      exact ⟨a, ha⟩
  have hsnoc := image_snoc (k + 2) n p c
  rw [himg_π] at hsnoc
  have hcard : (insert c (Finset.univ.image p)).card = k + 2 := by
    rw [← hsnoc, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_insert_of_notMem hmem] at hcard
  omega

-- Prefix image with size `k+1` is exactly the `castSucc` image.
private theorem image_init_eq_castSucc_image (n k : ℕ)
    (p : Fin n → Fin (k + 2))
    (hrg : ∀ i : Fin n,
      (p i).val ≤
        ((Finset.univ.filter fun j : Fin n => j < i).image p).card)
    (hcard : (Finset.univ.image p).card = k + 1) :
    Finset.univ.image p =
      Finset.univ.image (Fin.castSucc : Fin (k + 1) → Fin (k + 2)) := by
  have hlt : ∀ v : Fin (k + 2), v ∈ Finset.univ.image p → v.val < k + 1 := by
    intro v hv
    have hvlt := rg_image_val_lt_card (k + 2) n p hrg v hv
    rw [hcard] at hvlt
    exact hvlt
  have hsub : Finset.univ.image p ⊆
      Finset.univ.image (Fin.castSucc : Fin (k + 1) → Fin (k + 2)) := by
    intro v hv
    have hvlt := hlt v hv
    let b' : Fin (k + 1) := ⟨v.val, hvlt⟩
    have hb' : (Fin.castSucc b' : Fin (k + 2)) = v := by
      apply Fin.ext
      change (b'.castSucc).val = v.val
      rw [Fin.val_castSucc]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨b', hb'⟩
  have hcardT : (Finset.univ.image
      (Fin.castSucc : Fin (k + 1) → Fin (k + 2))).card = k + 1 := by
    rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _),
      Finset.card_univ, Fintype.card_fin]
  have hle : (Finset.univ.image
      (Fin.castSucc : Fin (k + 1) → Fin (k + 2))).card ≤
      (Finset.univ.image p).card := by
    omega
  exact Finset.eq_of_subset_of_card_le hsub hle

-- New last letter must be the top value, with transported prefix RGF.
private theorem exists_castSucc_of_not_mem (n k : ℕ)
    (p : Fin n → Fin (k + 2)) (c : Fin (k + 2))
    (hπ : IsRGF (n + 1) (k + 2)
      (Fin.snoc (α := fun _ => Fin (k + 2)) p c))
    (hmem : c ∉ Finset.univ.image p) :
    c = Fin.last (k + 1) ∧
      ∃ p' : Fin n → Fin (k + 1),
        p = Fin.castSucc ∘ p' ∧ IsRGF n (k + 1) p' := by
  have hrg_π := hπ.2
  have h_snoc : ∀ i : Fin (n + 1),
      (Fin.snoc (α := fun _ => Fin (k + 2)) p c i).val ≤
        ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image
          (Fin.snoc (α := fun _ => Fin (k + 2)) p c)).card := hrg_π
  have hrg_p : ∀ j : Fin n,
      (p j).val ≤
        ((Finset.univ.filter fun t : Fin n => t < j).image p).card :=
    fun j => rg_init_of_rg_snoc n (k + 2) p c h_snoc j
  have hcard : (Finset.univ.image p).card = k + 1 :=
    card_image_init_of_not_mem n k p c hπ hmem
  have himg_eq : Finset.univ.image p =
      Finset.univ.image (Fin.castSucc : Fin (k + 1) → Fin (k + 2)) :=
    image_init_eq_castSucc_image n k p hrg_p hcard
  have hc_last : c = Fin.last (k + 1) := by
    by_contra hne
    obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.mpr hne
    have hc_mem : c ∈ Finset.univ.image
        (Fin.castSucc : Fin (k + 1) → Fin (k + 2)) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨b', hb'⟩
    rw [← himg_eq] at hc_mem
    exact hmem hc_mem
  refine ⟨hc_last, ?_⟩
  have hval_lt : ∀ j : Fin n, (p j).val < k + 1 := by
    intro j
    have hmem_j : p j ∈ Finset.univ.image p := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    have hvlt := rg_image_val_lt_card (k + 2) n p hrg_p (p j) hmem_j
    rw [hcard] at hvlt
    exact hvlt
  let p' : Fin n → Fin (k + 1) := fun j => ⟨(p j).val, hval_lt j⟩
  have hp_eq : p = Fin.castSucc ∘ p' := by
    funext j
    apply Fin.ext
    change (p j).val = ((Fin.castSucc ∘ p') j).val
    rw [Function.comp_apply, Fin.val_castSucc]
  refine ⟨p', hp_eq, ?_, ?_⟩
  · intro b'
    have hmem_cast : (Fin.castSucc b' : Fin (k + 2)) ∈
        Finset.univ.image p := by
      have hmem_univ : (Fin.castSucc b' : Fin (k + 2)) ∈
          insert c (Finset.univ.image p) := by
        have himg_π : Finset.univ.image
            (Fin.snoc (α := fun _ => Fin (k + 2)) p c) = Finset.univ := by
          ext b
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · intro _
            exact trivial
          · intro _
            obtain ⟨a, ha⟩ := hπ.1 b
            exact ⟨a, ha⟩
        have hsnoc := image_snoc (k + 2) n p c
        rw [himg_π] at hsnoc
        have : (Fin.castSucc b' : Fin (k + 2)) ∈ Finset.univ :=
          Finset.mem_univ _
        rw [hsnoc] at this
        -- `hsnoc : univ = insert c (image p)`, so `this` becomes membership.
        -- Rewrite direction: `univ = insert`, so `mem univ` becomes `mem insert`.
        exact this
      have hne : (Fin.castSucc b' : Fin (k + 2)) ≠ c := by
        rw [hc_last]
        exact castSucc_ne_last' k b'
      simp only [Finset.mem_insert] at hmem_univ
      rcases hmem_univ with h_eq | h_mem
      · exact absurd h_eq hne
      · exact h_mem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem_cast
    obtain ⟨a, ha⟩ := hmem_cast
    have ha' : (Fin.castSucc (p' a) : Fin (k + 2)) =
        Fin.castSucc b' := by
      have hpa : p a = Fin.castSucc (p' a) := congrFun hp_eq a
      rw [hpa] at ha
      exact ha
    have hinj := Fin.castSucc_injective (k + 1) ha'
    exact ⟨a, hinj⟩
  · intro j
    have hj := hrg_p j
    have hval_eq : (p' j).val = (p j).val := rfl
    rw [hval_eq]
    have himg : (Finset.univ.filter fun t : Fin n => t < j).image p =
        (((Finset.univ.filter fun t : Fin n => t < j).image p').image
          Fin.castSucc) := by
      conv_lhs => rw [hp_eq]
      rw [Finset.image_image]
    have hcard_eq : ((Finset.univ.filter fun t : Fin n => t < j).image p).card =
        ((Finset.univ.filter fun t : Fin n => t < j).image p').card := by
      rw [himg, Finset.card_image_of_injective _
        (Fin.castSucc_injective _)]
    rw [← hcard_eq]
    exact hj

-- No RGFs when length is below block count.
private theorem countRGF_eq_zero_of_lt (N r k : ℕ) (hlt : N < k) :
    countRGF N r k = 0 := by
  unfold countRGF
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun a => ?_⟩
  obtain ⟨π, hsurj, _, _⟩ := a
  have hle : Fintype.card (Fin k) ≤ Fintype.card (Fin N) :=
    Fintype.card_le_of_surjective π hsurj
  rw [Fintype.card_fin, Fintype.card_fin] at hle
  omega

private theorem countRGF_zero_eq_zero (r k : ℕ) (hk : 1 ≤ k) :
    countRGF 0 r k = 0 := by
  apply countRGF_eq_zero_of_lt 0 r k
  omega

-- Splitting RGF counts by last letter.
private theorem countRGF_succ_eq_sum (n r k : ℕ) :
    countRGF (n + 1) r k = ∑ c : Fin k, countLast n r k c := by
  unfold countRGF countLast
  have hequiv : {π : Fin (n + 1) → Fin k //
        Function.Surjective π ∧
          (∀ i : Fin (n + 1),
            (π i).val ≤
              ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image π).card) ∧
          risesCount (n + 1) k π = r} ≃
      (Σ c : Fin k, {π : Fin (n + 1) → Fin k //
        Function.Surjective π ∧
          (∀ i : Fin (n + 1),
            (π i).val ≤
              ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image π).card) ∧
          risesCount (n + 1) k π = r ∧ π (Fin.last n) = c}) := by
    refine
      { toFun := fun π => ⟨π.1 (Fin.last n), π.1, π.2.1, π.2.2.1, π.2.2.2, rfl⟩
        invFun := fun s => ⟨s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1⟩
        left_inv := fun π => by
          obtain ⟨π, h1, h2, h3⟩ := π
          rfl
        right_inv := fun s => by
          obtain ⟨c, π, h1, h2, h3, hlast⟩ := s
          subst hlast
          rfl }
  rw [Fintype.card_congr hequiv, Fintype.card_sigma]

-- Converting additive rise conditions to `countLast`.
private theorem card_prefix_eq (m R k : ℕ) (c c' : Fin k) :
    Fintype.card {p : Fin (m + 1) → Fin k //
      Function.Surjective p ∧
        (∀ i : Fin (m + 1),
          (p i).val ≤
            ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p).card) ∧
        risesCount (m + 1) k p + (if c' < c then 1 else 0) = R ∧
          p (Fin.last m) = c'} =
      (if c' < c then
        (if 1 ≤ R then countLast m (R - 1) k c' else 0)
      else countLast m R k c') := by
  by_cases hlt : c' < c
  · simp only [ite_eq_left hlt]
    by_cases hR : 1 ≤ R
    · rw [ite_eq_left hR]
      unfold countLast
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro p
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, h4⟩
        omega
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, h4⟩
        omega
    · rw [ite_eq_right hR]
      have hR0 : R = 0 := by omega
      subst hR0
      rw [Fintype.card_eq_zero_iff]
      refine ⟨?_⟩
      rintro ⟨p, _, _, h3, _⟩
      omega
  · simp only [ite_eq_right hlt]
    unfold countLast
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro p
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, h4⟩
      rw [add_zero] at h3
      exact h3
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, h4⟩
      rw [add_zero]
      exact h3

-- Converting additive rise conditions to `countRGF` for the new-block case.
private theorem card_extra_eq (m R k : ℕ) :
    Fintype.card {p' : Fin (m + 1) → Fin (k + 1) //
      Function.Surjective p' ∧
        (∀ i : Fin (m + 1),
          (p' i).val ≤
            ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p').card) ∧
        risesCount (m + 1) (k + 1) p' + 1 = R} =
      (if 1 ≤ R then countRGF (m + 1) (R - 1) (k + 1) else 0) := by
  by_cases hR : 1 ≤ R
  · rw [ite_eq_left hR]
    unfold countRGF
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro p'
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      omega
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      omega
  · rw [ite_eq_right hR]
    have hR0 : R = 0 := by omega
    subst hR0
    rw [Fintype.card_eq_zero_iff]
    refine ⟨?_⟩
    rintro ⟨p', _, _, h3⟩
    omega

-- Length-one words cannot be `k+2`-RGFs.
private theorem countLast_zero_eq_zero (R k : ℕ) (c : Fin (k + 2)) :
    countLast 0 R (k + 2) c = 0 := by
  unfold countLast
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun a => ?_⟩
  obtain ⟨π, hsurj, _, _, _⟩ := a
  have hle : Fintype.card (Fin (k + 2)) ≤ Fintype.card (Fin 1) :=
    Fintype.card_le_of_surjective π hsurj
  rw [Fintype.card_fin, Fintype.card_fin] at hle
  omega

-- Additive count identity when the last letter is not the top.
private theorem countLast_additive_of_ne_top (m R k : ℕ)
    (c : Fin (k + 2)) (hc : c ≠ Fin.last (k + 1)) :
    countLast (m + 1) R (k + 2) c =
      ∑ c' : Fin (k + 2),
        Fintype.card {p : Fin (m + 1) → Fin (k + 2) //
          Function.Surjective p ∧
            (∀ i : Fin (m + 1),
              (p i).val ≤
                ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p).card) ∧
            risesCount (m + 1) (k + 2) p + (if c' < c then 1 else 0) = R ∧
              p (Fin.last m) = c'} := by
  unfold countLast
  have hequiv : {π : Fin ((m + 1) + 1) → Fin (k + 2) //
        Function.Surjective π ∧
          (∀ i : Fin ((m + 1) + 1),
            (π i).val ≤
              ((Finset.univ.filter fun j : Fin ((m + 1) + 1) => j < i).image π).card) ∧
          risesCount ((m + 1) + 1) (k + 2) π = R ∧
            π (Fin.last (m + 1)) = c} ≃
      (Σ c' : Fin (k + 2), {p : Fin (m + 1) → Fin (k + 2) //
        Function.Surjective p ∧
          (∀ i : Fin (m + 1),
            (p i).val ≤
              ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p).card) ∧
          risesCount (m + 1) (k + 2) p + (if c' < c then 1 else 0) = R ∧
            p (Fin.last m) = c'}) := by
    refine
      { toFun := fun π => by
          obtain ⟨π, hsurj_π, hrg_π, hrise_π, hlast_π⟩ := π
          let p : Fin (m + 1) → Fin (k + 2) := Fin.init π
          have heq : Fin.snoc (α := fun _ => Fin (k + 2)) p c = π := by
            have hinit : Fin.snoc (α := fun _ => Fin (k + 2)) p (π (Fin.last (m + 1))) =
                π := Fin.snoc_init_self _
            rw [hlast_π] at hinit
            exact hinit
          have hπ_snoc : IsRGF ((m + 1) + 1) (k + 2)
              (Fin.snoc (α := fun _ => Fin (k + 2)) p c) := by
            rw [heq]
            exact ⟨hsurj_π, hrg_π⟩
          have hmem : c ∈ Finset.univ.image p := by
            by_cases hmem' : c ∈ Finset.univ.image p
            · exact hmem'
            · exfalso
              have hc_top := (exists_castSucc_of_not_mem (m + 1) k p c hπ_snoc
                hmem').1
              exact hc hc_top
          have hp_rgf : IsRGF (m + 1) (k + 2) p :=
            isRGF_init_of_mem (m + 1) (k + 2) p c hπ_snoc hmem
          have hadd : risesCount (m + 1) (k + 2) p +
              (if p (Fin.last m) < c then 1 else 0) = R := by
            have hsnoc := risesCount_snoc m (k + 2) p c
            have hrise_snoc : risesCount ((m + 1) + 1) (k + 2)
                (Fin.snoc (α := fun _ => Fin (k + 2)) p c) = R := by
              rw [heq]
              exact hrise_π
            have hsnoc' : risesCount ((m + 1) + 1) (k + 2)
                (Fin.snoc (α := fun _ => Fin (k + 2)) p c) =
                risesCount (m + 1) (k + 2) p +
                  (if p (Fin.last m) < c then 1 else 0) := by
              have := hsnoc
              change risesCount (m + 2) _ _ = _ at this
              change risesCount ((m + 1) + 1) _ _ = _
              exact this
            rw [hsnoc'] at hrise_snoc
            exact hrise_snoc
          exact ⟨p (Fin.last m), p, hp_rgf.1, hp_rgf.2, hadd, rfl⟩
        invFun := fun s => by
          obtain ⟨c', p, hsurj_p, hrg_p, hadd, hlast_p⟩ := s
          have hp_rgf : IsRGF (m + 1) (k + 2) p := ⟨hsurj_p, hrg_p⟩
          have hπ_rgf : IsRGF ((m + 1) + 1) (k + 2)
              (Fin.snoc (α := fun _ => Fin (k + 2)) p c) :=
            isRGF_snoc_of_isRGF (m + 1) (k + 2) p c hp_rgf
          have hrise : risesCount ((m + 1) + 1) (k + 2)
              (Fin.snoc (α := fun _ => Fin (k + 2)) p c) = R := by
            have hsnoc := risesCount_snoc m (k + 2) p c
            have hif_eq : (if p (Fin.last m) < c then 1 else 0) =
                (if c' < c then 1 else 0) := by
              rw [hlast_p]
            have hsnoc' : risesCount ((m + 1) + 1) (k + 2)
                (Fin.snoc (α := fun _ => Fin (k + 2)) p c) =
                risesCount (m + 1) (k + 2) p +
                  (if p (Fin.last m) < c then 1 else 0) := by
              have := hsnoc
              change risesCount (m + 2) _ _ = _ at this
              change risesCount ((m + 1) + 1) _ _ = _
              exact this
            rw [hsnoc', hif_eq]
            exact hadd
          have hlast : (Fin.snoc (α := fun _ => Fin (k + 2)) p c)
              (Fin.last (m + 1)) = c := Fin.snoc_last _ _
          exact ⟨_, hπ_rgf.1, hπ_rgf.2, hrise, hlast⟩
        left_inv := fun π => by
          obtain ⟨π, hsurj_π, hrg_π, hrise_π, hlast_π⟩ := π
          apply Subtype.ext
          change Fin.snoc (α := fun _ => Fin (k + 2)) (Fin.init π) c = π
          have hinit : Fin.snoc (α := fun _ => Fin (k + 2)) (Fin.init π)
              (π (Fin.last (m + 1))) = π := Fin.snoc_init_self _
          rw [hlast_π] at hinit
          exact hinit
        right_inv := fun s => by
          obtain ⟨c', p, hsurj_p, hrg_p, hadd, hlast_p⟩ := s
          refine Sigma.subtype_ext ?_ ?_
          · change (Fin.init
                (Fin.snoc (α := fun _ => Fin (k + 2)) p c)) (Fin.last m) = c'
            rw [Fin.init_snoc _ _, hlast_p]
          · change Fin.init
                (Fin.snoc (α := fun _ => Fin (k + 2)) p c) = p
            exact Fin.init_snoc _ _ }
  rw [Fintype.card_congr hequiv, Fintype.card_sigma]

-- Additive count identity for the top last letter (with new-block term).
private theorem countLast_additive_of_eq_top (m R k : ℕ) :
    countLast (m + 1) R (k + 2) (Fin.last (k + 1)) =
      (∑ c' : Fin (k + 2),
        Fintype.card {p : Fin (m + 1) → Fin (k + 2) //
          Function.Surjective p ∧
            (∀ i : Fin (m + 1),
              (p i).val ≤
                ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p).card) ∧
            risesCount (m + 1) (k + 2) p +
              (if c' < Fin.last (k + 1) then 1 else 0) = R ∧
              p (Fin.last m) = c'}) +
        Fintype.card {p' : Fin (m + 1) → Fin (k + 1) //
          Function.Surjective p' ∧
            (∀ i : Fin (m + 1),
              (p' i).val ≤
                ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p').card) ∧
            risesCount (m + 1) (k + 1) p' + 1 = R} := by
  unfold countLast
  have hequiv : {π : Fin ((m + 1) + 1) → Fin (k + 2) //
        Function.Surjective π ∧
          (∀ i : Fin ((m + 1) + 1),
            (π i).val ≤
              ((Finset.univ.filter fun j : Fin ((m + 1) + 1) => j < i).image π).card) ∧
          risesCount ((m + 1) + 1) (k + 2) π = R ∧
            π (Fin.last (m + 1)) = Fin.last (k + 1)} ≃
      ((Σ c' : Fin (k + 2), {p : Fin (m + 1) → Fin (k + 2) //
        Function.Surjective p ∧
          (∀ i : Fin (m + 1),
            (p i).val ≤
              ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p).card) ∧
          risesCount (m + 1) (k + 2) p +
            (if c' < Fin.last (k + 1) then 1 else 0) = R ∧
            p (Fin.last m) = c'}) ⊕
        {p' : Fin (m + 1) → Fin (k + 1) //
          Function.Surjective p' ∧
            (∀ i : Fin (m + 1),
              (p' i).val ≤
                ((Finset.univ.filter fun j : Fin (m + 1) => j < i).image p').card) ∧
            risesCount (m + 1) (k + 1) p' + 1 = R}) := by
    refine
      { toFun := fun π =>
          if hmem' : Fin.last (k + 1) ∈
              Finset.univ.image (Fin.init π.1) then
            Sum.inl ⟨(Fin.init π.1) (Fin.last m), Fin.init π.1,
              by
                have hlast : π.1 (Fin.last (m + 1)) = Fin.last (k + 1) :=
                  π.2.2.2.2
                have hself := Fin.snoc_init_self π.1
                have heq : Fin.snoc (α := fun _ => Fin (k + 2))
                    (Fin.init π.1) (Fin.last (k + 1)) = π.1 := by
                  rw [hlast] at hself
                  exact hself
                have hπ : IsRGF ((m + 1) + 1) (k + 2)
                    (Fin.snoc (α := fun _ => Fin (k + 2))
                      (Fin.init π.1) (Fin.last (k + 1))) := by
                  rw [heq]
                  exact ⟨π.2.1, π.2.2.1⟩
                exact
                  (isRGF_init_of_mem (m + 1) (k + 2) (Fin.init π.1)
                    (Fin.last (k + 1)) hπ hmem').1,
              by
                have hlast : π.1 (Fin.last (m + 1)) = Fin.last (k + 1) :=
                  π.2.2.2.2
                have hself := Fin.snoc_init_self π.1
                have heq : Fin.snoc (α := fun _ => Fin (k + 2))
                    (Fin.init π.1) (Fin.last (k + 1)) = π.1 := by
                  rw [hlast] at hself
                  exact hself
                have hπ : IsRGF ((m + 1) + 1) (k + 2)
                    (Fin.snoc (α := fun _ => Fin (k + 2))
                      (Fin.init π.1) (Fin.last (k + 1))) := by
                  rw [heq]
                  exact ⟨π.2.1, π.2.2.1⟩
                exact
                  (isRGF_init_of_mem (m + 1) (k + 2) (Fin.init π.1)
                    (Fin.last (k + 1)) hπ hmem').2,
              by
                have hlast : π.1 (Fin.last (m + 1)) = Fin.last (k + 1) :=
                  π.2.2.2.2
                have hself := Fin.snoc_init_self π.1
                have heq : Fin.snoc (α := fun _ => Fin (k + 2))
                    (Fin.init π.1) (Fin.last (k + 1)) = π.1 := by
                  rw [hlast] at hself
                  exact hself
                have hrises_π := π.2.2.2.1
                have hsnoc := risesCount_snoc m (k + 2) (Fin.init π.1)
                  (Fin.last (k + 1))
                have hrewrite : risesCount ((m + 1) + 1) (k + 2)
                    (Fin.snoc (α := fun _ => Fin (k + 2))
                      (Fin.init π.1) (Fin.last (k + 1))) = R := by
                  rw [heq]
                  exact hrises_π
                rw [hsnoc] at hrewrite
                exact hrewrite,
              rfl⟩
          else
            Sum.inr
              (by
                have hlast : π.1 (Fin.last (m + 1)) = Fin.last (k + 1) :=
                  π.2.2.2.2
                have hself := Fin.snoc_init_self π.1
                have heq : Fin.snoc (α := fun _ => Fin (k + 2))
                    (Fin.init π.1) (Fin.last (k + 1)) = π.1 := by
                  rw [hlast] at hself
                  exact hself
                have hπ : IsRGF ((m + 1) + 1) (k + 2)
                    (Fin.snoc (α := fun _ => Fin (k + 2))
                      (Fin.init π.1) (Fin.last (k + 1))) := by
                  rw [heq]
                  exact ⟨π.2.1, π.2.2.1⟩
                have hexists : ∃ p' : Fin (m + 1) → Fin (k + 1),
                    Fin.init π.1 = Fin.castSucc ∘ p' ∧
                      IsRGF (m + 1) (k + 1) p' :=
                  (exists_castSucc_of_not_mem (m + 1) k (Fin.init π.1)
                    (Fin.last (k + 1)) hπ hmem').2
                have hspec := Classical.choose_spec hexists
                have hp_eq : Fin.init π.1 =
                    Fin.castSucc ∘ Classical.choose hexists := hspec.1
                have hp_rgf : IsRGF (m + 1) (k + 1)
                    (Classical.choose hexists) := hspec.2
                have hrises_π := π.2.2.2.1
                have hsnoc_top := risesCount_snoc_castSucc_top m k
                  (Classical.choose hexists)
                have heq' : Fin.snoc (α := fun _ => Fin (k + 2))
                    (Fin.castSucc ∘ Classical.choose hexists)
                    (Fin.last (k + 1)) = π.1 := by
                  rw [← hp_eq, heq]
                have hrewrite : risesCount ((m + 1) + 1) (k + 2)
                    (Fin.snoc (α := fun _ => Fin (k + 2))
                      (Fin.castSucc ∘ Classical.choose hexists)
                      (Fin.last (k + 1))) = R := by
                  rw [heq']
                  exact hrises_π
                rw [hsnoc_top] at hrewrite
                exact ⟨Classical.choose hexists, hp_rgf.1, hp_rgf.2,
                  hrewrite⟩)
        invFun := fun s => match s with
          | Sum.inl s_sigma => ⟨Fin.snoc (α := fun _ => Fin (k + 2)) s_sigma.2.1
            (Fin.last (k + 1)),
            by
              exact
                (isRGF_snoc_of_isRGF (m + 1) (k + 2) s_sigma.2.1
                  (Fin.last (k + 1))
                  ⟨s_sigma.2.2.1, s_sigma.2.2.2.1⟩).1,
            by
              exact
                (isRGF_snoc_of_isRGF (m + 1) (k + 2) s_sigma.2.1
                  (Fin.last (k + 1))
                  ⟨s_sigma.2.2.1, s_sigma.2.2.2.1⟩).2,
            by
              have hsnoc := risesCount_snoc m (k + 2) s_sigma.2.1
                (Fin.last (k + 1))
              have hRises_p := s_sigma.2.2.2.2.1
              have hLast_p := s_sigma.2.2.2.2.2
              rw [hsnoc, hLast_p]
              exact hRises_p,
            by exact Fin.snoc_last _ _⟩
          | Sum.inr s_extra => ⟨Fin.snoc (α := fun _ => Fin (k + 2))
            (Fin.castSucc ∘ s_extra.1) (Fin.last (k + 1)),
            by
              exact
                (isRGF_snoc_castSucc_top (m + 1) k s_extra.1
                  ⟨s_extra.2.1, s_extra.2.2.1⟩).1,
            by
              exact
                (isRGF_snoc_castSucc_top (m + 1) k s_extra.1
                  ⟨s_extra.2.1, s_extra.2.2.1⟩).2,
            by
              have hsnoc_top := risesCount_snoc_castSucc_top m k s_extra.1
              have hRises' := s_extra.2.2.2
              rw [hsnoc_top]
              exact hRises',
            by exact Fin.snoc_last _ _⟩
        left_inv := fun π => by
          obtain ⟨π, hsurj_π, hrg_π, hrise_π, hlast_π⟩ := π
          by_cases hmem' : Fin.last (k + 1) ∈
              Finset.univ.image (Fin.init π)
          · have hself := Fin.snoc_init_self π
            have heq : Fin.snoc (α := fun _ => Fin (k + 2))
                (Fin.init π) (Fin.last (k + 1)) = π := by
              rw [hlast_π] at hself
              exact hself
            apply Subtype.ext
            dsimp only
            rw [dite_eq_left hmem']
            dsimp only
            exact heq
          · have hself2 := Fin.snoc_init_self π
            have heq2 : Fin.snoc (α := fun _ => Fin (k + 2))
                (Fin.init π) (Fin.last (k + 1)) = π := by
              rw [hlast_π] at hself2
              exact hself2
            have hπ2 : IsRGF ((m + 1) + 1) (k + 2)
                (Fin.snoc (α := fun _ => Fin (k + 2))
                  (Fin.init π) (Fin.last (k + 1))) := by
              rw [heq2]
              exact ⟨hsurj_π, hrg_π⟩
            have hexists2 : ∃ p' : Fin (m + 1) → Fin (k + 1),
                Fin.init π = Fin.castSucc ∘ p' ∧
                  IsRGF (m + 1) (k + 1) p' :=
              (exists_castSucc_of_not_mem (m + 1) k (Fin.init π)
                (Fin.last (k + 1)) hπ2 hmem').2
            have hspec2 := Classical.choose_spec hexists2
            have hp_eq2 : Fin.init π =
                Fin.castSucc ∘ Classical.choose hexists2 := hspec2.1
            have hgoal_eq : Fin.snoc (α := fun _ => Fin (k + 2))
                (Fin.castSucc ∘ Classical.choose hexists2)
                (Fin.last (k + 1)) = π := by
              rw [← hp_eq2, heq2]
            apply Subtype.ext
            dsimp only
            rw [dite_eq_right hmem']
            dsimp only
            exact hgoal_eq
        right_inv := fun s => by
          cases s with
          | inl s_sigma =>
            have hinit_eq : Fin.init
                (Fin.snoc (α := fun _ => Fin (k + 2)) s_sigma.2.1
                  (Fin.last (k + 1))) = s_sigma.2.1 :=
              Fin.init_snoc _ _
            have hmem_p : Fin.last (k + 1) ∈
                Finset.univ.image s_sigma.2.1 := by
              obtain ⟨a, ha⟩ := s_sigma.2.2.1 (Fin.last (k + 1))
              simp only [Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨a, ha⟩
            have hmem_ours : Fin.last (k + 1) ∈ Finset.univ.image
                (Fin.init (Fin.snoc (α := fun _ => Fin (k + 2))
                  s_sigma.2.1 (Fin.last (k + 1)))) := by
              rw [hinit_eq]
              exact hmem_p
            simp only [dite_eq_left hmem_ours]
            refine congrArg Sum.inl ?_
            refine Sigma.subtype_ext ?_ ?_
            · change (Fin.init
                  (Fin.snoc (α := fun _ => Fin (k + 2)) s_sigma.2.1
                    (Fin.last (k + 1)))) (Fin.last m) = s_sigma.1
              rw [hinit_eq]
              exact s_sigma.2.2.2.2.2
            · change Fin.init
                  (Fin.snoc (α := fun _ => Fin (k + 2)) s_sigma.2.1
                    (Fin.last (k + 1))) = s_sigma.2.1
              exact hinit_eq
          | inr s_extra =>
            have hinit_eq' : Fin.init
                (Fin.snoc (α := fun _ => Fin (k + 2))
                  (Fin.castSucc ∘ s_extra.1) (Fin.last (k + 1))) =
                Fin.castSucc ∘ s_extra.1 := Fin.init_snoc _ _
            have hnotmem : Fin.last (k + 1) ∉ Finset.univ.image
                (Fin.init (Fin.snoc (α := fun _ => Fin (k + 2))
                  (Fin.castSucc ∘ s_extra.1) (Fin.last (k + 1)))) := by
              rw [hinit_eq']
              intro hmem
              simp only [Finset.mem_image, Finset.mem_univ, true_and,
                Function.comp_apply] at hmem
              obtain ⟨a, ha⟩ := hmem
              exact castSucc_ne_last' k (s_extra.1 a) ha
            have hexists_ours : ∃ p'' : Fin (m + 1) → Fin (k + 1),
                Fin.init (Fin.snoc (α := fun _ => Fin (k + 2))
                  (Fin.castSucc ∘ s_extra.1) (Fin.last (k + 1))) =
                  Fin.castSucc ∘ p'' ∧
                  IsRGF (m + 1) (k + 1) p'' :=
              ⟨s_extra.1, by rw [hinit_eq'],
                ⟨s_extra.2.1, s_extra.2.2.1⟩⟩
            have hspec_ours := Classical.choose_spec hexists_ours
            have hp_eq_ours : Fin.init (Fin.snoc (α := fun _ => Fin (k + 2))
                  (Fin.castSucc ∘ s_extra.1) (Fin.last (k + 1))) =
                Fin.castSucc ∘ Classical.choose hexists_ours :=
              hspec_ours.1
            have hcomp_eq : Fin.castSucc ∘ Classical.choose hexists_ours =
                Fin.castSucc ∘ s_extra.1 := by
              rw [← hp_eq_ours, hinit_eq']
            have hchoose_eq : Classical.choose hexists_ours = s_extra.1 := by
              funext j
              have hj := congrFun hcomp_eq j
              simp only [Function.comp_apply] at hj
              exact Fin.castSucc_injective _ hj
            simp only [dite_eq_right hnotmem]
            refine congrArg Sum.inr ?_
            apply Subtype.ext
            exact hchoose_eq }
  rw [Fintype.card_congr hequiv, Fintype.card_sum, Fintype.card_sigma]

-- The total series is the sum of per-last-letter series.
private theorem aSeries_eq_sum_bSeries (k : ℕ) (hk : 1 ≤ k) :
    aSeries k = ∑ c : Fin k, bSeries k c := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_aSeries, map_sum]
  simp only [coeff_bSeries]
  by_cases h0 : d 0 = 0
  · have hL : (countRGF (d 0) (d 1) k : ℚ) = 0 := by
      rw [h0, countRGF_zero_eq_zero _ k hk, Nat.cast_zero]
    have hR : (∑ c : Fin k,
        (if d 0 = 0 then (0 : ℚ) else (countLast (d 0 - 1) (d 1) k c : ℚ))) =
        0 := by
      simp only [h0, ite_true, Finset.sum_const_zero]
    rw [hL, hR]
  · have hpos : 1 ≤ d 0 := Nat.one_le_iff_ne_zero.mpr h0
    obtain ⟨n, hn⟩ : ∃ n, d 0 = n + 1 := ⟨d 0 - 1, by omega⟩
    have hne : ¬ d 0 = 0 := h0
    have hsub : d 0 - 1 = n := by omega
    have hsum : (∑ c : Fin k,
        (if d 0 = 0 then (0 : ℚ) else (countLast (d 0 - 1) (d 1) k c : ℚ))) =
        ∑ c : Fin k, (countLast n (d 1) k c : ℚ) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [ite_eq_right hne, hsub]
    rw [hsum, hn]
    have hNat : countRGF (n + 1) (d 1) k =
        ∑ c : Fin k, countLast n (d 1) k c :=
      countRGF_succ_eq_sum n (d 1) k
    rw [hNat, Nat.cast_sum]

private theorem bSeries_eq_of_ne_top (k : ℕ) (c : Fin (k + 2))
    (hc : c ≠ Fin.last (k + 1)) :
    bSeries (k + 2) c =
      ∑ c' : Fin (k + 2),
        (if c' < c then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else
          MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c') := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_bSeries, map_sum]
  simp only [apply_ite]
  by_cases h0 : d 0 = 0
  · have hL : (if d 0 = 0 then (0 : ℚ)
        else (countLast (d 0 - 1) (d 1) (k + 2) c : ℚ)) = 0 := by
      simp only [h0, ite_true]
    have hle : ¬ 1 ≤ d 0 := by omega
    have hle_and : ¬ (1 ≤ d 0 ∧ 1 ≤ d 1) := fun h => hle h.1
    have hterm : ∀ c' : Fin (k + 2),
        (if c' < c then
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              bSeries (k + 2) c')
        else
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) = 0 := by
      intro c'
      by_cases hlt : c' < c
      · simp only [ite_eq_left hlt, coeff_X0X1_mul, ite_eq_right hle_and]
      · simp only [ite_eq_right hlt, coeff_X0_mul, ite_eq_right hle]
    have hR : (∑ c' : Fin (k + 2),
        (if c' < c then
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              bSeries (k + 2) c')
        else
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) = 0 := by
      rw [← Finset.sum_const_zero]
      apply Finset.sum_congr rfl
      intro c' _
      exact hterm c'
    rw [hL, hR]
  · have hne : ¬ d 0 = 0 := h0
    obtain ⟨n, hn⟩ : ∃ n, d 0 = n + 1 := ⟨d 0 - 1, by omega⟩
    by_cases hn0 : n = 0
    · subst hn0
      have hd1 : d 0 = 1 := by omega
      have hsub : d 0 - 1 = 0 := by omega
      have hL : (if d 0 = 0 then (0 : ℚ)
          else (countLast (d 0 - 1) (d 1) (k + 2) c : ℚ)) = 0 := by
        rw [ite_eq_right hne, hsub, countLast_zero_eq_zero,
          Nat.cast_zero]
      have he0 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = 0 := by
        rw [sub_single0_eval0, hsub]
      have he0' : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = 0 := by
        rw [sub_add_single_eval0, hsub]
      have hterm : ∀ c' : Fin (k + 2),
          (if c' < c then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) = 0 := by
        intro c'
        by_cases hlt : c' < c
        · rw [ite_eq_left hlt, coeff_X0X1_mul]
          by_cases hle : 1 ≤ d 0 ∧ 1 ≤ d 1
          · rw [ite_eq_left hle, coeff_bSeries, he0',
              ite_eq_left rfl]
          · rw [ite_eq_right hle]
        · rw [ite_eq_right hlt, coeff_X0_mul]
          by_cases hle : 1 ≤ d 0
          · rw [ite_eq_left hle, coeff_bSeries, he0,
              ite_eq_left rfl]
          · rw [ite_eq_right hle]
      have hR : (∑ c' : Fin (k + 2),
          (if c' < c then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) = 0 := by
        rw [← Finset.sum_const_zero]
        apply Finset.sum_congr rfl
        intro c' _
        exact hterm c'
      rw [hL, hR]
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hd0 : d 0 = m + 1 + 1 := by omega
      have h1d0 : 1 ≤ d 0 := by omega
      have hsub : d 0 - 1 = m + 1 := by omega
      have hL : (if d 0 = 0 then (0 : ℚ)
          else (countLast (d 0 - 1) (d 1) (k + 2) c : ℚ)) =
          (countLast (m + 1) (d 1) (k + 2) c : ℚ) := by
        rw [ite_eq_right hne, hsub]
      have he0 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = m + 1 := by
        rw [sub_single0_eval0, hsub]
      have he0_ne : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 ≠ 0 := by
        rw [he0]; omega
      have he0_sub : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 - 1 = m := by
        rw [he0]; omega
      have he1 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 = d 1 := sub_single0_eval1 d
      have he0' : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = m + 1 := by
        rw [sub_add_single_eval0, hsub]
      have he0'_ne : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 ≠ 0 := by
        rw [he0']; omega
      have he0'_sub : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 - 1 = m := by
        rw [he0']; omega
      have he1' : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 1 = d 1 - 1 :=
        sub_add_single_eval1 d
      have hterm : ∀ c' : Fin (k + 2),
          (if c' < c then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) =
          (if c' < c then
            (if 1 ≤ d 1 then (countLast m (d 1 - 1) (k + 2) c' : ℚ) else 0)
          else (countLast m (d 1) (k + 2) c' : ℚ)) := by
        intro c'
        by_cases hlt : c' < c
        · rw [ite_eq_left hlt]
          rw [coeff_X0X1_mul]
          by_cases hR : 1 ≤ d 1
          · have hle : 1 ≤ d 0 ∧ 1 ≤ d 1 := ⟨h1d0, hR⟩
            rw [ite_eq_left hle, coeff_bSeries, ite_eq_right he0'_ne, he0'_sub,
              he1']
            rw [ite_eq_left hlt, ite_eq_left hR]
          · have hle : ¬ (1 ≤ d 0 ∧ 1 ≤ d 1) := fun h => hR h.2
            rw [ite_eq_right hle]
            rw [ite_eq_left hlt, ite_eq_right hR]
        · rw [ite_eq_right hlt]
          rw [coeff_X0_mul, ite_eq_left h1d0, coeff_bSeries,
            ite_eq_right he0_ne, he0_sub, he1]
          rw [ite_eq_right hlt]
      have hR : (∑ c' : Fin (k + 2),
          (if c' < c then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) =
          ∑ c' : Fin (k + 2),
            (if c' < c then
              (if 1 ≤ d 1 then (countLast m (d 1 - 1) (k + 2) c' : ℚ) else 0)
            else (countLast m (d 1) (k + 2) c' : ℚ)) := by
        apply Finset.sum_congr rfl
        intro c' _
        exact hterm c'
      have hNat : countLast (m + 1) (d 1) (k + 2) c =
          ∑ c' : Fin (k + 2),
            (if c' < c then
              (if 1 ≤ d 1 then countLast m (d 1 - 1) (k + 2) c' else 0)
            else countLast m (d 1) (k + 2) c') := by
        rw [countLast_additive_of_ne_top m (d 1) k c hc]
        apply Finset.sum_congr rfl
        intro c' _
        rw [card_prefix_eq m (d 1) (k + 2) c c']
      rw [hL, hR, hNat, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro c' _
      by_cases hlt : c' < c
      · rw [ite_eq_left hlt, ite_eq_left hlt]
        by_cases hR : 1 ≤ d 1
        · rw [ite_eq_left hR, ite_eq_left hR]
        · rw [ite_eq_right hR, ite_eq_right hR, Nat.cast_zero]
      · rw [ite_eq_right hlt, ite_eq_right hlt]

private theorem bSeries_eq_of_eq_top (k : ℕ) :
    bSeries (k + 2) (Fin.last (k + 1)) =
      (∑ c' : Fin (k + 2),
        (if c' < Fin.last (k + 1) then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else
          MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1) := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_bSeries, map_add, map_sum]
  simp only [apply_ite]
  by_cases h0 : d 0 = 0
  · have hL : (if d 0 = 0 then (0 : ℚ)
        else (countLast (d 0 - 1) (d 1) (k + 2) (Fin.last (k + 1)) : ℚ)) = 0 := by
      simp only [h0, ite_true]
    have hle : ¬ 1 ≤ d 0 := by omega
    have hle_and : ¬ (1 ≤ d 0 ∧ 1 ≤ d 1) := fun h => hle h.1
    have hterm : ∀ c' : Fin (k + 2),
        (if c' < Fin.last (k + 1) then
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              bSeries (k + 2) c')
        else
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) = 0 := by
      intro c'
      by_cases hlt : c' < Fin.last (k + 1)
      · simp only [ite_eq_left hlt, coeff_X0X1_mul, ite_eq_right hle_and]
      · simp only [ite_eq_right hlt, coeff_X0_mul, ite_eq_right hle]
    have hR : (∑ c' : Fin (k + 2),
        (if c' < Fin.last (k + 1) then
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              bSeries (k + 2) c')
        else
          MvPowerSeries.coeff d
            (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) = 0 := by
      rw [← Finset.sum_const_zero]
      apply Finset.sum_congr rfl
      intro c' _
      exact hterm c'
    have hE : MvPowerSeries.coeff d
        (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1)) = 0 := by
      rw [coeff_X0X1_mul, ite_eq_right hle_and]
    rw [hL, hR, hE, add_zero]
  · have hne : ¬ d 0 = 0 := h0
    obtain ⟨n, hn⟩ : ∃ n, d 0 = n + 1 := ⟨d 0 - 1, by omega⟩
    by_cases hn0 : n = 0
    · subst hn0
      have hsub : d 0 - 1 = 0 := by omega
      have hL : (if d 0 = 0 then (0 : ℚ)
          else (countLast (d 0 - 1) (d 1) (k + 2) (Fin.last (k + 1)) : ℚ)) = 0 := by
        rw [ite_eq_right hne, hsub, countLast_zero_eq_zero, Nat.cast_zero]
      have he0 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = 0 := by
        rw [sub_single0_eval0, hsub]
      have he0' : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = 0 := by
        rw [sub_add_single_eval0, hsub]
      have hterm : ∀ c' : Fin (k + 2),
          (if c' < Fin.last (k + 1) then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) = 0 := by
        intro c'
        by_cases hlt : c' < Fin.last (k + 1)
        · rw [ite_eq_left hlt, coeff_X0X1_mul]
          by_cases hle : 1 ≤ d 0 ∧ 1 ≤ d 1
          · rw [ite_eq_left hle, coeff_bSeries, he0', ite_eq_left rfl]
          · rw [ite_eq_right hle]
        · rw [ite_eq_right hlt, coeff_X0_mul]
          by_cases hle : 1 ≤ d 0
          · rw [ite_eq_left hle, coeff_bSeries, he0, ite_eq_left rfl]
          · rw [ite_eq_right hle]
      have hR : (∑ c' : Fin (k + 2),
          (if c' < Fin.last (k + 1) then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) = 0 := by
        rw [← Finset.sum_const_zero]
        apply Finset.sum_congr rfl
        intro c' _
        exact hterm c'
      have hE : MvPowerSeries.coeff d
          (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            aSeries (k + 1)) = 0 := by
        rw [coeff_X0X1_mul]
        by_cases hle : 1 ≤ d 0 ∧ 1 ≤ d 1
        · rw [ite_eq_left hle, coeff_aSeries]
          have hz : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
              Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = 0 := he0'
          rw [hz, countRGF_zero_eq_zero _ _ (Nat.succ_le_succ (Nat.zero_le k)),
            Nat.cast_zero]
        · rw [ite_eq_right hle]
      rw [hL, hR, hE, add_zero]
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h1d0 : 1 ≤ d 0 := by omega
      have hsub : d 0 - 1 = m + 1 := by omega
      have hL : (if d 0 = 0 then (0 : ℚ)
          else (countLast (d 0 - 1) (d 1) (k + 2) (Fin.last (k + 1)) : ℚ)) =
          (countLast (m + 1) (d 1) (k + 2) (Fin.last (k + 1)) : ℚ) := by
        rw [ite_eq_right hne, hsub]
      have he0 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = m + 1 := by
        rw [sub_single0_eval0, hsub]
      have he0_ne : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 ≠ 0 := by
        rw [he0]; omega
      have he0_sub : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 - 1 = m := by
        rw [he0]; omega
      have he1 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 = d 1 := sub_single0_eval1 d
      have he0' : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = m + 1 := by
        rw [sub_add_single_eval0, hsub]
      have he0'_ne : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 ≠ 0 := by
        rw [he0']; omega
      have he0'_sub : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 - 1 = m := by
        rw [he0']; omega
      have he1' : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
          Finsupp.single (1 : Fin 2) (1 : ℕ))) 1 = d 1 - 1 :=
        sub_add_single_eval1 d
      have hterm : ∀ c' : Fin (k + 2),
          (if c' < Fin.last (k + 1) then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) =
          (if c' < Fin.last (k + 1) then
            (if 1 ≤ d 1 then (countLast m (d 1 - 1) (k + 2) c' : ℚ) else 0)
          else (countLast m (d 1) (k + 2) c' : ℚ)) := by
        intro c'
        by_cases hlt : c' < Fin.last (k + 1)
        · rw [ite_eq_left hlt, coeff_X0X1_mul]
          by_cases hR : 1 ≤ d 1
          · have hle : 1 ≤ d 0 ∧ 1 ≤ d 1 := ⟨h1d0, hR⟩
            rw [ite_eq_left hle, coeff_bSeries, ite_eq_right he0'_ne, he0'_sub,
              he1', ite_eq_left hlt, ite_eq_left hR]
          · have hle : ¬ (1 ≤ d 0 ∧ 1 ≤ d 1) := fun h => hR h.2
            rw [ite_eq_right hle, ite_eq_left hlt, ite_eq_right hR]
        · rw [ite_eq_right hlt, coeff_X0_mul, ite_eq_left h1d0, coeff_bSeries,
            ite_eq_right he0_ne, he0_sub, he1, ite_eq_right hlt]
      have hR : (∑ c' : Fin (k + 2),
          (if c' < Fin.last (k + 1) then
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c')
          else
            MvPowerSeries.coeff d
              (MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) =
          ∑ c' : Fin (k + 2),
            (if c' < Fin.last (k + 1) then
              (if 1 ≤ d 1 then (countLast m (d 1 - 1) (k + 2) c' : ℚ) else 0)
            else (countLast m (d 1) (k + 2) c' : ℚ)) := by
        apply Finset.sum_congr rfl
        intro c' _
        exact hterm c'
      have hE : MvPowerSeries.coeff d
          (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            aSeries (k + 1)) =
          (if 1 ≤ d 1 then (countRGF (m + 1) (d 1 - 1) (k + 1) : ℚ) else 0) := by
        rw [coeff_X0X1_mul]
        by_cases hR : 1 ≤ d 1
        · have hle : 1 ≤ d 0 ∧ 1 ≤ d 1 := ⟨h1d0, hR⟩
          rw [ite_eq_left hle, coeff_aSeries, ite_eq_left hR]
          have hA0 : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
              Finsupp.single (1 : Fin 2) (1 : ℕ))) 0 = m + 1 := he0'
          have hA1 : (d - (Finsupp.single (0 : Fin 2) (1 : ℕ) +
              Finsupp.single (1 : Fin 2) (1 : ℕ))) 1 = d 1 - 1 := he1'
          rw [hA0, hA1]
        · have hle : ¬ (1 ≤ d 0 ∧ 1 ≤ d 1) := fun h => hR h.2
          rw [ite_eq_right hle, ite_eq_right hR]
      have hNat : countLast (m + 1) (d 1) (k + 2) (Fin.last (k + 1)) =
          (∑ c' : Fin (k + 2),
            (if c' < Fin.last (k + 1) then
              (if 1 ≤ d 1 then countLast m (d 1 - 1) (k + 2) c' else 0)
            else countLast m (d 1) (k + 2) c')) +
          (if 1 ≤ d 1 then countRGF (m + 1) (d 1 - 1) (k + 1) else 0) := by
        rw [countLast_additive_of_eq_top m (d 1) k, card_extra_eq m (d 1) k]
        congr 1
        apply Finset.sum_congr rfl
        intro c' _
        rw [card_prefix_eq m (d 1) (k + 2) (Fin.last (k + 1)) c']
      rw [hL, hR, hE, hNat, Nat.cast_add, Nat.cast_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro c' _
        by_cases hlt : c' < Fin.last (k + 1)
        · rw [ite_eq_left hlt, ite_eq_left hlt]
          by_cases hR : 1 ≤ d 1
          · rw [ite_eq_left hR, ite_eq_left hR]
          · rw [ite_eq_right hR, ite_eq_right hR, Nat.cast_zero]
        · rw [ite_eq_right hlt, ite_eq_right hlt]
      · by_cases hR : 1 ≤ d 1
        · rw [ite_eq_left hR, ite_eq_left hR]
        · rw [ite_eq_right hR, ite_eq_right hR, Nat.cast_zero]

private theorem zero_ne_last_succ (k : ℕ) :
    (0 : Fin (k + 2)) ≠ Fin.last (k + 1) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

private theorem not_lt_zero_fin (k : ℕ) (c' : Fin (k + 2)) :
    ¬ c' < (0 : Fin (k + 2)) := by
  intro h
  have hv : c'.val < (0 : Fin (k + 2)).val := Fin.lt_def.mp h
  simp only [Fin.val_zero] at hv
  omega

private theorem bSeries_zero (k : ℕ) :
    bSeries (k + 2) 0 =
      MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) := by
  rw [bSeries_eq_of_ne_top k 0 (zero_ne_last_succ k)]
  have hterm : ∀ c' : Fin (k + 2),
      (if c' < (0 : Fin (k + 2)) then
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) c'
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c') =
      MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c' := by
    intro c'
    rw [ite_eq_right (not_lt_zero_fin k c')]
  calc (∑ c' : Fin (k + 2),
        (if c' < (0 : Fin (k + 2)) then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))
      = ∑ c' : Fin (k + 2),
          MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c' := by
        apply Finset.sum_congr rfl
        intro c' _
        exact hterm c'
    _ = MvPowerSeries.X (0 : Fin 2) * ∑ c' : Fin (k + 2), bSeries (k + 2) c' := by
        rw [Finset.mul_sum]
    _ = MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) := by
        rw [aSeries_eq_sum_bSeries (k + 2) (by omega : 1 ≤ k + 2)]

private theorem sum_diff_aux (k n : ℕ) (c p : Fin (k + 2))
    (hc : c.val = n + 1) (hp : p.val = n) :
    (∑ c' : Fin (k + 2),
        (if c' < c then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) -
      (∑ c' : Fin (k + 2),
        (if c' < p then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) p -
        MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p := by
  have hpc : p < c := Fin.lt_def.mpr (by omega)
  have hFcp : (if p < c then
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        bSeries (k + 2) p
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        bSeries (k + 2) p := ite_eq_left hpc
  have hFpp : (if p < p then
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        bSeries (k + 2) p
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p) =
      MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p :=
    ite_eq_right (lt_irrefl p)
  have hEq : ∀ c' : Fin (k + 2), c' ≠ p →
      (if c' < c then
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) c'
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c') =
      (if c' < p then
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) c'
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c') := by
    intro c' hne
    by_cases h : c' < p
    · have h2 : c' < c := lt_trans h hpc
      rw [ite_eq_left h2, ite_eq_left h]
    · have h2 : ¬ c' < c := by
        intro h2
        have hv1 : c'.val < c.val := Fin.lt_def.mp h2
        have hv2 : ¬ c'.val < p.val := fun hh => h (Fin.lt_def.mpr hh)
        have hval : c'.val = n := by omega
        have hpval : c'.val = p.val := by omega
        exact hne (Fin.ext hpval)
      rw [ite_eq_right h2, ite_eq_right h]
  have hsub : (∑ c' : Fin (k + 2),
        (if c' < c then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) -
      (∑ c' : Fin (k + 2),
        (if c' < p then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) =
      ∑ c' : Fin (k + 2),
        ((if c' < c then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c') -
        (if c' < p then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) := by
    rw [Finset.sum_sub_distrib]
  rw [hsub]
  have hsingle : (∑ c' : Fin (k + 2),
        ((if c' < c then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c') -
        (if c' < p then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) c'
        else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) =
      ((if p < c then
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) p
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p) -
      (if p < p then
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) p
      else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p)) := by
    apply Finset.sum_eq_single p
    · intro c' _ hne
      rw [hEq c' hne, sub_self]
    · intro hmem
      simp at hmem
  rw [hsingle, hFcp, hFpp]

private theorem bSeries_succ_of_ne_top (k n : ℕ) (c p : Fin (k + 2))
    (hc : c.val = n + 1) (hp : p.val = n) (hc_top : c ≠ Fin.last (k + 1)) :
    bSeries (k + 2) c = qSeries * bSeries (k + 2) p := by
  have hplast : p ≠ Fin.last (k + 1) := by
    intro h
    have hv := congrArg Fin.val h
    rw [hp, Fin.val_last] at hv
    have hcval : c.val = k + 1 + 1 := by omega
    have hlt := c.isLt
    omega
  have hBc := bSeries_eq_of_ne_top k c hc_top
  have hBp := bSeries_eq_of_ne_top k p hplast
  have hdiff := sum_diff_aux k n c p hc hp
  have hEq : bSeries (k + 2) c - bSeries (k + 2) p =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) p -
        MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p := by
    conv_lhs => rw [hBc, hBp]
    exact hdiff
  have h1 : bSeries (k + 2) c =
      bSeries (k + 2) p +
        (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) p -
          MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p) := by
    have hsub : bSeries (k + 2) c =
        bSeries (k + 2) p + (bSeries (k + 2) c - bSeries (k + 2) p) := by
      ring
    rw [hEq] at hsub
    exact hsub
  rw [h1]
  unfold qSeries
  ring

private theorem bSeries_top_succ (k : ℕ) (p : Fin (k + 2)) (hp : p.val = k) :
    bSeries (k + 2) (Fin.last (k + 1)) =
      qSeries * bSeries (k + 2) p +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1) := by
  have hlast_val : (Fin.last (k + 1)).val = k + 1 := Fin.val_last _
  have hplast : p ≠ Fin.last (k + 1) := by
    intro h
    have hv := congrArg Fin.val h
    rw [hp, Fin.val_last] at hv
    omega
  have hBc := bSeries_eq_of_eq_top k
  have hBp := bSeries_eq_of_ne_top k p hplast
  have hdiff := sum_diff_aux k k (Fin.last (k + 1)) p hlast_val hp
  have hEq : bSeries (k + 2) (Fin.last (k + 1)) - bSeries (k + 2) p =
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          bSeries (k + 2) p -
        MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p) +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1) := by
    conv_lhs => rw [hBc, hBp]
    have hring : ((∑ c' : Fin (k + 2),
            (if c' < Fin.last (k + 1) then
              MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                bSeries (k + 2) c'
            else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) +
            MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              aSeries (k + 1)) -
            (∑ c' : Fin (k + 2),
              (if c' < p then
                MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                  bSeries (k + 2) c'
              else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) =
          ((∑ c' : Fin (k + 2),
              (if c' < Fin.last (k + 1) then
                MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                  bSeries (k + 2) c'
              else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c')) -
            (∑ c' : Fin (k + 2),
              (if c' < p then
                MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
                  bSeries (k + 2) c'
              else MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) c'))) +
            MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              aSeries (k + 1) := by
      ring
    rw [hring, hdiff]
  have h1 : bSeries (k + 2) (Fin.last (k + 1)) =
      bSeries (k + 2) p +
        (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            bSeries (k + 2) p -
          MvPowerSeries.X (0 : Fin 2) * bSeries (k + 2) p) +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1) := by
    have hsub : bSeries (k + 2) (Fin.last (k + 1)) =
        bSeries (k + 2) p +
          (bSeries (k + 2) (Fin.last (k + 1)) - bSeries (k + 2) p) := by
      ring
    rw [hEq] at hsub
    rw [hsub]
    ring
  rw [h1]
  unfold qSeries
  ring

private theorem bSeries_closed_le (k n : ℕ) (hle : n ≤ k) (h : n < k + 2) :
    bSeries (k + 2) ⟨n, h⟩ =
      qSeries ^ n * MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) := by
  induction n with
  | zero =>
    have h0 : (⟨0, h⟩ : Fin (k + 2)) = 0 := Fin.mk_zero
    rw [h0, bSeries_zero k, pow_zero, one_mul]
  | succ m ih =>
    have hm_le : m ≤ k := by omega
    have hm_lt : m < k + 2 := by omega
    have htop : (⟨m + 1, h⟩ : Fin (k + 2)) ≠ Fin.last (k + 1) := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_last] at hv
      omega
    have hsucc := bSeries_succ_of_ne_top k m ⟨m + 1, h⟩ ⟨m, hm_lt⟩ rfl rfl htop
    rw [hsucc, ih hm_le hm_lt, pow_succ']
    ring

private theorem bSeries_top_closed (k : ℕ) :
    bSeries (k + 2) (Fin.last (k + 1)) =
      qSeries ^ (k + 1) * MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1) := by
  have hm_lt : k < k + 2 := by omega
  have htop := bSeries_top_succ k ⟨k, hm_lt⟩ rfl
  have hclosed := bSeries_closed_le k k (le_refl k) hm_lt
  rw [htop, hclosed, pow_succ']
  ring

private theorem aSeries_sum_closed (k : ℕ) :
    aSeries (k + 2) =
      (∑ i ∈ Finset.range (k + 2), qSeries ^ i) *
          MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          aSeries (k + 1) := by
  have hsum := aSeries_eq_sum_bSeries (k + 2) (by omega : 1 ≤ k + 2)
  have hpoint : ∀ c : Fin (k + 2),
      bSeries (k + 2) c =
        qSeries ^ c.val * MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) +
          (if c = Fin.last (k + 1) then
            MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
              aSeries (k + 1)
          else 0) := by
    intro c
    by_cases hc_top : c = Fin.last (k + 1)
    · subst hc_top
      rw [bSeries_top_closed k, ite_eq_left rfl]
      have hval : (Fin.last (k + 1)).val = k + 1 := Fin.val_last _
      rw [hval]
    · have hval_ne : c.val ≠ k + 1 := by
        intro heq
        apply hc_top
        apply Fin.ext
        rw [heq]
        exact (Fin.val_last _).symm
      have hle : c.val ≤ k := by
        have hlt := c.isLt
        omega
      have hclosed := bSeries_closed_le k c.val hle c.isLt
      have heta : (⟨c.val, c.isLt⟩ : Fin (k + 2)) = c := Fin.eta _ _
      rw [heta] at hclosed
      rw [hclosed, ite_eq_right hc_top, add_zero]
  conv_lhs => rw [hsum]
  have hsplit : (∑ c : Fin (k + 2), bSeries (k + 2) c) =
      (∑ c : Fin (k + 2),
        qSeries ^ c.val * MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2)) +
      (∑ c : Fin (k + 2),
        (if c = Fin.last (k + 1) then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            aSeries (k + 1)
        else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    exact hpoint c
  rw [hsplit]
  have hextra : (∑ c : Fin (k + 2),
        (if c = Fin.last (k + 1) then
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            aSeries (k + 1)
        else 0)) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        aSeries (k + 1) := by
    rw [Finset.sum_ite_eq']
    simp
  have hgeom_sum : (∑ c : Fin (k + 2),
        qSeries ^ c.val * MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2)) =
      (∑ i ∈ Finset.range (k + 2), qSeries ^ i) *
        MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) := by
    have h1 : (∑ c : Fin (k + 2),
          qSeries ^ c.val * MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2)) =
        (∑ c : Fin (k + 2), qSeries ^ c.val) *
          (MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring
    have h2 : (∑ c : Fin (k + 2), qSeries ^ c.val) =
        ∑ i ∈ Finset.range (k + 2), qSeries ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun i => qSeries ^ i) (k + 2)]
    rw [h1, h2]
    ring
  rw [hextra, hgeom_sum]

private theorem aSeries_recurrence_succ (k : ℕ) :
    aSeries (k + 2) * (qSeries ^ (k + 2) - MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        (1 - MvPowerSeries.X (1 : Fin 2)) * aSeries (k + 1) := by
  have hA := aSeries_sum_closed k
  have hgeom : (1 - qSeries) * (∑ i ∈ Finset.range (k + 2), qSeries ^ i) =
      1 - qSeries ^ (k + 2) :=
    mul_neg_geom_sum qSeries (k + 2)
  have hq : MvPowerSeries.X (0 : Fin 2) * (1 - MvPowerSeries.X (1 : Fin 2)) =
      1 - qSeries := by
    unfold qSeries
    ring
  have hA' : aSeries (k + 2) * (1 - MvPowerSeries.X (1 : Fin 2)) =
      aSeries (k + 2) * (1 - qSeries ^ (k + 2)) +
        MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          (1 - MvPowerSeries.X (1 : Fin 2)) * aSeries (k + 1) := by
    conv_lhs => rw [hA]
    have hcalc : ((∑ i ∈ Finset.range (k + 2), qSeries ^ i) *
            MvPowerSeries.X (0 : Fin 2) * aSeries (k + 2) +
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            aSeries (k + 1)) *
          (1 - MvPowerSeries.X (1 : Fin 2)) =
        (∑ i ∈ Finset.range (k + 2), qSeries ^ i) *
            (MvPowerSeries.X (0 : Fin 2) * (1 - MvPowerSeries.X (1 : Fin 2))) *
            aSeries (k + 2) +
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
            (1 - MvPowerSeries.X (1 : Fin 2)) * aSeries (k + 1) := by
      ring
    rw [hcalc, hq]
    have hmid : (∑ i ∈ Finset.range (k + 2), qSeries ^ i) * (1 - qSeries) *
          aSeries (k + 2) =
        aSeries (k + 2) * ((1 - qSeries) *
          (∑ i ∈ Finset.range (k + 2), qSeries ^ i)) := by
      ring
    rw [hmid, hgeom]
  calc aSeries (k + 2) * (qSeries ^ (k + 2) - MvPowerSeries.X (1 : Fin 2))
      = aSeries (k + 2) * (1 - MvPowerSeries.X (1 : Fin 2)) -
          aSeries (k + 2) * (1 - qSeries ^ (k + 2)) := by
        ring
    _ = MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
          (1 - MvPowerSeries.X (1 : Fin 2)) * aSeries (k + 1) := by
        rw [hA']
        ring

private theorem aSeries_recurrence (k : ℕ) (hk : 2 ≤ k) :
    aSeries k * (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) *
        (1 - MvPowerSeries.X (1 : Fin 2)) * aSeries (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  exact aSeries_recurrence_succ m

private theorem countRGF_k1 (N r : ℕ) :
    countRGF N r 1 = (if 1 ≤ N ∧ r = 0 then 1 else 0) := by
  have h := card_k1 N r
  unfold countRGF risesCount at *
  exact h

private theorem eq_single0_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single (0 : Fin 2) (1 : ℕ) ↔ d 0 = 1 ∧ d 1 = 0 := by
  constructor
  · intro h
    rw [h]
    constructor
    · exact Finsupp.single_eq_same
    · have hne : (0 : Fin 2) ≠ 1 := by decide
      exact Finsupp.single_eq_of_ne' hne
  · intro h
    obtain ⟨h0, h1⟩ := h
    apply Finsupp.ext_iff.mpr
    intro i
    fin_cases i
    · change d 0 = Finsupp.single (0 : Fin 2) (1 : ℕ) 0
      rw [h0]
      exact (Finsupp.single_eq_same).symm
    · change d 1 = Finsupp.single (0 : Fin 2) (1 : ℕ) 1
      rw [h1]
      have hne : (0 : Fin 2) ≠ 1 := by decide
      exact (Finsupp.single_eq_of_ne' hne).symm

private theorem aSeries_one_mul :
    aSeries 1 * (1 - MvPowerSeries.X (0 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) := by
  apply MvPowerSeries.ext
  intro d
  have hmul : aSeries 1 * (1 - MvPowerSeries.X (0 : Fin 2)) =
      aSeries 1 - MvPowerSeries.X (0 : Fin 2) * aSeries 1 := by
    ring
  rw [hmul, map_sub, MvPowerSeries.coeff_X, coeff_aSeries, coeff_X0_mul]
  have hiff := eq_single0_iff d
  by_cases h1 : d 1 = 0
  · by_cases h0 : d 0 = 0
    · have hA : (countRGF (d 0) (d 1) 1 : ℚ) = 0 := by
        rw [countRGF_k1]
        have hneg : ¬ (1 ≤ d 0 ∧ d 1 = 0) := by omega
        rw [ite_eq_right hneg, Nat.cast_zero]
      have hXA : (if 1 ≤ d 0 then
          MvPowerSeries.coeff (d - Finsupp.single (0 : Fin 2) (1 : ℕ))
            (aSeries 1) else (0 : ℚ)) = 0 := by
        have hle : ¬ 1 ≤ d 0 := by omega
        rw [ite_eq_right hle]
      rw [hA, hXA, sub_zero]
      have hne : ¬ d = Finsupp.single (0 : Fin 2) (1 : ℕ) := by
        intro heq
        have hcon := hiff.mp heq
        omega
      rw [ite_eq_right hne]
    · by_cases h0' : d 0 = 1
      · have hA : (countRGF (d 0) (d 1) 1 : ℚ) = 1 := by
          rw [countRGF_k1]
          have hpos : 1 ≤ d 0 ∧ d 1 = 0 := by omega
          rw [ite_eq_left hpos, Nat.cast_one]
        have hsub0 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = 0 := by
          rw [sub_single0_eval0]
          omega
        have hsub1 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 = 0 := by
          rw [sub_single0_eval1]
          exact h1
        have hXA : (if 1 ≤ d 0 then
            MvPowerSeries.coeff (d - Finsupp.single (0 : Fin 2) (1 : ℕ))
              (aSeries 1) else (0 : ℚ)) = 0 := by
          have hle : 1 ≤ d 0 := by omega
          rw [ite_eq_left hle, coeff_aSeries, hsub0, hsub1, countRGF_k1]
          have hneg : ¬ (1 ≤ (0 : ℕ) ∧ (0 : ℕ) = 0) := by omega
          rw [ite_eq_right hneg, Nat.cast_zero]
        have heq : d = Finsupp.single (0 : Fin 2) (1 : ℕ) :=
          hiff.mpr ⟨h0', h1⟩
        rw [hA, hXA, sub_zero, ite_eq_left heq]
      · have hA : (countRGF (d 0) (d 1) 1 : ℚ) = 1 := by
          rw [countRGF_k1]
          have hpos : 1 ≤ d 0 ∧ d 1 = 0 := by omega
          rw [ite_eq_left hpos, Nat.cast_one]
        have hle : 1 ≤ d 0 := by omega
        have hsub0 : 1 ≤ (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 := by
          rw [sub_single0_eval0]
          omega
        have hsub1 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 = 0 := by
          rw [sub_single0_eval1]
          exact h1
        have hXA : (if 1 ≤ d 0 then
            MvPowerSeries.coeff (d - Finsupp.single (0 : Fin 2) (1 : ℕ))
              (aSeries 1) else (0 : ℚ)) = 1 := by
          rw [ite_eq_left hle, coeff_aSeries, hsub1, countRGF_k1]
          have hpos : 1 ≤ (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 ∧
              (0 : ℕ) = 0 := ⟨hsub0, rfl⟩
          rw [ite_eq_left hpos, Nat.cast_one]
        have hne : ¬ d = Finsupp.single (0 : Fin 2) (1 : ℕ) := by
          intro heq
          have hcon := hiff.mp heq
          omega
        rw [hA, hXA, ite_eq_right hne, sub_self]
  · have hA : (countRGF (d 0) (d 1) 1 : ℚ) = 0 := by
      rw [countRGF_k1]
      have hneg : ¬ (1 ≤ d 0 ∧ d 1 = 0) := by omega
      rw [ite_eq_right hneg, Nat.cast_zero]
    have hsub1 : (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 ≠ 0 := by
      rw [sub_single0_eval1]
      exact h1
    have hXA : (if 1 ≤ d 0 then
        MvPowerSeries.coeff (d - Finsupp.single (0 : Fin 2) (1 : ℕ))
          (aSeries 1) else (0 : ℚ)) = 0 := by
      by_cases hle : 1 ≤ d 0
      · rw [ite_eq_left hle, coeff_aSeries, countRGF_k1]
        have hneg : ¬ (1 ≤ (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 ∧
            (d - Finsupp.single (0 : Fin 2) (1 : ℕ)) 1 = 0) := by
          intro hcon
          exact hsub1 hcon.2
        rw [ite_eq_right hneg, Nat.cast_zero]
      · rw [ite_eq_right hle]
    have hne : ¬ d = Finsupp.single (0 : Fin 2) (1 : ℕ) := by
      intro heq
      have hcon := hiff.mp heq
      omega
    rw [hA, hXA, ite_eq_right hne, sub_zero]

private theorem dOne_eq : qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2) =
    (1 - MvPowerSeries.X (0 : Fin 2)) * (1 - MvPowerSeries.X (1 : Fin 2)) := by
  unfold qSeries
  rw [pow_one]
  ring

private theorem aSeries_one_base :
    aSeries 1 * (qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) * (1 - MvPowerSeries.X (1 : Fin 2)) := by
  rw [dOne_eq, ← mul_assoc, aSeries_one_mul]

private theorem cancel_D (k : ℕ) (A T : MvPowerSeries (Fin 2) ℚ)
    (hEq : A * (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) =
      T * (qSeries ^ k - MvPowerSeries.X (1 : Fin 2))) :
    A = T := by
  have hD : MvPowerSeries.constantCoeff
      (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) ≠ 0 :=
    dSeries_constCoeff_ne k
  have hcancel : (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) *
      (qSeries ^ k - MvPowerSeries.X (1 : Fin 2))⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ hD
  calc A = A * (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) *
        (qSeries ^ k - MvPowerSeries.X (1 : Fin 2))⁻¹ := by
        rw [mul_assoc, hcancel, mul_one]
    _ = T * (qSeries ^ k - MvPowerSeries.X (1 : Fin 2)) *
        (qSeries ^ k - MvPowerSeries.X (1 : Fin 2))⁻¹ := by
        rw [hEq]
    _ = T := by
        rw [mul_assoc, hcancel, mul_one]

private theorem aSeries_eq_tSeries_aux : ∀ n : ℕ,
    aSeries (n + 1) = tSeries (n + 1) := by
  intro n
  induction n with
  | zero =>
    have hA := aSeries_one_base
    have hT := tSeries_base
    have hEq : aSeries 1 * (qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2)) =
        tSeries 1 * (qSeries ^ 1 - MvPowerSeries.X (1 : Fin 2)) := by
      rw [hA, hT]
    exact cancel_D 1 (aSeries 1) (tSeries 1) hEq
  | succ m ih =>
    have hk : 2 ≤ m + 1 + 1 := by omega
    have hA := aSeries_recurrence (m + 1 + 1) hk
    have hT := tSeries_recurrence (m + 1 + 1) hk
    have hsub : m + 1 + 1 - 1 = m + 1 := by omega
    rw [hsub] at hA hT
    rw [ih] at hA
    have hEq : aSeries (m + 1 + 1) *
          (qSeries ^ (m + 1 + 1) - MvPowerSeries.X (1 : Fin 2)) =
        tSeries (m + 1 + 1) *
          (qSeries ^ (m + 1 + 1) - MvPowerSeries.X (1 : Fin 2)) := by
      rw [hA, hT]
    exact cancel_D (m + 1 + 1) _ _ hEq

private theorem aSeries_eq_tSeries (k : ℕ) (hk : 1 ≤ k) :
    aSeries k = tSeries k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact aSeries_eq_tSeries_aux n

/--
**Generating function for set partitions by rises.** Fix $k \ge 1$. For $n, r \ge 0$ let
$a_{n,r}$ be the number of words $\pi = \pi_1 \cdots \pi_n$ on the alphabet $\{0, \dots, k-1\}$
that use every letter, satisfy the restricted growth condition that each $\pi_i$ is at most the
number of distinct letters among $\pi_1, \dots, \pi_{i-1}$, and have exactly $r$ rises (the
source's $2$-rises), that is, positions $i < n$ with $\pi_i < \pi_{i+1}$. These words encode the
partitions of $[n]$ into $k$ blocks. Then, in the ring $\mathbb{Q}[[x, y]]$ of formal power
series,
$$\sum_{n, r \ge 0} a_{n,r}\, x^n y^r =
\frac{x^k y^{k-1} (1-y)^k}{\prod_{j=1}^{k} \bigl((1 - x + xy)^j - y\bigr)}.$$

Proves `Wanted` entry `setPartition_twoRise_ordinaryGeneratingFunction`.

Source: Toufik Mansour and Augustine O. Munagi, “Enumeration of Partitions by Long Rises, Levels, and Descents”, Journal of Integer Sequences 12 (2009), Article 09.1.8, Theorem `thrise2`, lines 505-510, <https://cs.uwaterloo.ca/journals/JIS/VOL12/Munagi/munagi15.tex>.
-/
theorem setPartition_twoRise_ordinaryGeneratingFunction
    (k : ℕ) (hk : 1 ≤ k) :
    let x : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 0
    let y : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 1
    ((fun d : Fin 2 →₀ ℕ =>
        (Fintype.card {π : Fin (d 0) → Fin k //
          Function.Surjective π ∧
            (∀ i : Fin (d 0),
              (π i).val ≤
                ((Finset.univ.filter fun j : Fin (d 0) => j < i).image π).card) ∧
            (Finset.univ.filter fun p : Fin (d 0) × Fin (d 0) =>
              p.2.val = p.1.val + 1 ∧ π p.1 < π p.2).card = d 1} : ℚ)) :
      MvPowerSeries (Fin 2) ℚ) =
      x ^ k * y ^ (k - 1) * ((1 : MvPowerSeries (Fin 2) ℚ) - y) ^ k *
        (∏ j ∈ Finset.Icc 1 k,
          (((1 : MvPowerSeries (Fin 2) ℚ) - x + x * y) ^ j - y))⁻¹ := by
  exact aSeries_eq_tSeries k hk

end MetaMathlibExt
end
