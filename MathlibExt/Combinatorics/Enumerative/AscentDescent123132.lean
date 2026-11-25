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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ascents and descents of permutations avoiding 123 and 132

The minimum of an avoider must be last or penultimate: any two entries following it would
form one of the forbidden patterns with it. We insert a new minimum in either position and
track whether the final comparison is an ascent or a descent.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace ascDesGF_123_132

open Equiv.Perm

private abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

private def Avoids {n : ℕ} (σ : Perm n) : Prop :=
  ∀ i j k, i < j → j < k → ¬ (σ i < σ j ∧ σ i < σ k)

private theorem avoids_iff {n : ℕ} (σ : Perm n) :
    Avoids σ ↔ ¬ HasPattern σ (pattern3 ![0, 1, 2]) ∧ ¬ HasPattern σ (pattern3 ![0, 2, 1]) := by
  constructor
  · intro h
    constructor <;> rintro ⟨e, he, hv⟩ <;>
      exact h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide))
        ⟨(hv 0 1).2 (by decide), (hv 0 2).2 (by decide)⟩
  · rintro ⟨h123, h132⟩ i j k hij hjk ⟨hij', hik'⟩
    have he : StrictMono (![i, j, k] : Fin 3 → Fin n) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      fin_cases a <;> assumption
    rcases lt_or_gt_of_ne (σ.injective.ne hjk.ne) with hjk' | hkj'
    · refine h123 ⟨![i, j, k], fun _ _ h => he h, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [pattern3, hij', hik', hjk', hij'.not_gt, hik'.not_gt, hjk'.not_gt]
    · refine h132 ⟨![i, j, k], fun _ _ h => he h, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [pattern3, hij', hik', hkj', hij'.not_gt, hik'.not_gt, hkj'.not_gt]

-- Decompose the inverse permutation at the position of the value zero.
private noncomputable def insertMin {n : ℕ} (i : Fin (n + 2)) (σ : Perm (n + 1)) : Perm (n + 2) :=
  (decomposeFin'Symm i σ.symm).symm

@[simp] private theorem insertMin_self {n : ℕ} (i : Fin (n + 2)) (σ : Perm (n + 1)) :
    insertMin i σ i = 0 := by
  apply (decomposeFin'Symm i σ.symm).symm_apply_eq.mpr
  simp [decomposeFin'Symm_zero]

@[simp] private theorem insertMin_succAbove {n : ℕ} (i : Fin (n + 2)) (σ : Perm (n + 1))
    (j : Fin (n + 1)) : insertMin i σ (i.succAbove j) = (σ j).succ := by
  apply (decomposeFin'Symm i σ.symm).symm_apply_eq.mpr
  simp [decomposeFin'Symm_succ]

private abbrev penult (n : ℕ) : Fin (n + 2) := (Fin.last n).castSucc

private theorem avoids_insertMin {n : ℕ} (i : Fin (n + 2)) (σ : Perm (n + 1)) :
    Avoids (insertMin i σ) ↔ Avoids σ ∧ penult n ≤ i := by
  constructor
  · intro h
    refine ⟨fun a b c hab hbc hr => ?_, le_of_not_gt fun hi => ?_⟩
    · exact h _ _ _ ((Fin.strictMono_succAbove i) hab) ((Fin.strictMono_succAbove i) hbc)
        (by simpa using hr)
    · refine h i (penult n) (Fin.last (n + 1)) hi (Fin.castSucc_lt_last _) ⟨?_, ?_⟩
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi.ne'
        simp [← hj]
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (hi.trans (Fin.castSucc_lt_last _)).ne'
        simp [← hj]
  · rintro ⟨h, hi⟩ a b c hab hbc ⟨hab', hac'⟩
    have ha : a ≠ i := by
      rintro rfl
      simp only [Fin.lt_def, Fin.le_def, penult, Fin.val_castSucc, Fin.val_last] at hi hab hbc
      have := c.isLt
      omega
    have hb : b ≠ i := by
      rintro rfl
      simp at hab'
    have hc : c ≠ i := by
      rintro rfl
      simp at hac'
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hb
    obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hc
    exact h a b c (Fin.succAbove_lt_succAbove_iff.mp hab)
      (Fin.succAbove_lt_succAbove_iff.mp hbc) (by simpa using And.intro hab' hac')

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev P : R := MvPolynomial.X 0
private noncomputable abbrev Q : R := MvPolynomial.X 1

private noncomputable def total {n : ℕ} (f : Perm n → R) : R := by
  classical exact ∑ σ, if Avoids σ then f σ else 0

private theorem total_insertMin {n : ℕ} (f : Perm (n + 2) → R) :
    total f = total (fun σ => f (insertMin (Fin.last _) σ)) +
      total (fun σ => f (insertMin (penult n) σ)) := by
  classical
  let e : Fin (n + 2) × Perm (n + 1) ≃ Perm (n + 2) :=
    (Equiv.prodCongr (Equiv.refl _) (Equiv.symmEquiv _ _)).trans
      (decomposeFin'.symm.trans (Equiv.symmEquiv _ _))
  unfold total
  rw [← e.sum_comp, Fintype.sum_prod_type_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  change (∑ i, if Avoids (insertMin i σ) then f (insertMin i σ) else 0) = _
  simp only [avoids_insertMin]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have h (j : Fin n) : ¬ penult n ≤ j.castSucc.castSucc := by simp [penult]
  simp [h, (Fin.castSucc_lt_last (Fin.last n)).le, add_comm]

private theorem adjacentCount {n : ℕ} (r : Fin (n + 1) → Fin (n + 1) → Prop) [DecidableRel r] :
    (Finset.univ.filter fun i : Fin (n + 1) =>
        ∃ h : i.val + 1 < n + 1, r i ⟨i.val + 1, h⟩).card =
      ∑ i : Fin n, if r i.castSucc i.succ then 1 else 0 := by
  rw [Finset.card_filter, Fin.sum_univ_castSucc]
  simp
  rfl

private noncomputable def edge {n : ℕ} (a b : Fin n) : R := if a < b then P else Q

-- Each edge contributes exactly one of the two variables.
private noncomputable def weight {n : ℕ} (σ : Perm (n + 1)) : R :=
  ∏ j : Fin n, edge (σ j.castSucc) (σ j.succ)

private theorem weight_eq_powers {n : ℕ} (σ : Perm (n + 1)) :
    weight σ = P ^ permAscents σ * Q ^ permDescents σ := by
  rw [permAscents, permDescents, adjacentCount (fun i j => σ i < σ j),
    adjacentCount (fun i j => σ j < σ i), ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases lt_or_gt_of_ne (σ.injective.ne (Fin.castSucc_lt_succ (i := j)).ne) with h | h <;>
    simp [edge, h, h.not_gt]

private def lastAscent {n : ℕ} (σ : Perm (n + 2)) : Prop :=
  σ (penult n) < σ (Fin.last (n + 1))

private instance {n : ℕ} (σ : Perm (n + 2)) : Decidable (lastAscent σ) := by
  unfold lastAscent
  infer_instance

private theorem edge_succ {n : ℕ} (a b : Fin n) : edge a.succ b.succ = edge a b := by
  simp [edge]

private theorem appendMin_weight {n : ℕ} (σ : Perm (n + 2)) :
    weight (insertMin (Fin.last _) σ) = Q * weight σ ∧
      ¬ lastAscent (insertMin (Fin.last _) σ) := by
  have hkeep (j : Fin (n + 2)) :
      insertMin (Fin.last (n + 2)) σ j.castSucc = (σ j).succ := by
    simpa only [Fin.succAbove_last] using insertMin_succAbove (Fin.last (n + 2)) σ j
  refine ⟨?_, by simp [lastAscent]⟩
  unfold weight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.succ_castSucc, Fin.succ_last, hkeep, insertMin_self, edge_succ]
  simp [edge, mul_comm]

private theorem penultMin_weight {n : ℕ} (σ : Perm (n + 2)) :
    weight (insertMin (penult (n + 1)) σ) = (if lastAscent σ then Q else P) * weight σ ∧
      lastAscent (insertMin (penult (n + 1)) σ) := by
  have hkeep (j : Fin (n + 1)) :
      insertMin (penult (n + 1)) σ j.castSucc.castSucc = (σ j.castSucc).succ := by
    rw [← Fin.succAbove_of_castSucc_lt (penult (n + 1)) j.castSucc (by simp [penult])]
    exact insertMin_succAbove _ _ _
  have hlast : insertMin (penult (n + 1)) σ (Fin.last (n + 2)) = (σ (Fin.last (n + 1))).succ := by
    have h : (penult (n + 1)).succAbove (Fin.last (n + 1)) = Fin.last (n + 2) :=
      (Fin.succAbove_of_le_castSucc _ _ le_rfl).trans (Fin.succ_last _)
    rw [← h, insertMin_succAbove]
  refine ⟨?_, by simp [lastAscent, hlast]⟩
  unfold weight
  simp only [Fin.prod_univ_castSucc (n := n + 1), Fin.prod_univ_castSucc (n := n),
    Fin.succ_castSucc, Fin.succ_last, hkeep, insertMin_self, hlast, edge_succ,
    show (Fin.last (n + 1)).castSucc = penult (n + 1) from rfl]
  simp only [edge, Fin.not_lt_zero, ite_false, Fin.succ_pos, ite_true, lastAscent, penult]
  split_ifs <;> ring

-- The sequences are indexed from length two, where a last edge first exists.
private noncomputable def A (n : ℕ) : R :=
  total fun σ : Perm (n + 2) => if lastAscent σ then weight σ else 0

private noncomputable def D (n : ℕ) : R :=
  total fun σ : Perm (n + 2) => if lastAscent σ then 0 else weight σ

private theorem total_weight (n : ℕ) : total (weight (n := n + 1)) = A n + D n := by
  classical
  unfold A D total
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases ha : lastAscent σ <;> by_cases hv : Avoids σ <;> simp [ha, hv]

private theorem A_succ (n : ℕ) : A (n + 1) = Q * A n + P * D n := by
  classical
  unfold A D
  rw [total_insertMin]
  unfold total
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  obtain ⟨hw, ha⟩ := penultMin_weight σ
  by_cases h : lastAscent σ <;> by_cases hv : Avoids σ <;>
    simp [ha, hw, (appendMin_weight σ).2, h, hv]

private theorem D_succ (n : ℕ) : D (n + 1) = Q * (A n + D n) := by
  classical
  rw [← total_weight]
  unfold D
  rw [total_insertMin]
  unfold total
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  obtain ⟨hw, ha⟩ := appendMin_weight σ
  by_cases hv : Avoids σ <;> simp [ha, hw, (penultMin_weight σ).2, hv]

private theorem avoids_small {n : ℕ} (hn : n ≤ 2) (σ : Perm n) : Avoids σ := by
  intro i j k hij hjk
  have := k.isLt
  simp only [Fin.lt_def] at hij hjk
  omega

private theorem total_small {n : ℕ} (hn : n ≤ 1) (f : Perm n → R) :
    total f = f (Equiv.refl _) := by
  classical
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  let _ : Unique (Perm n) := uniqueOfSubsingleton (Equiv.refl _)
  simp [total, avoids_small (by omega : n ≤ 2), Unique.default_eq (Equiv.refl _)]

private theorem total_two (f : Perm 2 → R) : total f = f (insertMin 0 (Equiv.refl _)) +
    f (insertMin (Fin.last 1) (Equiv.refl _)) := by
  rw [total_insertMin (n := 0), total_small (by decide), total_small (by decide)]
  simp [show penult 0 = 0 by rfl, add_comm]

private theorem initial : A 0 = P ∧ D 0 = Q := by
  have hp : insertMin 0 (Equiv.refl (Fin 1)) (1 : Fin 2) = 1 := by
    change insertMin 0 (Equiv.refl (Fin 1)) ((0 : Fin 1).succ) = (0 : Fin 1).succ
    exact insertMin_succAbove (0 : Fin 2) (Equiv.refl (Fin 1)) 0
  unfold A D
  rw [total_two, total_two]
  simp [weight, lastAscent, penult, edge, hp,
    show (0 : Fin 1).succ = Fin.last 1 by rfl]

open PowerSeries

private noncomputable abbrev G := ascDesGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1])
private noncomputable def up : PowerSeries R := mk A
private noncomputable def down : PowerSeries R := mk D

private theorem coeff_G_succ (n : ℕ) : coeff (n + 1) G = total (weight (n := n)) := by
  classical
  simp only [ascDesGF, coeff_mk, total, weight_eq_powers, ← avoids_iff, Finset.sum_filter]

private theorem series_eq : G = 1 + X + X ^ 2 * (up + down) := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | n
  · classical
    simp [ascDesGF, ← avoids_iff, avoids_small (by decide : 0 ≤ 2), permAscents, permDescents]
  · simp [coeff_G_succ, total_small (by decide : 1 ≤ 1), weight, coeff_one, coeff_X_pow_mul']
  · simp [coeff_G_succ, total_weight, coeff_one, coeff_X_pow_mul', coeff_X, up, down]

private theorem up_rec : (1 - C Q * X) * up - C P * X * down = C P := by
  have h : up = C P + X * (C Q * up + C P * down) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [up, initial.1]
    | succ n => simp [up, down, A_succ, coeff_C_mul]
  linear_combination h

private theorem down_rec : (1 - C Q * X) * down - C Q * X * up = C Q := by
  have h : down = C Q + X * (C Q * (up + down)) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [down, initial.2]
    | succ n => simp [up, down, D_succ, coeff_C_mul]
  linear_combination h

private theorem combined :
    ((1 - C Q * X) ^ 2 - C P * C Q * X ^ 2) * (up + down) =
      C P + C Q + (C P * C Q - C Q ^ 2) * X := by
  linear_combination up_rec + (1 - C Q * X + C P * X) * down_rec

end ascDesGF_123_132

public section

open ascDesGF_123_132

-- Keep the default bijectivity proofs for the patterns inline in the statement.
set_option backward.proofsInPublic true in
/-- **Ascents and descents over permutations avoiding $123$ and $132$.** Let
$$G = \sum_{n \ge 0} \sum_{\sigma} x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$123$ and $132$, and $\mathrm{asc}(\sigma)$ and $\mathrm{des}(\sigma)$ are the numbers of ascents
and descents of $\sigma$; $G$ is a formal power series in $x$ with coefficients in
$\mathbb{Q}[p, q]$. Then
$$(1 - 2qx - pqx^2 + q^2x^2)\, G = 1 + x - 2qx + px^2 - qx^2 - pqx^2 + q^2x^2.$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 1
(`integers-2026-A18-cor-1`). -/
public theorem ascDesGF_123_132 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - 2 * q * PowerSeries.X - p * q * PowerSeries.X ^ 2 + q ^ 2 * PowerSeries.X ^ 2) *
        ascDesGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) =
      1 + PowerSeries.X - 2 * q * PowerSeries.X + p * PowerSeries.X ^ 2 -
        q * PowerSeries.X ^ 2 - p * q * PowerSeries.X ^ 2 + q ^ 2 * PowerSeries.X ^ 2 := by
  dsimp only
  rw [show ascDesGF _ _ = _ from series_eq]
  let x : PowerSeries R := PowerSeries.X
  let p : PowerSeries R := PowerSeries.C P
  let q : PowerSeries R := PowerSeries.C Q
  let d := (1 - q * x) ^ 2 - p * q * x ^ 2
  calc
    _ = d * (1 + x) + x ^ 2 * (d * (up + down)) := by dsimp [d, p, q, x]; ring
    _ = _ := by rw [show d * (up + down) = _ from combined]; dsimp [d, p, q, x]; ring

end

end MetaMathlibExt
