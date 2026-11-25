/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.DoubleAscentDescent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ascents and descents of permutations avoiding 132 and 321

`ascDesGF_132_321` computes the joint generating function by distinguishing whether the
largest entry is last.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace ascDesGF_132_321

private abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

-- If the last two entries of a triple form a descent, the first must lie between them.
private def Good {n : ℕ} (σ : Perm n) : Prop :=
  ∀ i j k, i < j → j < k → σ k < σ j → σ k < σ i ∧ σ i < σ j

private instance instDecidableGood {n : ℕ} (σ : Perm n) : Decidable (Good σ) := by
  unfold Good
  infer_instance

private theorem good_iff {n : ℕ} (σ : Perm n) :
    Good σ ↔ ¬ HasPattern σ (pattern3 ![0, 2, 1]) ∧ ¬ HasPattern σ (pattern3 ![2, 1, 0]) := by
  constructor
  · intro h
    constructor
    · rintro ⟨e, he, hv⟩
      have hkj := (hv 2 1).2 (by decide)
      have hik := (hv 0 2).2 (by decide)
      exact (h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide)) hkj).1.asymm hik
    · rintro ⟨e, he, hv⟩
      have hkj := (hv 2 1).2 (by decide)
      have hji := (hv 1 0).2 (by decide)
      exact (h _ _ _ (he 0 1 (by decide)) (he 1 2 (by decide)) hkj).2.asymm hji
  · rintro ⟨h132, h321⟩ i j k hij hjk hkj
    have he : StrictMono (![i, j, k] : Fin 3 → Fin n) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      fin_cases a <;> assumption
    constructor
    · by_contra! h
      have hik := lt_of_le_of_ne h (σ.injective.ne (hij.trans hjk).ne)
      apply h132
      refine ⟨![i, j, k], fun _ _ hlt => he hlt, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;> simp [pattern3, hkj, hik, hik.trans hkj,
        hkj.not_gt, hik.not_gt, (hik.trans hkj).not_gt]
    · by_contra! h
      have hji := lt_of_le_of_ne h (σ.injective.ne hij.ne')
      apply h321
      refine ⟨![i, j, k], fun _ _ hlt => he hlt, ?_⟩
      intro a b
      fin_cases a <;> fin_cases b <;> simp [pattern3, hkj, hji, hkj.trans hji,
        hkj.not_gt, hji.not_gt, (hkj.trans hji).not_gt]

private def appendMax {n : ℕ} (σ : Perm n) : Perm (n + 1) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] private theorem appendMax_last {n : ℕ} (σ : Perm n) :
    appendMax σ (Fin.last n) = Fin.last n := by
  unfold appendMax
  rw [Equiv.trans_apply, finSumFinEquiv_symm_last]
  rfl

@[simp] private theorem appendMax_castSucc {n : ℕ} (σ : Perm n) (i : Fin n) :
    appendMax σ i.castSucc = (σ i).castSucc := by
  unfold appendMax
  rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_castSucc]
  rfl

private theorem good_appendMax {n : ℕ} (σ : Perm n) : Good (appendMax σ) ↔ Good σ := by
  constructor
  · intro h i j k hij hjk hkj
    simpa using h i.castSucc j.castSucc k.castSucc (by simpa) (by simpa) (by simpa)
  · intro h i j k hij hjk hkj
    have lift {a : Fin (n + 1)} (ha : a < Fin.last n) :
        ∃ b : Fin n, b.castSucc = a := ⟨a.castLT ha, rfl⟩
    have hk : k < Fin.last n := by
      refine lt_of_le_of_ne (Fin.le_last _) ?_
      rintro rfl
      exact (Fin.le_last _).not_gt (by simpa using hkj)
    obtain ⟨k, rfl⟩ := lift hk
    obtain ⟨j, rfl⟩ := lift (hjk.trans hk)
    obtain ⟨i, rfl⟩ := lift (hij.trans (hjk.trans hk))
    simpa using h i j k (by simpa using hij) (by simpa using hjk) (by simpa using hkj)

private theorem exists_appendMax {n : ℕ} (σ : Perm (n + 1))
    (hσ : σ (Fin.last n) = Fin.last n) : ∃ τ : Perm n, appendMax τ = σ := by
  have restrict (τ : Perm (n + 1)) (hτ : τ (Fin.last n) = Fin.last n) (i : Fin n) :
      (τ i.castSucc).val < n := by
    have hne : τ i.castSucc ≠ Fin.last n := by
      rw [← hτ]
      exact τ.injective.ne (Fin.castSucc_ne_last i)
    exact Fin.lt_last_iff_ne_last.mpr hne
  let τ : Perm n :=
    { toFun := fun i => (σ i.castSucc).castLT (restrict σ hσ i)
      invFun := fun i => (σ.symm i.castSucc).castLT (restrict σ.symm
        (σ.symm_apply_eq.mpr hσ.symm) i)
      left_inv := fun i =>
        Fin.ext (congrArg (fun x : Fin (n + 1) => x.val) (σ.symm_apply_apply i.castSucc))
      right_inv := fun i =>
        Fin.ext (congrArg (fun x : Fin (n + 1) => x.val) (σ.apply_symm_apply i.castSucc)) }
  refine ⟨τ, Equiv.ext fun i => ?_⟩
  induction i using Fin.lastCases with
  | last => simpa using hσ.symm
  | cast i => rw [appendMax_castSucc]; rfl

private theorem appendMax_injective {n : ℕ} : Function.Injective (@appendMax n) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  simpa using Equiv.congr_fun h i.castSucc

-- This cyclic shift puts the maximum at `m`.
private def rotate {n : ℕ} (m : Fin n) : Perm (n + 1) :=
  Equiv.addRight (⟨n - m.val, by omega⟩ : Fin (n + 1))

private theorem rotate_val {n : ℕ} (m : Fin n) (i : Fin (n + 1)) :
    (rotate m i).val = if i.val ≤ m.val then i.val + (n - m.val) else i.val - (m.val + 1) := by
  change (i.val + (n - m.val)) % (n + 1) = _
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega : n + 1 ≤ i.val + (n - m.val)),
      Nat.mod_eq_of_lt (by omega)]
    omega

private theorem rotate_max {n : ℕ} (m : Fin n) :
    rotate m m.castSucc = Fin.last n := by
  apply Fin.ext
  rw [rotate_val]
  simp only [Fin.val_castSucc, le_refl, ite_true, Fin.val_last]
  omega

private theorem rotate_inversion {n : ℕ} (m : Fin n) {i j : Fin (n + 1)} (hij : i < j) :
    rotate m j < rotate m i ↔ i ≤ m.castSucc ∧ m.castSucc < j := by
  simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, rotate_val] at hij ⊢
  split_ifs <;> omega

private theorem good_rotate {n : ℕ} (m : Fin n) : Good (rotate m) := by
  intro i j k hij hjk hkj
  obtain ⟨hjm, hmk⟩ := (rotate_inversion m hjk).mp hkj
  exact ⟨(rotate_inversion m (hij.trans hjk)).mpr ⟨hij.le.trans hjm, hmk⟩,
    lt_of_not_ge fun h => ((rotate_inversion m hij).mp
      (lt_of_le_of_ne h ((rotate m).injective.ne hij.ne'))).2.not_ge hjm⟩

-- An interior maximum separates two increasing blocks, with every prefix value larger.
private theorem inversion_of_good {n : ℕ} {σ : Perm (n + 1)} (hσ : Good σ)
    {m : Fin n} (hm : σ m.castSucc = Fin.last n) {i j : Fin (n + 1)} (hij : i < j) :
    σ j < σ i ↔ i ≤ m.castSucc ∧ m.castSucc < j := by
  have hmax {k : Fin (n + 1)} (hk : k ≠ m.castSucc) : σ k < σ m.castSucc := by
    rw [hm]
    exact lt_of_le_of_ne (Fin.le_last _) (hm ▸ σ.injective.ne hk)
  have hsep {i j : Fin (n + 1)} (hi : i ≤ m.castSucc) (hj : m.castSucc < j) :
      σ j < σ i := by
    rcases hi.lt_or_eq with hi | rfl
    · exact (hσ i m.castSucc j hi hj (hmax hj.ne')).1
    · exact hmax hj.ne'
  refine ⟨fun h => ?_, fun ⟨hi, hj⟩ => hsep hi hj⟩
  have hi : i ≤ m.castSucc := by
    by_contra! hmi
    exact (hσ m.castSucc i j hmi hij h).2.not_ge (hmax hmi.ne').le
  refine ⟨hi, lt_of_not_ge fun hj => ?_⟩
  have hmLast := Fin.castSucc_lt_last m
  have hlast := hsep hj hmLast
  exact (hσ i j (Fin.last n) hij (hj.trans_lt hmLast) hlast).2.not_ge h.le

private theorem eq_rotate {n : ℕ} {σ : Perm (n + 1)} (hσ : Good σ)
    {m : Fin n} (hm : σ m.castSucc = Fin.last n) : σ = rotate m := by
  have hmono : StrictMono fun x => σ ((rotate m).symm x) := by
    intro x y hxy
    obtain ⟨i, rfl⟩ := (rotate m).surjective x
    obtain ⟨j, rfl⟩ := (rotate m).surjective y
    simp only [Equiv.symm_apply_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · apply lt_of_not_ge
      intro h
      have hinv := lt_of_le_of_ne h (σ.injective.ne hij.ne')
      exact ((rotate_inversion m hij).mpr
        ((inversion_of_good hσ hm hij).mp hinv)).asymm hxy
    · exact (lt_irrefl _ hxy).elim
    · exact (inversion_of_good hσ hm hji).mpr ((rotate_inversion m hji).mp hxy)
  apply Equiv.ext
  intro i
  simpa using hmono.apply_eq (x := rotate m i)

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

private theorem ascents_appendMax {n : ℕ} (σ : Perm (n + 1)) :
    permAscents (appendMax σ) = permAscents σ + 1 := by
  simp only [ascents_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp [-Fin.castSucc_succ, Fin.succ_castSucc]

private theorem descents_appendMax {n : ℕ} (σ : Perm (n + 1)) :
    permDescents (appendMax σ) = permDescents σ := by
  simp only [descents_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp [-Fin.castSucc_succ, Fin.succ_castSucc, (Fin.le_last _).not_gt]

private theorem rotate_adjacent_descent {n : ℕ} (m i : Fin n) :
    rotate m i.succ < rotate m i.castSucc ↔ i = m := by
  rw [rotate_inversion m (Fin.castSucc_lt_succ (i := i))]
  simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
  omega

private theorem descents_rotate {n : ℕ} (m : Fin (n + 1)) :
    permDescents (rotate m) = 1 := by
  simp [descents_eq_sum, rotate_adjacent_descent]

private theorem ascents_rotate {n : ℕ} (m : Fin (n + 1)) :
    permAscents (rotate m) = n := by
  have hass (i : Fin (n + 1)) : rotate m i.castSucc < rotate m i.succ ↔ i ≠ m := by
    rw [Ne, ← rotate_adjacent_descent]
    exact ⟨fun h => h.not_gt, fun h =>
      lt_of_le_of_ne (le_of_not_gt h) ((rotate m).injective.ne (Fin.castSucc_lt_succ (i := i)).ne)⟩
  have hs : permAscents (rotate m) + permDescents (rotate m) = n + 1 := by
    rw [ascents_eq_sum, descents_eq_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Fin (n + 1), (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = m <;> simp [hass, rotate_adjacent_descent, h]
      _ = _ := by simp
  rw [descents_rotate] at hs
  omega

private noncomputable def avoiderEquiv (n : ℕ) :
    ({σ : Perm (n + 1) // Good σ} ⊕ Fin (n + 1)) ≃ {σ : Perm (n + 2) // Good σ} := by
  let f : ({σ : Perm (n + 1) // Good σ} ⊕ Fin (n + 1)) → {σ : Perm (n + 2) // Good σ} :=
    Sum.elim (fun σ => ⟨appendMax σ.val, (good_appendMax σ.val).mpr σ.property⟩)
      (fun m => ⟨rotate m, good_rotate m⟩)
  have append_ne_rotate (σ : Perm (n + 1)) (m : Fin (n + 1)) : appendMax σ ≠ rotate m := by
    intro h
    have hmax : rotate m (Fin.last (n + 1)) = Fin.last (n + 1) := by rw [← h, appendMax_last]
    exact Fin.castSucc_ne_last m ((rotate m).injective ((rotate_max m).trans hmax.symm))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    have he := congrArg Subtype.val h
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Subtype.ext (appendMax_injective he))
    · exact (append_ne_rotate a.val b he).elim
    · exact (append_ne_rotate b.val a he.symm).elim
    · apply congrArg Sum.inr
      apply Fin.castSucc_inj.mp
      change rotate a = rotate b at he
      apply (rotate b).injective
      rw [rotate_max, ← he, rotate_max]
  · intro σ
    by_cases h : σ.val (Fin.last (n + 1)) = Fin.last (n + 1)
    · obtain ⟨τ, hτ⟩ := exists_appendMax σ.val h
      exact ⟨Sum.inl ⟨τ, (good_appendMax τ).mp (hτ ▸ σ.property)⟩, Subtype.ext hτ⟩
    · have hm : (σ.val.symm (Fin.last (n + 1))).val < n + 1 :=
        Fin.lt_last_iff_ne_last.mpr fun he => h (σ.val.symm_apply_eq.mp he).symm
      let m : Fin (n + 1) := (σ.val.symm (Fin.last (n + 1))).castLT hm
      exact ⟨Sum.inr m, Subtype.ext (eq_rotate σ.property (σ.val.apply_symm_apply _)).symm⟩

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev P : R := MvPolynomial.X 0
private noncomputable abbrev Q : R := MvPolynomial.X 1

private noncomputable def weight {n : ℕ} (σ : Perm n) : R :=
  P ^ permAscents σ * Q ^ permDescents σ

private noncomputable def total (n : ℕ) : R := by
  classical exact ∑ σ : {σ : Perm n // Good σ}, weight σ.val

private theorem total_succ_succ (n : ℕ) :
    total (n + 2) = P * total (n + 1) + (n + 1 : R) * P ^ n * Q := by
  classical
  unfold total
  rw [← (avoiderEquiv n).sum_comp, Fintype.sum_sum_type]
  change (∑ σ : {σ : Perm (n + 1) // Good σ}, weight (appendMax σ.val)) +
      (∑ m : Fin (n + 1), weight (rotate m)) = _
  simp only [weight, ascents_appendMax, descents_appendMax, ascents_rotate, descents_rotate,
    pow_succ]
  rw [Finset.mul_sum]
  have hmul (σ : Perm (n + 1)) :
      P ^ permAscents σ * P * Q ^ permDescents σ =
        P * (P ^ permAscents σ * Q ^ permDescents σ) := by ring
  simp [hmul, mul_assoc]

private theorem total_eq_filtered (n : ℕ) :
    total n = ∑ σ ∈ (Finset.univ.filter fun σ : Perm n => Good σ), weight σ := by
  classical
  exact (Finset.sum_subtype _ (fun σ => by simp) weight).symm

private theorem total_small {n : ℕ} (hn : n ≤ 1) : total n = 1 := by
  classical
  have hgood (σ : Perm n) : Good σ := by
    intro i j k hij hjk
    have := k.isLt
    change i.val < j.val at hij
    change j.val < k.val at hjk
    omega
  have hnext (i : Fin n) : ¬ i.val + 1 < n := by omega
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  rw [total_eq_filtered]
  simp [hgood, weight, permAscents, permDescents, hnext]

open PowerSeries

private noncomputable abbrev G := ascDesGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0])

private theorem coeff_G (n : ℕ) : coeff n G = total n := by
  classical
  rw [total_eq_filtered]
  simp only [G, ascDesGF, coeff_mk, weight, good_iff]

private noncomputable def positiveLengths : PowerSeries R := mk fun n => total (n + 1)
private noncomputable def geometric : PowerSeries R := mk fun n => P ^ n
private noncomputable def weightedGeometric : PowerSeries R := mk fun n => (n + 1 : R) * P ^ n

private theorem series_eq : G = 1 + X * positiveLengths := by
  apply PowerSeries.ext
  intro n
  rw [coeff_G]
  cases n <;> simp [positiveLengths, coeff_one, total_small]

private theorem positiveLengths_rec :
    (1 - X * C P) * positiveLengths = 1 + X * C Q * weightedGeometric := by
  have h : positiveLengths = 1 + X * (C P * positiveLengths + C Q * weightedGeometric) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [positiveLengths, total_small]
    | succ n =>
      simp only [positiveLengths, weightedGeometric, coeff_mk, map_add,
        coeff_one, Nat.add_one_ne_zero, ite_false, zero_add, coeff_succ_X_mul, coeff_C_mul]
      rw [total_succ_succ]
      ring
  linear_combination h

private theorem weightedGeometric_rec : (1 - X * C P) * weightedGeometric = geometric := by
  have h : weightedGeometric = geometric + X * (C P * weightedGeometric) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [weightedGeometric, geometric]
    | succ n =>
      simp [weightedGeometric, geometric, coeff_C_mul, pow_succ]
      ring
  linear_combination h

private theorem geometric_rec : (1 - X * C P) * geometric = 1 := by
  have h : geometric = 1 + X * (C P * geometric) := by
    apply PowerSeries.ext
    intro n
    cases n <;> simp [geometric, coeff_one, pow_succ, mul_comm]
  linear_combination h

end ascDesGF_132_321

public section

open ascDesGF_132_321

-- Keep the default bijectivity proofs for the patterns inline in the statement.
set_option backward.proofsInPublic true in
/-- **Ascents and descents over permutations avoiding $132$ and $321$.** Let
$$G = \sum_{n \ge 0} \sum_{\sigma} x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$132$ and $321$, and $\mathrm{asc}(\sigma)$ and $\mathrm{des}(\sigma)$ are the numbers of ascents
and descents of $\sigma$; $G$ is a formal power series in $x$ with coefficients in
$\mathbb{Q}[p, q]$. Then
$$(1 - px)^3\, G = 1 + x - 3px - 2px^2 + 3p^2x^2 + qx^2 + p^2x^3 - p^3x^3.$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 2
(`integers-2026-A18-cor-2`). -/
public theorem ascDesGF_132_321 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - p * PowerSeries.X) ^ 3 * ascDesGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) =
      1 + PowerSeries.X - 3 * p * PowerSeries.X - 2 * p * PowerSeries.X ^ 2 +
        3 * p ^ 2 * PowerSeries.X ^ 2 + q * PowerSeries.X ^ 2 + p ^ 2 * PowerSeries.X ^ 3 -
        p ^ 3 * PowerSeries.X ^ 3 := by
  dsimp only
  rw [show ascDesGF _ _ = _ from series_eq]
  let x : PowerSeries R := PowerSeries.X
  let d : PowerSeries R := 1 - x * PowerSeries.C P
  calc
    _ = d ^ 3 + x * d ^ 2 * (d * positiveLengths) := by dsimp [d, x]; ring
    _ = d ^ 3 + x * d ^ 2 + x ^ 2 * PowerSeries.C Q * (d * (d * weightedGeometric)) := by
      rw [show d * positiveLengths = _ from positiveLengths_rec]
      ring
    _ = d ^ 3 + x * d ^ 2 + x ^ 2 * PowerSeries.C Q := by
      rw [show d * weightedGeometric = _ from weightedGeometric_rec,
        show d * geometric = _ from geometric_rec, mul_one]
    _ = _ := by dsimp [d, x]; ring

end

end MetaMathlibExt
