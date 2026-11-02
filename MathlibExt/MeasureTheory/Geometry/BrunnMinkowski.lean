/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import MathlibExt.MeasureTheory.Integral.PrekopaLeindler
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory

section

open MeasureTheory
open scoped Pointwise ENNReal

namespace MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted

/-- Minkowski sum of compact sets is compact. -/
private theorem bm_isCompact_add {d : ℕ} {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (A + B) :=
  hA.add hB

/-- Translating `B` by a point of `A` stays inside the Minkowski sum. -/
private theorem bm_volume_le_volume_add {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ A) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) B ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (A + B) := by
  have hsub : a +ᵥ B ⊆ A + B := Set.vadd_set_subset_add ha
  calc (volume : Measure (EuclideanSpace ℝ (Fin n))) B
      = (volume : Measure (EuclideanSpace ℝ (Fin n))) (a +ᵥ B) :=
        (MeasureTheory.measure_vadd _ _ _).symm
    _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) (A + B) :=
        measure_mono hsub

/-- Nonnegative dilation scales Lebesgue measure by `r ^ n`. -/
private theorem bm_volume_smul_euclidean {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (S : Set (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (r • S) =
      ENNReal.ofReal (r ^ n) * (volume : Measure (EuclideanSpace ℝ (Fin n))) S := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg _ hr, finrank_euclideanSpace_fin]

/-- `n`-th root representation of a finite nonzero `ℝ≥0∞` number. -/
private theorem bm_exists_ofReal_pow_eq (n : ℕ) (hn : 0 < n) (α : ℝ≥0∞)
    (h0 : α ≠ 0) (htop : α ≠ ⊤) :
    0 < Real.rpow α.toReal ((1 : ℝ) / (n : ℝ)) ∧
      α = ENNReal.ofReal ((Real.rpow α.toReal ((1 : ℝ) / (n : ℝ))) ^ n) ∧
      ENNReal.rpow α ((1 : ℝ) / (n : ℝ)) =
        ENNReal.ofReal (Real.rpow α.toReal ((1 : ℝ) / (n : ℝ))) := by
  have hnNne : n ≠ 0 := ne_of_gt hn
  have hTpos : 0 < α.toReal := ENNReal.toReal_pos h0 htop
  have hTnn : 0 ≤ α.toReal := le_of_lt hTpos
  have hapos : 0 < Real.rpow α.toReal ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_pos_of_pos hTpos _
  refine ⟨hapos, ?_, ?_⟩
  · have h1 : (1 : ℝ) / (n : ℝ) = ((n : ℝ))⁻¹ := one_div _
    have hpow : (Real.rpow α.toReal ((1 : ℝ) / (n : ℝ))) ^ n = α.toReal := by
      rw [h1]
      exact Real.rpow_inv_natCast_pow hTnn hnNne
    rw [hpow, ENNReal.ofReal_toReal htop]
  · have hα : α = ENNReal.ofReal α.toReal := (ENNReal.ofReal_toReal htop).symm
    have hexp : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by positivity
    conv_lhs => rw [hα]
    exact ENNReal.ofReal_rpow_of_nonneg hTnn hexp

/-- Multiplicative Brunn–Minkowski from Prékopa–Leindler. -/
private theorem bm_volume_rpow_mul_le_of_convex_combination {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {K L M : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hL : MeasurableSet L) (hM : MeasurableSet M)
    (hmem : ∀ x ∈ K, ∀ y ∈ L, (1 - t) • x + t • y ∈ M) :
    ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) K) (1 - t) *
        ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) L) t ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))) M := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hf : Measurable (K.indicator 1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :=
    measurable_one.indicator hK
  have hg : Measurable (L.indicator 1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :=
    measurable_one.indicator hL
  have hh : Measurable (M.indicator 1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :=
    measurable_one.indicator hM
  have hzmt : ENNReal.rpow (0 : ℝ≥0∞) (1 - t) = 0 := ENNReal.zero_rpow_of_pos h1t
  have hzt : ENNReal.rpow (0 : ℝ≥0∞) t = 0 := ENNReal.zero_rpow_of_pos ht0
  have hfgh : ∀ x y : EuclideanSpace ℝ (Fin n),
      ENNReal.rpow (K.indicator 1 x) (1 - t) *
          ENNReal.rpow (L.indicator 1 y) t ≤
        M.indicator 1 ((1 - t) • x + t • y) := by
    intro x y
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ L
      · have hMmem := hmem x hx y hy
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hMmem]
        simp [ENNReal.one_rpow]
      · rw [Set.indicator_of_notMem hy, hzt, mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hx, hzmt, zero_mul]
      exact zero_le
  have hPL :=
    MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted.prekopa_leindler ht0 ht1
      hf hg hh hfgh
  rw [MeasureTheory.lintegral_indicator_one hK, MeasureTheory.lintegral_indicator_one hL,
    MeasureTheory.lintegral_indicator_one hM] at hPL
  exact hPL

/-- Inverse dilation normalizes an `ofReal`-power volume. -/
private theorem bm_volume_inv_smul_eq_ofReal_pow {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (S : Set (EuclideanSpace ℝ (Fin n))) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hS : (volume : Measure (EuclideanSpace ℝ (Fin n))) S =
      ENNReal.ofReal (c ^ n)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (((c / d)⁻¹) • S) =
      ENNReal.ofReal (d ^ n) := by
  have hcd : (0 : ℝ) ≤ (c / d)⁻¹ := by positivity
  have hpow_nn : (0 : ℝ) ≤ ((c / d)⁻¹) ^ n := by positivity
  rw [bm_volume_smul_euclidean S hcd, hS, ← ENNReal.ofReal_mul hpow_nn,
    inv_div, div_pow, div_mul_cancel₀ _ (pow_ne_zero n (ne_of_gt hc))]

/-- Core estimate: positive `ofReal`-power volumes add under Minkowski sum. -/
private theorem bm_ofReal_pow_add_le_volume_add {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hB : IsCompact B)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hAvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) A =
      ENNReal.ofReal (a ^ n))
    (hBvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) B =
      ENNReal.ofReal (b ^ n)) :
    ENNReal.ofReal ((a + b) ^ n) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)) := by
  have hab : (0 : ℝ) < a + b := by linarith
  set t : ℝ := b / (a + b) with htdef
  have ht0 : 0 < t := div_pos hb hab
  have ht1 : t < 1 := by rw [htdef, div_lt_one hab]; linarith
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1t_eq : 1 - t = a / (a + b) := by
    rw [htdef]
    field_simp
    ring
  have h1t_ne : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  have hKm : MeasurableSet ((1 - t)⁻¹ • A) :=
    (IsCompact.smul _ hA).measurableSet
  have hLm : MeasurableSet (t⁻¹ • B) :=
    (IsCompact.smul _ hB).measurableSet
  have hMm : MeasurableSet ((A + B)) :=
    (bm_isCompact_add hA hB).measurableSet
  have hmem : ∀ x ∈ (1 - t)⁻¹ • A, ∀ y ∈ t⁻¹ • B,
      (1 - t) • x + t • y ∈ (A + B) := by
    intro x hx y hy
    have hAx : (1 - t) • x ∈ A := (Set.mem_inv_smul_set_iff₀ h1t_ne A x).mp hx
    have hBy : t • y ∈ B := (Set.mem_inv_smul_set_iff₀ ht_ne B y).mp hy
    exact Set.add_mem_add hAx hBy
  have hPL := bm_volume_rpow_mul_le_of_convex_combination ht0 ht1 hKm hLm hMm hmem
  have hKvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) ((1 - t)⁻¹ • A) =
      ENNReal.ofReal ((a + b) ^ n) := by
    rw [h1t_eq]
    exact bm_volume_inv_smul_eq_ofReal_pow A ha hab hAvol
  have hLvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) (t⁻¹ • B) =
      ENNReal.ofReal ((a + b) ^ n) := by
    rw [htdef]
    exact bm_volume_inv_smul_eq_ofReal_pow B hb hab hBvol
  rw [hKvol, hLvol] at hPL
  have hapos : (0 : ℝ) < (a + b) ^ n := pow_pos hab n
  have hc0 : ENNReal.ofReal ((a + b) ^ n) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hapos)
  have hctop : ENNReal.ofReal ((a + b) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrw : ENNReal.rpow (ENNReal.ofReal ((a + b) ^ n)) (1 - t) *
      ENNReal.rpow (ENNReal.ofReal ((a + b) ^ n)) t =
      ENNReal.ofReal ((a + b) ^ n) :=
    calc ENNReal.rpow (ENNReal.ofReal ((a + b) ^ n)) (1 - t) *
            ENNReal.rpow (ENNReal.ofReal ((a + b) ^ n)) t
          = ENNReal.rpow (ENNReal.ofReal ((a + b) ^ n)) ((1 - t) + t) :=
            (ENNReal.rpow_add _ _ hc0 hctop).symm
        _ = ENNReal.rpow (ENNReal.ofReal ((a + b) ^ n)) 1 := by
            rw [sub_add_cancel]
        _ = ENNReal.ofReal ((a + b) ^ n) := ENNReal.rpow_one _
  rw [hrw] at hPL
  exact hPL

/-- Brunn–Minkowski when both volumes are nonzero. -/
private theorem bm_brunn_minkowski_of_pos {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hB : IsCompact B)
    (hA0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) A ≠ 0)
    (hB0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) B ≠ 0) :
    ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)))
        ((1 : ℝ) / (n : ℝ)) ≥
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A)
        ((1 : ℝ) / (n : ℝ)) +
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B)
        ((1 : ℝ) / (n : ℝ)) := by
  have hAfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) A ≠ ⊤ :=
    ne_of_lt hA.measure_lt_top
  have hBfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) B ≠ ⊤ :=
    ne_of_lt hB.measure_lt_top
  obtain ⟨hapos, hAeq, hArpow⟩ := bm_exists_ofReal_pow_eq n hn
    ((volume : Measure (EuclideanSpace ℝ (Fin n))) A) hA0 hAfin
  obtain ⟨hbpos, hBeq, hBrpow⟩ := bm_exists_ofReal_pow_eq n hn
    ((volume : Measure (EuclideanSpace ℝ (Fin n))) B) hB0 hBfin
  have hcore := bm_ofReal_pow_add_le_volume_add hA hB hapos hbpos hAeq hBeq
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := le_of_lt (one_div_pos.mpr hnpos)
  have hab : (0 : ℝ) < Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal
    ((1 : ℝ) / (n : ℝ)) + Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
    ((1 : ℝ) / (n : ℝ)) := add_pos hapos hbpos
  have hLHS : ENNReal.rpow (ENNReal.ofReal ((Real.rpow
      ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((1 : ℝ) / (n : ℝ)) +
      Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
      ((1 : ℝ) / (n : ℝ))) ^ n)) ((1 : ℝ) / (n : ℝ)) =
      ENNReal.ofReal (Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal
        ((1 : ℝ) / (n : ℝ))) +
      ENNReal.ofReal (Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
        ((1 : ℝ) / (n : ℝ))) :=
    calc ENNReal.rpow (ENNReal.ofReal ((Real.rpow
            ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((1 : ℝ) / (n : ℝ)) +
            Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
            ((1 : ℝ) / (n : ℝ))) ^ n)) ((1 : ℝ) / (n : ℝ))
          = ENNReal.ofReal (Real.rpow ((Real.rpow
            ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((1 : ℝ) / (n : ℝ)) +
            Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
            ((1 : ℝ) / (n : ℝ))) ^ n) ((1 : ℝ) / (n : ℝ))) :=
            ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (le_of_lt hab) n) hexp
        _ = ENNReal.ofReal (Real.rpow
            ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((1 : ℝ) / (n : ℝ)) +
            Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
            ((1 : ℝ) / (n : ℝ))) := by
            congr 1
            have h1 : (1 : ℝ) / (n : ℝ) = ((n : ℝ))⁻¹ := one_div _
            have hab2 : (0 : ℝ) ≤ Real.rpow
                ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((n : ℝ))⁻¹ +
                Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
                ((n : ℝ))⁻¹ := by
              rw [show ((n : ℝ))⁻¹ = (1 : ℝ) / (n : ℝ) from (one_div _).symm]
              exact le_of_lt hab
            rw [h1]
            exact Real.pow_rpow_inv_natCast hab2 (ne_of_gt hn)
        _ = ENNReal.ofReal (Real.rpow
            ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((1 : ℝ) / (n : ℝ))) +
            ENNReal.ofReal (Real.rpow
            ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal ((1 : ℝ) / (n : ℝ))) :=
            ENNReal.ofReal_add (le_of_lt hapos) (le_of_lt hbpos)
  have hmono : ENNReal.rpow (ENNReal.ofReal ((Real.rpow
      ((volume : Measure (EuclideanSpace ℝ (Fin n))) A).toReal ((1 : ℝ) / (n : ℝ)) +
      Real.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B).toReal
      ((1 : ℝ) / (n : ℝ))) ^ n)) ((1 : ℝ) / (n : ℝ)) ≤
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)))
        ((1 : ℝ) / (n : ℝ)) :=
    ENNReal.rpow_le_rpow hcore hexp
  rw [hLHS] at hmono
  rw [hArpow, hBrpow]
  exact hmono

/-- Brunn–Minkowski when one volume vanishes. -/
private theorem bm_brunn_minkowski_of_volume_eq_zero {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (h0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) A = 0 ∨
      (volume : Measure (EuclideanSpace ℝ (Fin n))) B = 0) :
    ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)))
        ((1 : ℝ) / (n : ℝ)) ≥
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A)
        ((1 : ℝ) / (n : ℝ)) +
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B)
        ((1 : ℝ) / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp : (0 : ℝ) < (1 : ℝ) / (n : ℝ) := one_div_pos.mpr hnpos
  have hexp_nn : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := le_of_lt hexp
  rcases h0 with hA0 | hB0
  · obtain ⟨a, ha⟩ := hAne
    have hle : (volume : Measure (EuclideanSpace ℝ (Fin n))) B ≤
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)) :=
      bm_volume_le_volume_add A B ha
    have hz : ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A)
        ((1 : ℝ) / (n : ℝ)) = 0 := by
      rw [hA0]
      exact ENNReal.zero_rpow_of_pos hexp
    rw [hz, zero_add]
    exact ENNReal.rpow_le_rpow hle hexp_nn
  · obtain ⟨b, hb⟩ := hBne
    have hle : (volume : Measure (EuclideanSpace ℝ (Fin n))) A ≤
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)) := by
      have h := bm_volume_le_volume_add B A hb
      rwa [add_comm B A] at h
    have hz : ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B)
        ((1 : ℝ) / (n : ℝ)) = 0 := by
      rw [hB0]
      exact ENNReal.zero_rpow_of_pos hexp
    rw [hz, add_zero]
    exact ENNReal.rpow_le_rpow hle hexp_nn

end MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted

end

@[expose] public section

open MeasureTheory
open scoped Pointwise

namespace MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted

/--
**Brunn–Minkowski inequality.** Let $n \ge 1$, let $A$ and $B$ be nonempty compact subsets of
$\mathbb{R}^n$, let $A + B = \{a + b : a \in A,\ b \in B\}$ be their Minkowski sum, and let
$\mathrm{vol}$ denote Lebesgue measure on $\mathbb{R}^n$. Then

$$\mathrm{vol}(A + B)^{1/n} \ge \mathrm{vol}(A)^{1/n} + \mathrm{vol}(B)^{1/n}.$$

Proves `Wanted` entry `brunn_minkowski`.

Source: H. Brunn, Über Ovale und Eiflächen (1887); H. Minkowski, Geometrie der Zahlen (1896); modern
formulation R. J. Gardner, Bull. AMS 39 (2002), 355–406, DOI 10.1090/S0273-0979-02-00941-2.
-/
public theorem brunn_minkowski
    {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) :
    ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)))
        ((1 : ℝ) / (n : ℝ)) ≥
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A)
        ((1 : ℝ) / (n : ℝ)) +
      ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B)
        ((1 : ℝ) / (n : ℝ)) := by
  by_cases h : (volume : Measure (EuclideanSpace ℝ (Fin n))) A = 0 ∨
      (volume : Measure (EuclideanSpace ℝ (Fin n))) B = 0
  · exact bm_brunn_minkowski_of_volume_eq_zero hn hAne hBne h
  · rw [not_or] at h
    exact bm_brunn_minkowski_of_pos hn hA hB h.1 h.2

end MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted
