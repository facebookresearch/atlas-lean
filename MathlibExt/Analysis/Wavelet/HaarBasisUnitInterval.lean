/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import MathlibExt.Analysis.Wavelet.Haar
import MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-!
# The Haar basis of the unit interval

The constant function and the normalized Haar wavelets on the dyadic subintervals form a
Hilbert basis of real `L²[0,1)`. Orthogonality to this family forces every dyadic cell integral
to vanish, so dyadic differentiation gives completeness.
-/

public section

open MeasureTheory Set Filter Topology
open MathlibExt.Analysis.Wavelet.Haar
open MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

namespace MathlibExt.Analysis.Wavelet.HaarBasisWanted

noncomputable section

local notation "U" => Ico (0 : ℝ) 1
local notation "unitVol" => volume.restrict U
private abbrev Index := Option (Σ k : ℕ, Fin (2 ^ k))

private lemma mem_cell (k : ℕ) (j : ℤ) (x : ℝ) :
    x ∈ dyadicInterval k j ↔ j ≤ 2 ^ k * x ∧ 2 ^ k * x < j + 1 := by
  have h : 0 < (2 : ℝ) ^ k := by positivity
  simp only [dyadicInterval, zpow_natCast, mem_Ico, div_le_iff₀ h, lt_div_iff₀ h, mul_comm x]

private lemma mem_left (k : ℕ) (j : ℤ) (x : ℝ) :
    x ∈ dyadicInterval (k + 1 : ℕ) (2 * j) ↔
      (2 : ℝ) ^ k * x - j ∈ Ico (0 : ℝ) (1 / 2) := by
  rw [mem_cell, mem_Ico, pow_succ]
  push_cast
  constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith

private lemma mem_right (k : ℕ) (j : ℤ) (x : ℝ) :
    x ∈ dyadicInterval (k + 1 : ℕ) (2 * j + 1) ↔
      (2 : ℝ) ^ k * x - j ∈ Ico (1 / 2 : ℝ) 1 := by
  rw [mem_cell, mem_Ico, pow_succ]
  push_cast
  constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith

private lemma children_union (k : ℕ) (j : ℤ) :
    dyadicInterval (k + 1 : ℕ) (2 * j) ∪ dyadicInterval (k + 1 : ℕ) (2 * j + 1) =
      dyadicInterval k j := by
  ext x
  rw [mem_union, mem_left, mem_right, mem_cell]
  simp only [mem_Ico]
  grind -ring

private lemma children_disjoint (k : ℕ) (j : ℤ) :
    Disjoint (dyadicInterval (k + 1 : ℕ) (2 * j)) (dyadicInterval (k + 1 : ℕ) (2 * j + 1)) := by
  rw [Set.disjoint_left]
  intro x hl hr
  exact ((mem_left k j x).1 hl).2.not_ge ((mem_right k j x).1 hr).1

private abbrev scale (k : ℕ) : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2)

private def cellVector (k : ℕ) (j : ℤ) : Lp ℝ 2 unitVol :=
  indicatorConstLp 2 (measurableSet_dyadicInterval k j) (measure_ne_top _ _) 1

private def family : Index → Lp ℝ 2 unitVol
  | none => cellVector 0 0
  | some ⟨k, j⟩ => scale k •
      (cellVector (k + 1) (2 * (j : ℤ)) - cellVector (k + 1) (2 * (j : ℤ) + 1))

private lemma cellVector_ae (k : ℕ) (j : ℤ) :
    ⇑(cellVector k j) =ᵐ[unitVol] (dyadicInterval k j).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

private lemma family_none : ⇑(family none) =ᵐ[unitVol] fun _ => (1 : ℝ) := by
  filter_upwards [cellVector_ae 0 0, ae_restrict_mem (μ := volume) (s := U) measurableSet_Ico]
    with x hx hU
  simpa [family, dyadicInterval, hU] using hx

private lemma family_some (k : ℕ) (j : Fin (2 ^ k)) :
    ⇑(family (some ⟨k, j⟩)) =ᵐ[unitVol] haarSystem k (j : ℕ) := by
  unfold family
  filter_upwards [Lp.coeFn_smul (scale k) (cellVector (k + 1) (2 * (j : ℤ)) -
    cellVector (k + 1) (2 * (j : ℤ) + 1)),
    Lp.coeFn_sub (cellVector (k + 1) (2 * (j : ℤ))) (cellVector (k + 1) (2 * (j : ℤ) + 1)),
    cellVector_ae (k + 1) (2 * (j : ℤ)), cellVector_ae (k + 1) (2 * (j : ℤ) + 1)]
    with x hsmul hsub hl hr
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  simp only [Pi.sub_apply] at hsub
  rw [hsmul, hsub, hl, hr]
  classical
  simp only [haarSystem, haarFunction, scale, zpow_natCast, Int.cast_natCast, Set.indicator,
    mem_left, mem_right, Pi.one_apply]

private lemma haar_off_unit (k : ℕ) (j : Fin (2 ^ k)) {x : ℝ} (hx : x ∉ U) :
    haarSystem k (j : ℕ) x = 0 := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hj : (j.val : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast j.isLt
  simp only [haarSystem, zpow_natCast, Int.cast_natCast]
  rw [haarFunction_eq_zero, mul_zero]
  rintro ⟨hl, hr⟩
  apply hx
  constructor
  · by_contra! h
    have := mul_neg_of_pos_of_neg hp h
    linarith [Nat.cast_nonneg (α := ℝ) j.val]
  · by_contra! h
    linarith [mul_le_mul_of_nonneg_left h hp.le]

private lemma inner_via_ae {v w : Lp ℝ 2 unitVol} {f g : ℝ → ℝ}
    (hv : ⇑v =ᵐ[unitVol] f) (hw : ⇑w =ᵐ[unitVol] g) :
    inner ℝ v w = ∫ x, f x * g x ∂unitVol := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv, hw] with x hx hy using by simp [hx, hy, RCLike.inner_apply, mul_comm]

private lemma inner_none_some (k : ℕ) (j : Fin (2 ^ k)) :
    inner ℝ (family none) (family (some ⟨k, j⟩)) = 0 := by
  rw [inner_via_ae family_none (family_some k j)]
  simp only [one_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hx => haar_off_unit k j hx)]
  simp only [haarSystem, integral_const_mul, integral_comp_dyadic, integral_haarFunction, mul_zero]

private lemma family_orthonormal : Orthonormal ℝ family := by
  classical
  rw [orthonormal_iff_ite]
  rintro (_ | ⟨k, j⟩) (_ | ⟨l, i⟩)
  · rw [inner_via_ae family_none family_none]
    simp [measureReal_def]
  · simpa using inner_none_some l i
  · rw [real_inner_comm]
    simpa using inner_none_some k j
  · rw [inner_via_ae (family_some k j) (family_some l i),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [haar_off_unit k j hx, zero_mul]),
      integral_haarSystem_mul_haarSystem]
    by_cases h : k = l
    · subst l
      simp [Fin.ext_iff]
    · simp [h]

private lemma inner_cell (f : Lp ℝ 2 unitVol) (k : ℕ) (j : ℤ) :
    inner ℝ (cellVector k j) f = ∫ x in dyadicInterval k j, f x ∂unitVol :=
  L2.inner_indicatorConstLp_one _ _ _

-- The two child integrals sum to the parent integral. Their scaled difference is a
-- Haar coefficient, so if both the parent integral and the coefficient vanish, so do both children.
private lemma integral_cells_zero (f : Lp ℝ 2 unitVol) (hf : ∀ i, inner ℝ (family i) f = 0)
    (k : ℕ) (j : ℤ) (hj : 0 ≤ j) (hlt : j < (2 : ℤ) ^ k) :
    ∫ x in dyadicInterval k j, f x ∂unitVol = 0 := by
  have hint : Integrable (⇑f) unitVol := (Lp.memLp f).integrable (by norm_num)
  induction k generalizing j with
  | zero =>
    have : j = 0 := by simp only [pow_zero] at hlt; omega
    subst j
    exact (inner_cell f 0 0).symm.trans (hf none)
  | succ k ih =>
    rw [pow_succ] at hlt
    let m := j / 2
    have hm : 0 ≤ m := by dsimp [m]; omega
    have hmk : m < (2 : ℤ) ^ k := by dsimp [m]; omega
    let i : Fin (2 ^ k) := ⟨m.toNat, (Int.toNat_lt_of_ne_zero (by positivity)).2 (by
      exact_mod_cast hmk)⟩
    have hi : (i : ℤ) = m := Int.toNat_of_nonneg hm
    have hdiff := hf (some ⟨k, i⟩)
    simp only [family, real_inner_smul_left, inner_sub_left, inner_cell, hi] at hdiff
    have hscale : scale k ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hscale)
    have hsum := ih m hm hmk
    rw [← children_union, setIntegral_union (children_disjoint _ _)
      (measurableSet_dyadicInterval _ _) hint.integrableOn hint.integrableOn] at hsum
    rcases (show j = 2 * m ∨ j = 2 * m + 1 by dsimp [m]; omega) with h | h <;>
      rw [h] <;> linarith

private lemma family_total : (Submodule.span ℝ (range family))ᗮ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro f hf
  have hortho (i : Index) : inner ℝ (family i) f = 0 :=
    hf _ (Submodule.subset_span (mem_range_self i))
  let g := (U).indicator (⇑f)
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ico).2
    ((Lp.memLp f).integrable (by norm_num))
  have hlim := ae_tendsto_setAverage_dyadicInterval hg.locallyIntegrable
  apply Lp.ext
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem (μ := volume) (s := U) measurableSet_Ico,
    Lp.coeFn_zero ℝ 2 unitVol] with x hx hxU hz
  have havg (k : ℕ) : ⨍ y in dyadicInterval k (dyadicIndex k x), g y = 0 := by
    let j := dyadicIndex k x
    have hj : 0 ≤ j := Int.floor_nonneg.2 (mul_nonneg hxU.1 (zpow_pos two_pos _).le)
    have hjlt : j < (2 : ℤ) ^ k := by
      apply Int.floor_lt.mpr
      simpa [zpow_natCast] using mul_lt_mul_of_pos_right hxU.2 (pow_pos two_pos k)
    rw [setAverage_eq, show (∫ y in dyadicInterval k j, g y) = 0 by
      rw [setIntegral_indicator measurableSet_Ico]
      simpa only [Measure.restrict_restrict (measurableSet_dyadicInterval k j)] using
        integral_cells_zero f hortho k j hj hjlt, smul_zero]
  simp only [havg] at hx
  have hzero : g x = 0 := tendsto_nhds_unique hx tendsto_const_nhds
  exact (show f x = 0 by simpa [g, hxU] using hzero).trans hz.symm

/-- **The Haar basis of `L²[0,1)`** (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7
(1998), Section 3.5, (3.47)). The constant function `1` together with the Haar functions
`H_{k,j}(x) = 2^{k/2} H(2^k x - j)`, `k ≥ 0`, `0 ≤ j < 2^k`, fitted to the dyadic intervals
`2^{-k}[j, j+1)`, form an orthonormal basis of `L²[0,1)`: there is a Hilbert basis of
`L²([0,1))` indexed by `Option (Σ k, Fin (2^k))` whose elements are a.e. equal to these
functions. -/
theorem exists_hilbertBasis_haar_unitInterval :
    ∃ b : HilbertBasis (Option (Σ k : ℕ, Fin (2 ^ k))) ℝ
        (Lp ℝ 2 (volume.restrict (Ico (0 : ℝ) 1))),
      (⇑(b none : Lp ℝ 2 (volume.restrict (Ico (0 : ℝ) 1))) =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
          fun _ => (1 : ℝ)) ∧
      ∀ (k : ℕ) (j : Fin (2 ^ k)),
        ⇑(b (some ⟨k, j⟩) : Lp ℝ 2 (volume.restrict (Ico (0 : ℝ) 1)))
          =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] haarSystem k (j : ℕ) := by
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot family_orthonormal family_total, ?_⟩
  simpa only [HilbertBasis.coe_mkOfOrthogonalEqBot] using And.intro family_none family_some

end

end MathlibExt.Analysis.Wavelet.HaarBasisWanted
