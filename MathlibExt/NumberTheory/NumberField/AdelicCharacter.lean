/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`P2M/Sol/S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.lean`,
`P2M/Sol/S_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one.lean`,
`P2M/Sol/S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean` and
`P2M/Sol/S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.NumberField.GlobalAddChar
public import MathlibExt.NumberTheory.NumberField.AdelicBox
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.RingTheory.ClassGroup.Basic
public import MathlibExt.NumberTheory.NumberField.FiniteAdeleDensity

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm Filter Topology
open NumberField.mixedEmbedding
open NumberField.InfinitePlace NumberField.InfiniteAdeleRing
open scoped Pointwise

noncomputable section

namespace NumberField
namespace AdelicFourier

variable (F : Type*) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

theorem exists_norm_apply_le_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℝ, ∀ x : 𝔸, ‖ψ x‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨k, hk⟩ := (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F x).exists
  have hkx : ψ (ι k + x) = ψ x := by
    rw [AddChar.map_add_eq_mul, hψ.principalInvariant k, one_mul]
  rw [← hkx]
  exact hM _ (hsub hk)

theorem norm_apply_le_one_of_bounded {ψ : AddChar 𝔸 ℂ} {M : ℝ} (hM : ∀ x : 𝔸, ‖ψ x‖ ≤ M)
    (x : 𝔸) : ‖ψ x‖ ≤ 1 := by
  by_contra h
  have h1 : 1 < ‖ψ x‖ := lt_of_not_ge h
  have hpow : ∀ n : ℕ, ‖ψ x‖ ^ n ≤ M := fun n => by
    rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
    exact hM _
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually (eventually_gt_atTop M)).exists
  exact absurd (hpow n) (not_le.mpr hn)

theorem norm_apply_eq_one_of_isGlobalAddChar_impl {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ‖ψ x‖ = 1 := by
  obtain ⟨M, hM⟩ := exists_norm_apply_le_of_isGlobalAddChar F hψ
  refine le_antisymm (norm_apply_le_one_of_bounded F hM x) ?_
  have hneg : ‖ψ (-x)‖ ≤ 1 := norm_apply_le_one_of_bounded F hM (-x)
  have hprod : ‖ψ (-x)‖ * ‖ψ x‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, norm_one]
  calc (1 : ℝ) = ‖ψ (-x)‖ * ‖ψ x‖ := hprod.symm
    _ ≤ 1 * ‖ψ x‖ := mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
    _ = ‖ψ x‖ := one_mul _

def toCircleAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) : AddChar 𝔸 Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x)⟩
  map_zero_eq_one' := by
    ext
    simp only [AddChar.map_zero_eq_one]
    rfl
  map_add_eq_mul' a b := by
    ext
    simp only [AddChar.map_add_eq_mul]
    rfl

theorem coe_toCircleAddChar_apply {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ((toCircleAddChar F hψ x : Circle) : ℂ) = ψ x := rfl

theorem exists_compAddChar_eq_of_isGlobalAddChar_impl {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ e : AddChar 𝔸 Circle, Circle.coeHom.compAddChar e = ψ :=
  ⟨toCircleAddChar F hψ, by ext x; rfl⟩


example : ∀ {ψ : AddChar 𝔸 ℂ} (_ : IsGlobalAddChar F ψ) (x : 𝔸), ‖ψ x‖ = 1 :=
  fun hψ x => norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x
example : ∀ {ψ : AddChar 𝔸 ℂ} (_ : IsGlobalAddChar F ψ),
    ∃ e : AddChar 𝔸 Circle, Circle.coeHom.compAddChar e = ψ :=
  fun hψ => exists_compAddChar_eq_of_isGlobalAddChar_impl F hψ

end NumberField.AdelicFourier

end

public theorem NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar
    (F : Type*) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : AutomorphicForm.IsGlobalAddChar F ψ)
    (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 :=
  NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x

noncomputable section


namespace NumberField
namespace AdelicR2

lemma eq_one_of_forall_pow_norm_sub_one_le {u : ℂ} (h : ∀ n : ℕ, ‖u ^ n - 1‖ ≤ 2⁻¹) :
    u = 1 := by
  have key : ∀ j : ℕ, (3 / 2 : ℝ) ^ j * ‖u - 1‖ ≤ ‖u ^ (2 ^ j) - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h2 : u ^ (2 ^ (j + 1)) - 1 = (u ^ (2 ^ j) - 1) * (u ^ (2 ^ j) + 1) := by
        rw [pow_succ, pow_mul]
        ring
      have hplus : (3 / 2 : ℝ) ≤ ‖u ^ (2 ^ j) + 1‖ := by
        have : (2 : ℝ) - ‖u ^ (2 ^ j) - 1‖ ≤ ‖u ^ (2 ^ j) + 1‖ := by
          have := norm_sub_norm_le (2 : ℂ) (1 - u ^ (2 ^ j))
          have h2' : (2 : ℂ) - (1 - u ^ (2 ^ j)) = u ^ (2 ^ j) + 1 := by ring
          simpa [h2', norm_sub_rev] using this
        linarith [h (2 ^ j)]
      calc (3 / 2 : ℝ) ^ (j + 1) * ‖u - 1‖
          = (3 / 2) * ((3 / 2 : ℝ) ^ j * ‖u - 1‖) := by ring
        _ ≤ (3 / 2) * ‖u ^ (2 ^ j) - 1‖ := by
            have h32 : (0 : ℝ) ≤ 3 / 2 := by norm_num
            exact mul_le_mul_of_nonneg_left ih h32
        _ ≤ ‖u ^ (2 ^ j) + 1‖ * ‖u ^ (2 ^ j) - 1‖ :=
            mul_le_mul_of_nonneg_right hplus (norm_nonneg _)
        _ = ‖u ^ (2 ^ j) - 1‖ * ‖u ^ (2 ^ j) + 1‖ := mul_comm _ _
        _ = ‖u ^ (2 ^ (j + 1)) - 1‖ := by rw [← norm_mul, ← h2]
  by_contra hne
  have hd : 0 < ‖u - 1‖ := by
    simpa [norm_pos_iff, sub_eq_zero] using hne
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((2 : ℝ)⁻¹ / ‖u - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : (3 / 2 : ℝ) ^ j * ‖u - 1‖ ≤ 2⁻¹ := (key j).trans (h _)
  have h2 : (2 : ℝ)⁻¹ < (3 / 2 : ℝ) ^ j * ‖u - 1‖ := by
    rw [div_lt_iff₀ hd] at hj
    linarith
  linarith

end NumberField.AdelicR2


noncomputable section

namespace NumberField
namespace AdelicR2Slices

variable {F : Type*} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (RingOfIntegers F) F
local notation "𝔸f" => FiniteAdeleRing (RingOfIntegers F) F
local notation "𝔸i" => InfiniteAdeleRing F

open Classical in
def archSingle (w : InfinitePlace F) (s : w.Completion) : 𝔸i := Pi.single w s

open Classical in
def finSingle (v : HeightOneSpectrum (RingOfIntegers F)) (t : v.adicCompletion F) : 𝔸f :=
  RestrictedProduct.single
    (fun u : HeightOneSpectrum (RingOfIntegers F) => u.adicCompletionIntegers F) v t

def archSlice (w : InfinitePlace F) (s : w.Completion) : 𝔸 := (archSingle w s, 0)

def finSlice (v : HeightOneSpectrum (RingOfIntegers F)) (t : v.adicCompletion F) : 𝔸 :=
  (0, finSingle v t)

omit [NumberField F] in
private lemma mulApply_i (a b : 𝔸i) (u : InfinitePlace F) : (a * b) u = a u * b u := rfl

private lemma fst_mul (y z : 𝔸) : (y * z).1 = y.1 * z.1 := rfl

private lemma snd_mul (y z : 𝔸) : (y * z).2 = y.2 * z.2 := rfl

omit [NumberField F] in
open Classical in
theorem mul_archSingle (y1 : 𝔸i) (w : InfinitePlace F) (s : w.Completion) :
    y1 * archSingle w s = archSingle w (y1 w * s) := by
  funext u
  rw [mulApply_i]
  by_cases hu : u = w
  · subst hu
    show y1 u * Pi.single u s u = Pi.single u (y1 u * s) u
    simp
  · show y1 u * Pi.single w s u = Pi.single w (y1 w * s) u
    simp [Pi.single_eq_of_ne hu]

open Classical in
theorem mul_finSingle (y2 : 𝔸f) (v : HeightOneSpectrum (RingOfIntegers F))
    (t : v.adicCompletion F) :
    y2 * finSingle v t = finSingle v (y2 v * t) := by
  unfold finSingle
  have h := RestrictedProduct.single_mul
    (A := fun u : HeightOneSpectrum (RingOfIntegers F) => u.adicCompletionIntegers F) v t y2
  exact (mul_comm _ _).trans (h.symm.trans (congrArg
    (RestrictedProduct.single
      (fun u : HeightOneSpectrum (RingOfIntegers F) => u.adicCompletionIntegers F) v)
    (mul_comm t (y2 v))))

theorem mul_archSlice (y : 𝔸) (w : InfinitePlace F) (s : w.Completion) :
    y * archSlice w s = archSlice w (y.1 w * s) := by
  unfold archSlice
  refine Prod.ext ?_ ?_
  · rw [fst_mul]
    exact mul_archSingle y.1 w s
  · rw [snd_mul]
    exact mul_zero _

theorem mul_finSlice (y : 𝔸) (v : HeightOneSpectrum (RingOfIntegers F))
    (t : v.adicCompletion F) :
    y * finSlice v t = finSlice v (y.2 v * t) := by
  unfold finSlice
  refine Prod.ext ?_ ?_
  · rw [fst_mul]
    exact mul_zero _
  · rw [snd_mul]
    exact mul_finSingle y.2 v t

theorem forall_archSlice_eq_one {ψ : AddChar 𝔸 ℂ} {y : 𝔸}
    (hy : ∀ x : 𝔸, ψ (y * x) = 1) {w : InfinitePlace F} (hw : y.1 w ≠ 0)
    (s : w.Completion) : ψ (archSlice w s) = 1 := by
  have h := hy (archSlice w ((y.1 w)⁻¹ * s))
  rwa [mul_archSlice, ← mul_assoc, mul_inv_cancel₀ hw, one_mul] at h

theorem forall_finSlice_eq_one {ψ : AddChar 𝔸 ℂ} {y : 𝔸}
    (hy : ∀ x : 𝔸, ψ (y * x) = 1) {v : HeightOneSpectrum (RingOfIntegers F)}
    (hv : y.2 v ≠ 0) (t : v.adicCompletion F) : ψ (finSlice v t) = 1 := by
  have h := hy (finSlice v ((y.2 v)⁻¹ * t))
  rwa [mul_finSlice, ← mul_assoc, mul_inv_cancel₀ hv, one_mul] at h

theorem nonzero_arch_or_fin {y : 𝔸} (hy : y ≠ 0) :
    (∃ w : InfinitePlace F, y.1 w ≠ 0) ∨
      (∃ v : HeightOneSpectrum (RingOfIntegers F), y.2 v ≠ 0) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  apply hy
  refine Prod.ext ?_ ?_
  · funext w; exact h1 w
  · ext v : 1; exact h2 v

end NumberField.AdelicR2Slices

open scoped nonZeroDivisors Classical ENNReal NNReal

noncomputable section

namespace NumberField
namespace AdelicR2Mesh

variable (F : Type*) [Field F] [NumberField F]

local notation "E" => mixedSpace F

def latticeB := fractionalIdealLatticeBasis F (1 : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ)

def latticeC : ℝ := ∑ i, ‖latticeB F i‖

theorem latticeC_nonneg : 0 ≤ latticeC F :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

variable {F}

omit [NumberField F] in
theorem normAtPlace_mixedEmbedding_mul (w : InfinitePlace F) (η : F) (x : E) :
    normAtPlace w (mixedEmbedding F η * x) = w η * normAtPlace w x := by
  by_cases hw : IsReal w
  · have hcomp : (mixedEmbedding F η * x).1 ⟨w, hw⟩
        = (mixedEmbedding F η).1 ⟨w, hw⟩ * x.1 ⟨w, hw⟩ := rfl
    rw [normAtPlace_apply_of_isReal hw, hcomp, norm_mul,
      show ‖(mixedEmbedding F η).1 ⟨w, hw⟩‖ = normAtPlace w (mixedEmbedding F η) from
        (normAtPlace_apply_of_isReal hw _).symm,
      normAtPlace_apply, ← normAtPlace_apply_of_isReal hw x]
  · have hw' : IsComplex w := not_isReal_iff_isComplex.mp hw
    have hcomp : (mixedEmbedding F η * x).2 ⟨w, hw'⟩
        = (mixedEmbedding F η).2 ⟨w, hw'⟩ * x.2 ⟨w, hw'⟩ := rfl
    rw [normAtPlace_apply_of_isComplex hw', hcomp, norm_mul,
      show ‖(mixedEmbedding F η).2 ⟨w, hw'⟩‖ = normAtPlace w (mixedEmbedding F η) from
        (normAtPlace_apply_of_isComplex hw' _).symm,
      normAtPlace_apply, ← normAtPlace_apply_of_isComplex hw' x]

theorem normAtPlace_le_norm (w : InfinitePlace F) (x : E) : normAtPlace w x ≤ ‖x‖ := by
  by_cases hw : IsReal w
  · rw [normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm x.1 ⟨w, hw⟩).trans (norm_fst_le x)
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
    exact (norm_le_pi_norm x.2 _).trans (norm_snd_le x)

theorem exists_mem_sub_normAtPlace_lt (J : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ)
    {η : F} (hηJ : η ∈ (J : FractionalIdeal (RingOfIntegers F)⁰ F)) (hη0 : η ≠ 0)
    {δ : ℝ} (T : Set (InfinitePlace F))
    (hsmall : ∀ w : InfinitePlace F, w ∉ T → w η < δ) (z : E) :
    ∃ a ∈ (J : FractionalIdeal (RingOfIntegers F)⁰ F),
      ∀ w : InfinitePlace F, w ∉ T →
        normAtPlace w (z - mixedEmbedding F a) < δ * (latticeC F + 1) := by
  set z' : E := mixedEmbedding F η⁻¹ * z with hz'
  set q := ZSpan.floor (latticeB F) z' with hq

  have hqmem : (q : E) ∈ mixedEmbedding F ''
      ((1 : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
        FractionalIdeal (RingOfIntegers F)⁰ F) := by
    rw [← mem_span_fractionalIdealLatticeBasis]
    exact SetLike.coe_mem q
  obtain ⟨b, hb1, hqb⟩ := hqmem
  rw [Units.val_one] at hb1
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).mp (SetLike.mem_coe.mp hb1)

  refine ⟨η * b, ?_, ?_⟩
  · have hmem : η * b = c • η := by rw [Algebra.smul_def, ← hc, mul_comm]
    rw [hmem, ← FractionalIdeal.mem_coe]
    rw [← FractionalIdeal.mem_coe] at hηJ
    exact Submodule.smul_mem _ c hηJ
  · intro w hw

    have hid : z - mixedEmbedding F (η * b)
        = mixedEmbedding F η * ZSpan.fract (latticeB F) z' := by
      calc z - mixedEmbedding F (η * b)
          = mixedEmbedding F η * z' - mixedEmbedding F η * (q : E) := by
            rw [hz', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hη0, map_one, one_mul,
              map_mul, hqb]
        _ = mixedEmbedding F η * (z' - (q : E)) := by ring
        _ = mixedEmbedding F η * ZSpan.fract (latticeB F) z' := by
            rw [ZSpan.fract_apply, hq]
    rw [hid, normAtPlace_mixedEmbedding_mul]
    have h1 : normAtPlace w (ZSpan.fract (latticeB F) z') ≤ latticeC F :=
      (normAtPlace_le_norm w _).trans (ZSpan.norm_fract_le (latticeB F) z')
    calc w η * normAtPlace w (ZSpan.fract (latticeB F) z')
        ≤ w η * (latticeC F + 1) := by
          refine mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (apply_nonneg w η)
      _ < δ * (latticeC F + 1) := by
          refine mul_lt_mul_of_pos_right (hsmall w hw) ?_
          linarith [latticeC_nonneg F]

theorem exists_ne_zero_small_off (J : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ)
    (w₀ : InfinitePlace F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η ∈ (J : FractionalIdeal (RingOfIntegers F)⁰ F), η ≠ 0 ∧
      ∀ w : InfinitePlace F, w ≠ w₀ → w η < δ := by
  have hδ' : (0 : ℝ≥0) < δ.toNNReal := Real.toNNReal_pos.mpr hδ
  set A' : ℝ≥0 := ∏ w ∈ Finset.univ.erase w₀, δ.toNNReal ^ (mult w) with hA'
  set A : ℝ≥0∞ := (convexBodyLTFactor F : ℝ≥0∞) * (A' : ℝ≥0∞) with hA
  have hA0 : A ≠ 0 := by
    rw [hA]
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (lt_of_lt_of_le one_pos (one_le_convexBodyLTFactor F)).ne'
    · rw [hA']
      refine ENNReal.coe_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun w _ => ?_)
      exact pow_ne_zero _ hδ'.ne'
  have hAtop : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  set M : ℝ≥0 := (minkowskiBound F J / A).toNNReal + 1 with hM
  have hM1 : (1 : ℝ≥0) ≤ M := le_add_self
  set f : InfinitePlace F → ℝ≥0 := fun w => if w = w₀ then M else δ.toNNReal with hf
  have hvol : minkowskiBound F J < volume (convexBodyLT F f) := by
    rw [convexBodyLT_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    have hrest : (∏ w ∈ Finset.univ.erase w₀, (f w) ^ (mult w)) = A' := by
      rw [hA']
      refine Finset.prod_congr rfl fun w hw => ?_
      simp only [Finset.mem_erase] at hw
      rw [hf]
      simp [ite_eq_right hw.1]
    rw [hrest, show f w₀ = M from ite_eq_left rfl,
      show ((A' * M ^ mult w₀ : ℝ≥0) : ℝ≥0∞) = (A' : ℝ≥0∞) * (M : ℝ≥0∞) ^ mult w₀ by
        push_cast; ring,
      ← mul_assoc, ← hA]
    have hMpow : (M : ℝ≥0∞) ≤ (M : ℝ≥0∞) ^ (mult w₀) := by
      refine le_self_pow ?_ mult_ne_zero
      exact_mod_cast hM1
    refine lt_of_lt_of_le ?_ (mul_le_mul_right hMpow A)
    have hdiv : minkowskiBound F J / A < (M : ℝ≥0∞) := by
      rw [hM]
      push_cast
      refine lt_of_le_of_lt (le_of_eq (ENNReal.coe_toNNReal ?_).symm) ?_
      · exact (ENNReal.div_lt_top (minkowskiBound_lt_top F J).ne hA0).ne
      · exact ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero
    calc minkowskiBound F J = A * (minkowskiBound F J / A) := by
          rw [mul_comm]
          exact (ENNReal.div_mul_cancel hA0 hAtop).symm
      _ < A * M := ENNReal.mul_lt_mul_right hA0 hAtop hdiv
  obtain ⟨a, haJ, ha0, hbound⟩ := exists_ne_zero_mem_ideal_lt F J hvol
  refine ⟨a, haJ, ha0, fun w hw => ?_⟩
  have hb := hbound w
  rw [hf] at hb
  simp only [ite_eq_right hw] at hb
  rwa [Real.coe_toNNReal _ hδ.le] at hb

theorem exists_mem_sub_normAtPlace_lt_off (J : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ)
    (w₀ : InfinitePlace F) (z : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ (J : FractionalIdeal (RingOfIntegers F)⁰ F),
      ∀ w : InfinitePlace F, w ≠ w₀ → normAtPlace w (z - mixedEmbedding F a) < ε := by
  have hC : 0 < latticeC F + 1 := by linarith [latticeC_nonneg F]
  obtain ⟨η, hηJ, hη0, hsmall⟩ := exists_ne_zero_small_off J w₀ (div_pos hε hC)
  obtain ⟨a, haJ, hclose⟩ := exists_mem_sub_normAtPlace_lt J hηJ hη0 {w₀}
    (fun w hw => hsmall w (by simpa using hw)) z
  refine ⟨a, haJ, fun w hw => ?_⟩
  have h := hclose w (by simpa using hw)
  rwa [div_mul_cancel₀ _ hC.ne'] at h

theorem exists_mem_sub_normAtPlace_lt_all (J : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ)
    {δ : ℝ} (hδ : 0 < δ)
    (hvol : minkowskiBound F J < volume (convexBodyLT F (fun _ => δ.toNNReal)))
    (z : E) :
    ∃ a ∈ (J : FractionalIdeal (RingOfIntegers F)⁰ F),
      ∀ w : InfinitePlace F, normAtPlace w (z - mixedEmbedding F a) < δ * (latticeC F + 1) := by
  obtain ⟨η, hηJ, hη0, hbound⟩ := exists_ne_zero_mem_ideal_lt F J hvol
  have hsmall : ∀ w : InfinitePlace F, w ∉ (∅ : Set (InfinitePlace F)) → w η < δ := by
    intro w _
    have hb := hbound w
    rwa [Real.coe_toNNReal _ hδ.le] at hb
  obtain ⟨a, haJ, hclose⟩ := exists_mem_sub_normAtPlace_lt J hηJ hη0 ∅ hsmall z
  exact ⟨a, haJ, fun w => hclose w (Set.notMem_empty w)⟩

end NumberField.AdelicR2Mesh

namespace NumberField
namespace AdelicR2General

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {F : Type*} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (NumberField.RingOfIntegers F) F
local notation "𝔸f" => FiniteAdeleRing (NumberField.RingOfIntegers F) F
local notation "𝔸i" => InfiniteAdeleRing F

private lemma valued_algebraMap_eq {v : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    (N : NumberField.RingOfIntegers F) :
    Valued.v (algebraMap F (v.adicCompletion F)
        (algebraMap (NumberField.RingOfIntegers F) F N)) = v.intValuation N := by
  have h : Valued.v (algebraMap F (v.adicCompletion F)
      (algebraMap (NumberField.RingOfIntegers F) F N))
      = v.valuation F (algebraMap (NumberField.RingOfIntegers F) F N) :=
    valuedAdicCompletion_eq_valuation' v _
  rw [h, valuation_of_algebraMap]

private lemma exp_neg_one_pow (k : ℕ) : (exp (-1 : ℤ)) ^ k = exp (-(k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← exp_add]
    congr 1
    push_cast
    ring

private lemma exists_pow_subset_of_mem_nhds
    {v : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    {t : Set (v.adicCompletionIntegers F)} (ht : t ∈ nhds 0) :
    ∃ k : ℕ, ∀ (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F),
      Valued.v y ≤ exp (-(k : ℤ)) → (⟨y, hy⟩ : v.adicCompletionIntegers F) ∈ t := by
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp ht
  have h0 : ((0 : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := rfl
  rw [h0] at hu
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt hγ0
  refine ⟨k, fun y hy hle => hut (hγ ?_)⟩
  simp only [Set.mem_setOf_eq]
  show Valued.v.restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hle hk

theorem exists_level_smul_integral_subset {U : Set 𝔸f} (hU : U ∈ nhds (0 : 𝔸f)) :
    ∃ N : NumberField.RingOfIntegers F, N ≠ 0 ∧ ∀ r : 𝔸f,
      (∀ v, r v ∈ v.adicCompletionIntegers F) →
      algebraMap F 𝔸f (algebraMap (NumberField.RingOfIntegers F) F N) * r ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v =>
    Valued.isOpen_valuationSubring _
  set sm := RestrictedProduct.structureMap
      (fun w : HeightOneSpectrum (NumberField.RingOfIntegers F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      Filter.cofinite with hsmdef
  have hsm0 : sm 0 = (0 : 𝔸f) := by
    ext w
    rfl
  have hV : sm ⁻¹' U ∈ nhds 0 := by
    have hc : Continuous sm :=
      (RestrictedProduct.isOpenEmbedding_structureMap hAopen).continuous
    have := hc.continuousAt (x := 0)
    exact this.preimage_mem_nhds (by rwa [hsm0])
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hIfin, t, ht, hsub⟩ := hV
  choose k hk using fun v : HeightOneSpectrum (NumberField.RingOfIntegers F) =>
    exists_pow_subset_of_mem_nhds (ht v)
  choose π hπmem hπne using fun v : HeightOneSpectrum (NumberField.RingOfIntegers F) =>
    Submodule.ne_bot_iff _ |>.mp v.ne_bot
  set N := ∏ v ∈ hIfin.toFinset, π v ^ k v with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hπne v)
  refine ⟨N, hN0, fun r hr => ?_⟩
  have hNval : ∀ v ∈ hIfin.toFinset, v.intValuation N ≤ exp (-(k v : ℤ)) := by
    intro v hv
    rw [hNdef, map_prod]
    rw [← Finset.prod_erase_mul _ _ hv]
    have h1 : v.intValuation (π v ^ k v) ≤ exp (-(k v : ℤ)) := by
      rw [map_pow, ← exp_neg_one_pow]
      refine pow_le_pow_left' ?_ _
      have := (v.intValuation_le_pow_iff_mem (π v) 1).mpr (by simpa using hπmem v)
      simpa using this
    have h2 : (∏ w ∈ hIfin.toFinset.erase v, v.intValuation (π w ^ k w)) ≤ 1 :=
      Finset.prod_le_one (fun w _ => v.intValuation_le_one _)
    calc (∏ w ∈ hIfin.toFinset.erase v, v.intValuation (π w ^ k w))
          * v.intValuation (π v ^ k v)
        ≤ 1 * exp (-(k v : ℤ)) := mul_le_mul' h2 h1
      _ = exp (-(k v : ℤ)) := one_mul _
  set Nbar : F := algebraMap (NumberField.RingOfIntegers F) F N with hNbar
  have hmem : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
      algebraMap F (v.adicCompletion F) Nbar * r v ∈ v.adicCompletionIntegers F := by
    intro v
    refine mul_mem ?_ (hr v)
    rw [mem_adicCompletionIntegers, hNbar, valued_algebraMap_eq]
    exact v.intValuation_le_one N
  set g : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨algebraMap F (v.adicCompletion F) Nbar * r v, hmem v⟩ with hgdef
  have hgpi : g ∈ Set.pi I t := by
    intro v hv
    have hvF : v ∈ hIfin.toFinset := hIfin.mem_toFinset.mpr hv
    refine hk v _ (hmem v) ?_
    rw [map_mul, valued_algebraMap_eq]
    calc v.intValuation N * Valued.v (r v)
        ≤ exp (-(k v : ℤ)) * 1 :=
          mul_le_mul' (hNval v hvF) ((mem_adicCompletionIntegers _ _ _).mp (hr v))
      _ = exp (-(k v : ℤ)) := mul_one _
  have hsmg : sm g = algebraMap F 𝔸f Nbar * r := by
    ext w : 1
    have h1 : (sm g) w = algebraMap F (w.adicCompletion F) Nbar * r w := by
      simp [hsmdef, hgdef]
    have h2 : (algebraMap F 𝔸f Nbar * r) w
        = algebraMap F (w.adicCompletion F) Nbar * r w := rfl
    exact h1.trans h2.symm
  have hthis : sm g ∈ U := hsub hgpi
  rwa [hsmg] at hthis

end NumberField.AdelicR2General

open scoped Classical nonZeroDivisors

noncomputable section

namespace NumberField
namespace AdelicR2Density

variable {F : Type*} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (RingOfIntegers F) F
local notation "𝔸f" => FiniteAdeleRing (RingOfIntegers F) F
local notation "𝔸i" => InfiniteAdeleRing F
local notation "E" => mixedSpace F

omit [NumberField F] in
theorem norm_apply_eq_normAtPlace (s : 𝔸i) (w : InfinitePlace F) :
    ‖s w‖ = normAtPlace w (ringEquiv_mixedSpace F s) := by
  by_cases hw : w.IsReal
  · rw [normAtPlace_apply_of_isReal hw, ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (s w)).symm
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw),
      ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (s w)).symm

private lemma fst_algebraMap (ξ : F) :
    (algebraMap F 𝔸 ξ).1 = algebraMap F 𝔸i ξ := rfl

private lemma snd_algebraMap (ξ : F) :
    (algebraMap F 𝔸 ξ).2 = algebraMap F 𝔸f ξ := rfl

private lemma finite_component_algebraMap (ξ : F)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    (algebraMap F 𝔸f ξ) v = algebraMap F (v.adicCompletion F) ξ := rfl

private lemma valued_algebraMap' (v : HeightOneSpectrum (RingOfIntegers F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem hdens_of_board : ∀ a : 𝔸f, ∃ x : F, ∀ v,
    (a - algebraMap F 𝔸f x) v ∈ v.adicCompletionIntegers F := by
  intro a
  have hopen : IsOpen ((fun y : 𝔸f => a - y) ⁻¹' AdelicBox.integralFiniteAdeles (𝓞 F) F) :=
    (AdelicBox.isOpen_integralFiniteAdeles F).preimage
      ((continuous_const.sub continuous_id))
  have hne : ((fun y : 𝔸f => a - y) ⁻¹' AdelicBox.integralFiniteAdeles (𝓞 F) F).Nonempty :=
    ⟨a, by
      show a - a ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F
      rw [sub_self]
      exact fun v => zero_mem _⟩
  obtain ⟨x, hx⟩ := (denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hopen hne
  refine ⟨x, fun v => ?_⟩
  have hx' : (a - algebraMap F 𝔸f x) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := hx
  exact hx' v

theorem exists_principal_add_level (N : RingOfIntegers F) (hN : N ≠ 0) (xf : 𝔸f) :
    ∃ ξ : F, ∃ r : 𝔸f, (∀ v, r v ∈ v.adicCompletionIntegers F) ∧
      xf = algebraMap F 𝔸f ξ
        + algebraMap F 𝔸f (algebraMap (RingOfIntegers F) F N) * r := by
  set Nb : F := algebraMap (RingOfIntegers F) F N with hNb
  have hNb0 : Nb ≠ 0 := fun h => hN (by
    have := IsFractionRing.to_map_eq_zero_iff.mp (hNb ▸ h)
    exact this)
  obtain ⟨k, hk⟩ := hdens_of_board (F := F) xf
  set u : 𝔸f := xf - algebraMap F 𝔸f k with hu
  obtain ⟨k₂, hk₂⟩ := hdens_of_board (F := F) (algebraMap F 𝔸f Nb⁻¹ * u)
  set r : 𝔸f := algebraMap F 𝔸f Nb⁻¹ * u - algebraMap F 𝔸f k₂ with hr
  refine ⟨k + Nb * k₂, r, fun v => hk₂ v, ?_⟩
  have hNbu : algebraMap F 𝔸f Nb * (algebraMap F 𝔸f Nb⁻¹ * u) = u := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hNb0, map_one, one_mul]
  have hsplit : algebraMap F 𝔸f k₂ + r = algebraMap F 𝔸f Nb⁻¹ * u := by
    rw [hr, add_sub_cancel]
  calc xf = algebraMap F 𝔸f k + u := by rw [hu, add_sub_cancel]
    _ = algebraMap F 𝔸f k + algebraMap F 𝔸f Nb * (algebraMap F 𝔸f k₂ + r) := by
        rw [hsplit, hNbu]
    _ = algebraMap F 𝔸f (k + Nb * k₂) + algebraMap F 𝔸f Nb * r := by
        rw [mul_add, map_add, map_mul, add_assoc]

theorem eq_one_of_forall_archSlice_eq_one {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    {w₀ : InfinitePlace F}
    (hslice : ∀ s : w₀.Completion, ψ (AdelicR2Slices.archSlice w₀ s) = 1) :
    ψ = 1 := by
  rw [AddChar.eq_one_iff]
  intro x
  have key : ∀ V ∈ 𝓝 (1 : ℂ), ψ x ∈ V := by
    intro V hV

    have hW : ψ ⁻¹' V ∈ 𝓝 (0 : 𝔸) := by
      refine hψ.continuous.continuousAt.preimage_mem_nhds ?_
      rwa [show ψ (0 : 𝔸) = 1 from AddChar.map_zero_eq_one ψ]
    obtain ⟨Ui, hUi, Uf, hUf, hprod⟩ := mem_nhds_prod_iff.mp hW

    have hUi2 : Ui ∈ Filter.pi (fun v : InfinitePlace F => 𝓝 (0 : v.Completion)) := by
      have hnp : (𝓝 (0 : ∀ v : InfinitePlace F, v.Completion))
          = Filter.pi (fun v : InfinitePlace F => 𝓝 (0 : v.Completion)) := nhds_pi
      exact hnp ▸ hUi
    obtain ⟨I, hIfin, t, ht, hsub⟩ := Filter.mem_pi.mp hUi2
    have hballs : ∀ v : InfinitePlace F, ∃ e : ℝ, 0 < e ∧ Metric.ball (0 : v.Completion) e ⊆ t v :=
      fun v => Metric.mem_nhds_iff.mp (ht v)
    choose ef hef hballs using hballs
    have hne : (Finset.univ : Finset (InfinitePlace F)).Nonempty := Finset.univ_nonempty
    set ε : ℝ := Finset.univ.inf' hne ef with hεdef
    have hε : 0 < ε := (Finset.lt_inf'_iff hne).mpr fun v _ => hef v
    have hεle : ∀ v : InfinitePlace F, ε ≤ ef v := fun v =>
      Finset.inf'_le ef (Finset.mem_univ v)

    obtain ⟨N, hN0, hlevel⟩ :=
      AdelicR2General.exists_level_smul_integral_subset (F := F) hUf
    set Nb : F := algebraMap (RingOfIntegers F) F N with hNb

    obtain ⟨ξ₁, r, hrint, hxf⟩ := exists_principal_add_level N hN0 x.2

    set z : 𝔸i := x.1 - algebraMap F 𝔸i ξ₁ with hz

    have hNb0 : Nb ≠ 0 := fun h => hN0 (IsFractionRing.to_map_eq_zero_iff.mp (hNb ▸ h))
    set J : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ :=
      Units.mk0 (FractionalIdeal.spanSingleton _ Nb)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hNb0) with hJ
    obtain ⟨a, haJ, hclose⟩ := AdelicR2Mesh.exists_mem_sub_normAtPlace_lt_off J w₀
      (ringEquiv_mixedSpace F z) hε

    rw [hJ, Units.val_mk0, FractionalIdeal.mem_spanSingleton] at haJ
    obtain ⟨c, hc⟩ := haJ

    set ξ : F := ξ₁ + a with hξ

    set rest : 𝔸 := x - algebraMap F 𝔸 ξ
      - AdelicR2Slices.archSlice w₀ ((x.1 - algebraMap F 𝔸i ξ) w₀) with hrest
    have hψx : ψ x = ψ rest := by
      have hx' : x = algebraMap F 𝔸 ξ
          + AdelicR2Slices.archSlice w₀ ((x.1 - algebraMap F 𝔸i ξ) w₀) + rest := by
        rw [hrest]; ring
      rw [hx', AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        hψ.principalInvariant ξ, hslice, one_mul, one_mul]

    have hrest_mem : rest ∈ Ui ×ˢ Uf := by
      constructor
      ·
        have harch : rest.1 = (x.1 - algebraMap F 𝔸i ξ)
            - AdelicR2Slices.archSingle w₀ ((x.1 - algebraMap F 𝔸i ξ) w₀) := rfl
        have hw : ∀ w : InfinitePlace F, ‖rest.1 w‖ < ε := by
          intro w
          by_cases hww : w = w₀
          · subst hww
            have h0 : rest.1 w = 0 := by
              rw [harch]
              show (x.1 - algebraMap F 𝔸i ξ) w - Pi.single w ((x.1 - _) w) w = 0
              simp
            rw [h0, norm_zero]
            exact hε
          · have hcomp : rest.1 w = (x.1 - algebraMap F 𝔸i ξ) w := by
              rw [harch]
              show (x.1 - algebraMap F 𝔸i ξ) w - Pi.single w₀ ((x.1 - _) w₀) w = _
              rw [Pi.single_eq_of_ne hww, sub_zero]
            rw [hcomp]

            have hzw : x.1 - algebraMap F 𝔸i ξ = z - algebraMap F 𝔸i a := by
              rw [hz, hξ, map_add, ← sub_sub]
            rw [hzw, norm_apply_eq_normAtPlace, map_sub,
              ← mixedEmbedding_eq_algebraMap_comp]
            exact hclose w hww
        refine hsub fun v _ => ?_
        refine hballs v ?_
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_lt_of_le (hw v) (hεle v)
      ·
        have hsnd : rest.2 = x.2 - algebraMap F 𝔸f ξ := by
          rw [hrest]
          show (x - algebraMap F 𝔸 ξ).2 - (0 : 𝔸f) = _
          rw [sub_zero]
          rfl
        have hfin : rest.2 = algebraMap F 𝔸f Nb * (r - algebraMap F 𝔸f (algebraMap
            (RingOfIntegers F) F c)) := by
          rw [hsnd, hxf, hξ, map_add, mul_sub]
          have hca : algebraMap F 𝔸f Nb * algebraMap F 𝔸f (algebraMap
              (RingOfIntegers F) F c) = algebraMap F 𝔸f a := by
            rw [← map_mul]
            congr 1
            rw [← hc, Algebra.smul_def, mul_comm]
          rw [hca]
          ring
        rw [hfin]
        refine hlevel _ fun v => ?_
        have hr1 : (r - algebraMap F 𝔸f (algebraMap (RingOfIntegers F) F c)) v
            = r v - algebraMap F (v.adicCompletion F) (algebraMap (RingOfIntegers F) F c) :=
          rfl
        rw [hr1]
        refine sub_mem (hrint v) ?_
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          valued_algebraMap' v (algebraMap (RingOfIntegers F) F c)]
        exact v.valuation_le_one c
    rw [hψx]
    exact hprod hrest_mem
  have h1 : (1 : ℂ) ∈ closure {ψ x} :=
    mem_closure_iff_nhds.mpr fun V hV => ⟨ψ x, key V hV, rfl⟩
  rw [closure_singleton, Set.mem_singleton_iff] at h1
  exact h1.symm

end NumberField.AdelicR2Density

open AutomorphicForm Filter Topology FractionalIdeal MeasureTheory
open scoped Classical nonZeroDivisors ENNReal NNReal

noncomputable section

namespace NumberField
namespace AdelicR2Density

variable {F : Type*} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (RingOfIntegers F) F
local notation "𝔸f" => FiniteAdeleRing (RingOfIntegers F) F
local notation "𝔸i" => InfiniteAdeleRing F
local notation "E" => mixedSpace F

theorem exists_mem_pow_notMem {v₀ v : HeightOneSpectrum (RingOfIntegers F)} (hv : v ≠ v₀)
    (m : ℕ) : ∃ y ∈ v₀.asIdeal ^ m, y ∉ v.asIdeal := by
  rw [← SetLike.not_le_iff_exists]
  intro hle
  haveI := v.isPrime
  have h1 : v₀.asIdeal ≤ v.asIdeal := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact absurd (hle (by simp [hm] : (1 : RingOfIntegers F) ∈ v₀.asIdeal ^ m))
        (fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h))
    · exact Ideal.IsPrime.le_of_pow_le hle
  have hmax : v₀.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime v₀.ne_bot v₀.isPrime
  exact hv (HeightOneSpectrum.ext (hmax.eq_of_le v.isPrime.ne_top h1).symm)

def primeNZD (v₀ : HeightOneSpectrum (RingOfIntegers F)) : (Ideal (RingOfIntegers F))⁰ :=
  ⟨v₀.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v₀.ne_bot⟩

theorem valuation_le_one_of_mem_inv_pow {v₀ v : HeightOneSpectrum (RingOfIntegers F)}
    (hv : v ≠ v₀) (m : ℕ) {b : F}
    (hb : b ∈ ((((FractionalIdeal.mk0 F (primeNZD v₀))⁻¹ :
      (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) ^ m :
      (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
      FractionalIdeal (RingOfIntegers F)⁰ F)) :
    v.valuation F b ≤ 1 := by
  obtain ⟨y, hy, hynot⟩ := exists_mem_pow_notMem hv m
  have hyc : algebraMap (RingOfIntegers F) F y
      ∈ (((FractionalIdeal.mk0 F (primeNZD v₀)) ^ m :
        (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
        FractionalIdeal (RingOfIntegers F)⁰ F) := by
    rw [← map_pow, FractionalIdeal.coe_mk0]
    refine (FractionalIdeal.mem_coeIdeal _).mpr ⟨y, ?_, rfl⟩
    simpa [primeNZD, SubmonoidClass.coe_pow] using hy
  have hmem1 : b * algebraMap (RingOfIntegers F) F y
      ∈ (1 : FractionalIdeal (RingOfIntegers F)⁰ F) := by
    have h := FractionalIdeal.mul_mem_mul hb hyc
    rwa [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one] at h
  obtain ⟨c₁, hc₁⟩ := (FractionalIdeal.mem_one_iff _).mp hmem1
  have hvy : v.valuation F (algebraMap (RingOfIntegers F) F y) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (v.intValuation_le_one y) ?_
    by_contra hlt
    push Not at hlt
    exact hynot ((v.intValuation_lt_one_iff_mem y).mp hlt)
  have hchain : v.valuation F b
      * v.valuation F (algebraMap (RingOfIntegers F) F y) ≤ 1 := by
    rw [← map_mul, ← hc₁, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one c₁
  rwa [hvy, mul_one] at hchain

theorem minkowskiBound_eq_absNorm_mul (J : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
    minkowskiBound F J
      = ENNReal.ofReal (absNorm (J : FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ)
        * minkowskiBound F 1 := by
  rw [minkowskiBound, minkowskiBound,
    volume_fundamentalDomain_fractionalIdealLatticeBasis,
    volume_fundamentalDomain_fractionalIdealLatticeBasis (I := 1)]
  rw [show ((1 : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
      FractionalIdeal (RingOfIntegers F)⁰ F) = 1 from Units.val_one, absNorm_one]
  norm_num [mul_assoc]

theorem exists_minkowskiBound_mul_inv_pow_lt (v₀ : HeightOneSpectrum (RingOfIntegers F))
    {Nb : F} (hNb : Nb ≠ 0) {T : ℝ≥0∞} (hT0 : T ≠ 0) :
    ∃ m : ℕ, minkowskiBound F
      (Units.mk0 (FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ Nb)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hNb)
        * ((FractionalIdeal.mk0 F (primeNZD v₀))⁻¹) ^ m) < T := by
  set NbU : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ :=
    Units.mk0 (FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ Nb)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hNb) with hNbU
  set P : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ :=
    FractionalIdeal.mk0 F (primeNZD v₀) with hP
  set B₁ : ℝ≥0∞ := minkowskiBound F 1 with hB₁
  have hB₁top : B₁ ≠ ⊤ := (minkowskiBound_lt_top F 1).ne
  set A₀ : ℝ := (absNorm (NbU : FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ) with hA₀
  set q : ℝ := (absNorm ((P⁻¹ : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
    FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ) with hq
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; exact_mod_cast absNorm_nonneg _
  have hq0 : 0 ≤ q := by rw [hq]; exact_mod_cast absNorm_nonneg _
  have habs : ∀ m : ℕ, (absNorm ((NbU * P⁻¹ ^ m :
      (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
      FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ) = A₀ * q ^ m := by
    intro m
    rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, hA₀, hq]
    push_cast
    ring
  have hNq : (Ideal.absNorm (v₀.asIdeal : Ideal (RingOfIntegers F)) : ℝ) * q = 1 := by
    have h1 : absNorm ((P : FractionalIdeal (RingOfIntegers F)⁰ F))
        * absNorm ((P⁻¹ : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
          FractionalIdeal (RingOfIntegers F)⁰ F) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, absNorm_one]
    have h2 : absNorm ((P : FractionalIdeal (RingOfIntegers F)⁰ F))
        = (Ideal.absNorm (v₀.asIdeal : Ideal (RingOfIntegers F)) : ℚ) := by
      rw [hP, FractionalIdeal.coe_mk0, coeIdeal_absNorm]
      norm_num [primeNZD]
    rw [h2] at h1
    rw [hq]
    exact_mod_cast h1
  have hN2 : 2 ≤ (Ideal.absNorm (v₀.asIdeal : Ideal (RingOfIntegers F)) : ℝ) := by
    have hne0 : Ideal.absNorm (v₀.asIdeal : Ideal (RingOfIntegers F)) ≠ 0 := by
      intro h0
      have hz : absNorm ((P : FractionalIdeal (RingOfIntegers F)⁰ F)) = 0 := by
        rw [hP, FractionalIdeal.coe_mk0, coeIdeal_absNorm]
        norm_num [primeNZD, h0]
      rw [absNorm_eq_zero_iff] at hz
      exact Units.ne_zero P (by rwa [hP] at hz)
    have hne1 : Ideal.absNorm (v₀.asIdeal : Ideal (RingOfIntegers F)) ≠ 1 := by
      intro h1
      exact v₀.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    have h2n : 2 ≤ Ideal.absNorm (v₀.asIdeal : Ideal (RingOfIntegers F)) := by omega
    exact_mod_cast h2n
  have hq1 : q < 1 := by nlinarith
  by_cases hD : T / B₁ = ⊤
  · refine ⟨0, ?_⟩
    rcases ENNReal.div_eq_top.mp hD with ⟨hT, hB⟩ | ⟨hTtop, _⟩
    ·
      rw [minkowskiBound_eq_absNorm_mul, ← hB₁, hB, mul_zero]
      exact pos_iff_ne_zero.mpr hT0
    ·
      rw [minkowskiBound_eq_absNorm_mul, ← hB₁, hTtop, lt_top_iff_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB₁top
  · have hD0 : T / B₁ ≠ 0 := by
      refine ENNReal.div_ne_zero.mpr ⟨hT0, hB₁top⟩
    have hDtop : (T / B₁).toReal > 0 := ENNReal.toReal_pos hD0 hD
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (div_pos hDtop (by linarith : (0 : ℝ) < A₀ + 1)) hq1
    refine ⟨m, ?_⟩
    rw [minkowskiBound_eq_absNorm_mul, ← hB₁, habs m]
    have hlt : A₀ * q ^ m < (T / B₁).toReal := by
      have h1 : A₀ * q ^ m ≤ (A₀ + 1) * q ^ m := by
        have := pow_nonneg hq0 m
        nlinarith
      have h2 : (A₀ + 1) * q ^ m < (T / B₁).toReal := by
        have h3 := mul_lt_mul_of_pos_left hm (by linarith : (0 : ℝ) < A₀ + 1)
        rwa [mul_div_cancel₀ _ (by linarith : (A₀ + 1) ≠ 0)] at h3
      linarith
    have hofr : ENNReal.ofReal (A₀ * q ^ m) < T / B₁ := by
      rw [← ENNReal.ofReal_toReal hD]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr hlt
    have hB0 : B₁ ≠ 0 := fun h => hD (by rw [h, ENNReal.div_zero hT0])
    calc ENNReal.ofReal (A₀ * q ^ m) * B₁
        < (T / B₁) * B₁ := ENNReal.mul_lt_mul_left hB0 hB₁top hofr
      _ = T := ENNReal.div_mul_cancel hB0 hB₁top

theorem convexBodyLT_volume_ne_zero {δ : ℝ} (hδ : 0 < δ) :
    volume (convexBodyLT F (fun _ => δ.toNNReal)) ≠ 0 := by
  rw [convexBodyLT_volume]
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (lt_of_lt_of_le one_pos (one_le_convexBodyLTFactor F)).ne'
  · refine ENNReal.coe_ne_zero.mpr ?_
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    exact pow_ne_zero _ (Real.toNNReal_pos.mpr hδ).ne'

private lemma valued_algebraMap'' (v : HeightOneSpectrum (RingOfIntegers F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

private lemma finSingle_apply_same (v₀ : HeightOneSpectrum (RingOfIntegers F))
    (t : v₀.adicCompletion F) : (AdelicR2Slices.finSingle v₀ t) v₀ = t := by
  show Pi.single v₀ t v₀ = t
  simp

private lemma finSingle_apply_ne {v₀ v : HeightOneSpectrum (RingOfIntegers F)}
    (hv : v ≠ v₀) (t : v₀.adicCompletion F) : (AdelicR2Slices.finSingle v₀ t) v = 0 := by
  show Pi.single v₀ t v = 0
  exact Pi.single_eq_of_ne hv t

theorem eq_one_of_forall_finSlice_eq_one {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    {v₀ : HeightOneSpectrum (RingOfIntegers F)}
    (hslice : ∀ t : v₀.adicCompletion F, ψ (AdelicR2Slices.finSlice v₀ t) = 1) :
    ψ = 1 := by
  rw [AddChar.eq_one_iff]
  intro x
  have key : ∀ V ∈ 𝓝 (1 : ℂ), ψ x ∈ V := by
    intro V hV
    have hW : ψ ⁻¹' V ∈ 𝓝 (0 : 𝔸) := by
      refine hψ.continuous.continuousAt.preimage_mem_nhds ?_
      rwa [show ψ (0 : 𝔸) = 1 from AddChar.map_zero_eq_one ψ]
    obtain ⟨Ui, hUi, Uf, hUf, hprod⟩ := mem_nhds_prod_iff.mp hW
    have hUi2 : Ui ∈ Filter.pi (fun v : InfinitePlace F => 𝓝 (0 : v.Completion)) := by
      have hnp : (𝓝 (0 : ∀ v : InfinitePlace F, v.Completion))
          = Filter.pi (fun v : InfinitePlace F => 𝓝 (0 : v.Completion)) := nhds_pi
      exact hnp ▸ hUi
    obtain ⟨I, hIfin, t, ht, hsub⟩ := Filter.mem_pi.mp hUi2
    have hballs : ∀ v : InfinitePlace F,
        ∃ e : ℝ, 0 < e ∧ Metric.ball (0 : v.Completion) e ⊆ t v :=
      fun v => Metric.mem_nhds_iff.mp (ht v)
    choose ef hef hballs using hballs
    have hne : (Finset.univ : Finset (InfinitePlace F)).Nonempty := Finset.univ_nonempty
    set ε : ℝ := Finset.univ.inf' hne ef with hεdef
    have hε : 0 < ε := (Finset.lt_inf'_iff hne).mpr fun v _ => hef v
    have hεle : ∀ v : InfinitePlace F, ε ≤ ef v := fun v =>
      Finset.inf'_le ef (Finset.mem_univ v)
    obtain ⟨N, hN0, hlevel⟩ :=
      AdelicR2General.exists_level_smul_integral_subset (F := F) hUf
    set Nb : F := algebraMap (RingOfIntegers F) F N with hNb
    have hNb0 : Nb ≠ 0 := fun h => hN0 (IsFractionRing.to_map_eq_zero_iff.mp (hNb ▸ h))
    obtain ⟨ξ₁, r, hrint, hxf⟩ := exists_principal_add_level N hN0 x.2
    set z : 𝔸i := x.1 - algebraMap F 𝔸i ξ₁ with hz

    have hC : 0 < AdelicR2Mesh.latticeC F + 1 := by
      linarith [AdelicR2Mesh.latticeC_nonneg F]
    set δ : ℝ := ε / (AdelicR2Mesh.latticeC F + 1) with hδdef
    have hδ : 0 < δ := div_pos hε hC
    obtain ⟨m, hm⟩ := exists_minkowskiBound_mul_inv_pow_lt v₀ hNb0
      (T := volume (convexBodyLT F (fun _ => δ.toNNReal)))
      (convexBodyLT_volume_ne_zero hδ)
    obtain ⟨a, haJ, hclose⟩ := AdelicR2Mesh.exists_mem_sub_normAtPlace_lt_all _ hδ hm
      (ringEquiv_mixedSpace F z)

    have hbmem : Nb⁻¹ * a ∈ ((((FractionalIdeal.mk0 F (primeNZD v₀))⁻¹ :
        (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) ^ m :
        (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ) :
        FractionalIdeal (RingOfIntegers F)⁰ F) := by
      have h1 : Nb⁻¹ ∈ FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ Nb⁻¹ :=
        FractionalIdeal.mem_spanSingleton_self _ _
      have h2 := FractionalIdeal.mul_mem_mul h1 haJ
      rwa [Units.val_mul, Units.val_mk0, ← mul_assoc,
        FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hNb0,
        FractionalIdeal.spanSingleton_one, one_mul] at h2
    set b : F := Nb⁻¹ * a with hb
    have hab : a = Nb * b := by rw [hb, ← mul_assoc, mul_inv_cancel₀ hNb0, one_mul]

    set ξ : F := ξ₁ + a with hξ
    set w' : 𝔸f := r - algebraMap F 𝔸f b with hw'
    set rest : 𝔸 := x - algebraMap F 𝔸 ξ
      - AdelicR2Slices.finSlice v₀ ((x.2 - algebraMap F 𝔸f ξ) v₀) with hrest
    have hψx : ψ x = ψ rest := by
      have hx' : x = algebraMap F 𝔸 ξ
          + AdelicR2Slices.finSlice v₀ ((x.2 - algebraMap F 𝔸f ξ) v₀) + rest := by
        rw [hrest]; ring
      rw [hx', AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        hψ.principalInvariant ξ, hslice, one_mul, one_mul]
    have hrest_mem : rest ∈ Ui ×ˢ Uf := by
      constructor
      ·
        have harch : rest.1 = x.1 - algebraMap F 𝔸i ξ := by
          rw [hrest]
          show (x - algebraMap F 𝔸 ξ).1 - (0 : 𝔸i) = _
          rw [sub_zero]
          rfl
        have hw : ∀ w : InfinitePlace F, ‖rest.1 w‖ < ε := by
          intro w
          have hzw : x.1 - algebraMap F 𝔸i ξ = z - algebraMap F 𝔸i a := by
            rw [hz, hξ, map_add, ← sub_sub]
          rw [harch, hzw, norm_apply_eq_normAtPlace, map_sub,
            ← mixedEmbedding_eq_algebraMap_comp]
          calc normAtPlace w (ringEquiv_mixedSpace F z - mixedEmbedding F a)
              < δ * (AdelicR2Mesh.latticeC F + 1) := hclose w
            _ = ε := by rw [hδdef, div_mul_cancel₀ _ hC.ne']
        refine hsub fun v _ => ?_
        refine hballs v ?_
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_lt_of_le (hw v) (hεle v)
      ·
        have hsnd0 : x.2 - algebraMap F 𝔸f ξ = algebraMap F 𝔸f Nb * w' := by
          rw [hxf, hξ, map_add, hw', mul_sub]
          have hca : algebraMap F 𝔸f Nb * algebraMap F 𝔸f b = algebraMap F 𝔸f a := by
            rw [← map_mul, ← hab]
          rw [hca]
          ring
        have hsnd : rest.2 = algebraMap F 𝔸f Nb
            * (w' - AdelicR2Slices.finSingle v₀ (w' v₀)) := by
          have h1 : rest.2 = (x.2 - algebraMap F 𝔸f ξ)
              - AdelicR2Slices.finSingle v₀ ((x.2 - algebraMap F 𝔸f ξ) v₀) := by
            rw [hrest]
            rfl
          have h2 : AdelicR2Slices.finSingle v₀ ((algebraMap F 𝔸f Nb * w') v₀)
              = algebraMap F 𝔸f Nb * AdelicR2Slices.finSingle v₀ (w' v₀) := by
            have h3 : (algebraMap F 𝔸f Nb * w') v₀
                = (algebraMap F 𝔸f Nb) v₀ * w' v₀ := rfl
            rw [h3]
            exact (AdelicR2Slices.mul_finSingle (algebraMap F 𝔸f Nb) v₀ (w' v₀)).symm
          rw [h1, hsnd0, h2]
          exact (mul_sub (algebraMap F 𝔸f Nb) w'
            (AdelicR2Slices.finSingle v₀ (w' v₀))).symm
        rw [hsnd]
        refine hlevel _ fun v => ?_
        by_cases hvv : v = v₀
        · subst hvv
          have h0 : (w' - AdelicR2Slices.finSingle v (w' v)) v = 0 := by
            have : (w' - AdelicR2Slices.finSingle v (w' v)) v
                = w' v - (AdelicR2Slices.finSingle v (w' v)) v := rfl
            rw [this, finSingle_apply_same, sub_self]
          rw [h0]
          exact zero_mem _
        · have hcomp : (w' - AdelicR2Slices.finSingle v₀ (w' v₀)) v
              = r v - algebraMap F (v.adicCompletion F) b := by
            have h1 : (w' - AdelicR2Slices.finSingle v₀ (w' v₀)) v
                = w' v - (AdelicR2Slices.finSingle v₀ (w' v₀)) v := rfl
            rw [h1, finSingle_apply_ne hvv, sub_zero, hw']
            rfl
          rw [hcomp]
          refine sub_mem (hrint v) ?_
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
            valued_algebraMap'' v b]
          exact valuation_le_one_of_mem_inv_pow hvv m hbmem
    rw [hψx]
    exact hprod hrest_mem
  have h1 : (1 : ℂ) ∈ closure {ψ x} :=
    mem_closure_iff_nhds.mpr fun V hV => ⟨ψ x, key V hV, rfl⟩
  rw [closure_singleton, Set.mem_singleton_iff] at h1
  exact h1.symm

end NumberField.AdelicR2Density


noncomputable section

namespace NumberField
namespace AdelicR2Global

variable (F : Type*) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

variable {F}

theorem perp_principal {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (k : F) :
    ∀ ξ : F, ψ (ι k * ι ξ) = 1 := fun ξ => by
  rw [← map_mul]
  exact hψ.principalInvariant (k * ξ)

theorem perp_add {ψ : AddChar 𝔸 ℂ} {y z : 𝔸} (hy : ∀ ξ : F, ψ (y * ι ξ) = 1)
    (hz : ∀ ξ : F, ψ (z * ι ξ) = 1) : ∀ ξ : F, ψ ((y + z) * ι ξ) = 1 := fun ξ => by
  rw [add_mul, AddChar.map_add_eq_mul, hy ξ, hz ξ, one_mul]

theorem perp_neg {ψ : AddChar 𝔸 ℂ} {y : 𝔸} (hy : ∀ ξ : F, ψ (y * ι ξ) = 1) :
    ∀ ξ : F, ψ ((-y) * ι ξ) = 1 := fun ξ => by
  rw [neg_mul, AddChar.map_neg_eq_inv, hy ξ, inv_one]

theorem perp_sub {ψ : AddChar 𝔸 ℂ} {y z : 𝔸} (hy : ∀ ξ : F, ψ (y * ι ξ) = 1)
    (hz : ∀ ξ : F, ψ (z * ι ξ) = 1) : ∀ ξ : F, ψ ((y - z) * ι ξ) = 1 := by
  rw [sub_eq_add_neg]
  exact perp_add hy (perp_neg hz)

theorem perp_principal_mul {ψ : AddChar 𝔸 ℂ} {y : 𝔸} (hy : ∀ ξ : F, ψ (y * ι ξ) = 1)
    (c : F) : ∀ ξ : F, ψ (ι c * y * ι ξ) = 1 := fun ξ => by
  have h : ι c * y * ι ξ = y * ι (c * ξ) := by
    rw [map_mul]
    ring
  rw [h]
  exact hy (c * ξ)

theorem isClosed_perp {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    IsClosed {y : 𝔸 | ∀ ξ : F, ψ (y * ι ξ) = 1} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter fun ξ =>
    isClosed_eq (hψ.continuous.comp (continuous_mul_const (ι ξ))) continuous_const


theorem exists_nhds_forall_perp_imp_global {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ U ∈ 𝓝 (0 : 𝔸), ∀ y ∈ U, (∀ ξ : F, ψ (y * ι ξ) = 1) → ∀ x : 𝔸, ψ (y * x) = 1 := by
  obtain ⟨C, hCcomp, hboxC⟩ := AdelicBox.exists_isCompact_adelicBox_subset F

  have hopen : IsOpen {p : 𝔸 × 𝔸 | ‖ψ (p.1 * p.2) - 1‖ < 2⁻¹} := by
    have hc : Continuous fun p : 𝔸 × 𝔸 => ‖ψ (p.1 * p.2) - 1‖ :=
      ((hψ.continuous.comp continuous_mul).sub continuous_const).norm
    exact isOpen_lt hc continuous_const
  have hsub : Set.singleton (0 : 𝔸) ×ˢ C ⊆ {p : 𝔸 × 𝔸 | ‖ψ (p.1 * p.2) - 1‖ < 2⁻¹} := by
    rintro ⟨y, b⟩ ⟨hy, -⟩
    rcases hy with rfl
    simp [AddChar.map_zero_eq_one]
  obtain ⟨U, V, hUopen, -, hU0, hCV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hCcomp hopen hsub
  refine ⟨U, hUopen.mem_nhds (hU0 rfl), fun y hyU hyperp x => ?_⟩

  refine NumberField.AdelicR2.eq_one_of_forall_pow_norm_sub_one_le fun n => ?_

  obtain ⟨k, hk, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F (n • x)

  have hsm : y * (n • x) = n • (y * x) := mul_smul_comm n y x
  have h2 : ψ (y * (n • x)) = ψ (y * x) ^ n := by
    rw [hsm]
    exact AddChar.map_nsmul_eq_pow ψ n (y * x)
  have hpow : ψ (y * x) ^ n = ψ (y * (ι k + n • x)) := by
    rw [mul_add, AddChar.map_add_eq_mul, hyperp k, one_mul, h2]
  rw [hpow]
  have hlt := hUV (Set.mk_mem_prod hyU (hCV (hboxC hk)))
  simp only [Set.mem_setOf_eq] at hlt
  exact le_of_lt hlt

theorem mem_range_algebraMap_of_forall_apply_mul_eq_one_of_faithful
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    (hfaith : ∀ y : 𝔸, (∀ x : 𝔸, ψ (y * x) = 1) → y = 0)
    (y : 𝔸) (hy : ∀ ξ : F, ψ (y * ι ξ) = 1) : y ∈ Set.range ι := by
  classical
  obtain ⟨U, hU, hUkill⟩ := exists_nhds_forall_perp_imp_global hψ
  obtain ⟨C, hCcomp, hboxC⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  obtain ⟨k₀, hk₀, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F y
  set b : 𝔸 := ι k₀ + y with hbdef
  have hbperp : ∀ ξ : F, ψ (b * ι ξ) = 1 := perp_add (perp_principal hψ k₀) hy
  suffices hb : b ∈ Set.range ι by
    obtain ⟨s, hs⟩ := hb
    exact ⟨s - k₀, by rw [map_sub, hs, hbdef]; ring⟩
  set S : Set 𝔸 := C ∩ {z : 𝔸 | ∀ ξ : F, ψ (z * ι ξ) = 1} with hSdef
  have hScomp : IsCompact S := hCcomp.inter_right (isClosed_perp hψ)
  have hSsep : ∀ z ∈ S, ∀ w ∈ S, w - z ∈ U → w = z := by
    rintro z ⟨-, hzperp⟩ w ⟨-, hwperp⟩ hwz
    exact sub_eq_zero.mp (hfaith _ (hUkill _ hwz (perp_sub hwperp hzperp)))
  have hSfin : S.Finite := by
    by_contra hinf
    obtain ⟨z, hzS, hne⟩ := exists_nhds_ne_inf_principal_neBot hScomp hinf
    have hmem : {w : 𝔸 | w - z ∈ U} ∈ 𝓝 z := by
      have hc : ContinuousAt (fun w : 𝔸 => w - z) z :=
        (continuous_id.sub continuous_const).continuousAt
      apply hc.preimage_mem_nhds
      simpa using hU
    have hmem3 : ({w : 𝔸 | w - z ∈ U} ∩ ({z}ᶜ ∩ S)).Nonempty :=
      Filter.nonempty_of_mem (Filter.inter_mem
        (Filter.mem_inf_of_left (mem_nhdsWithin_of_mem_nhds hmem))
        (Filter.inter_mem (Filter.mem_inf_of_left self_mem_nhdsWithin)
          (Filter.mem_inf_of_right (Filter.mem_principal_self S))))
    obtain ⟨w, hwU, hwne, hwS⟩ := hmem3
    exact hwne (hSsep z hzS w hwS hwU)
  have hbox : ∀ c : F, ∃ k : F, ι k + ι c * b ∈ AdelicBox.adelicBox F := fun c =>
    (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F (ι c * b)).exists
  choose kc hkc using hbox
  have hmaps : Set.MapsTo (fun c : F => ι (kc c) + ι c * b) Set.univ S := by
    intro c _
    exact ⟨hboxC (hkc c), perp_add (perp_principal hψ (kc c)) (perp_principal_mul hbperp c)⟩
  obtain ⟨c, -, c', -, hcc, heq⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hSfin
  have hkey : ι (c - c') * b = ι (kc c' - kc c) := by
    rw [map_sub, map_sub, sub_mul]
    linear_combination heq
  have hnz : c - c' ≠ 0 := sub_ne_zero.mpr hcc
  refine ⟨(c - c')⁻¹ * (kc c' - kc c), ?_⟩
  rw [map_mul]
  calc ι ((c - c')⁻¹) * ι (kc c' - kc c)
      = ι ((c - c')⁻¹) * (ι (c - c') * b) := by rw [hkey]
    _ = b := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hnz, map_one, one_mul]

end NumberField.AdelicR2Global


noncomputable section

namespace NumberField
namespace AdelicR2Density

variable {F : Type*} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (RingOfIntegers F) F

theorem hfaith_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∀ y : 𝔸, (∀ x : 𝔸, ψ (y * x) = 1) → y = 0 := by
  intro y hy
  by_contra hy0
  rcases AdelicR2Slices.nonzero_arch_or_fin hy0 with ⟨w₀, hw₀⟩ | ⟨v₀, hv₀⟩
  · exact hψ.nontrivial (eq_one_of_forall_archSlice_eq_one hψ
      (fun s => AdelicR2Slices.forall_archSlice_eq_one hy hw₀ s))
  · exact hψ.nontrivial (eq_one_of_forall_finSlice_eq_one hψ
      (fun t => AdelicR2Slices.forall_finSlice_eq_one hy hv₀ t))

theorem mem_range_algebraMap_of_forall_apply_mul_eq_one_impl {ψ : AddChar 𝔸 ℂ}
    (hψ : IsGlobalAddChar F ψ) (y : 𝔸)
    (hy : ∀ ξ : F, ψ (y * algebraMap F 𝔸 ξ) = 1) :
    y ∈ Set.range (algebraMap F 𝔸) :=
  AdelicR2Global.mem_range_algebraMap_of_forall_apply_mul_eq_one_of_faithful hψ
    (hfaith_of_isGlobalAddChar hψ) y hy

example {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (y : 𝔸)
    (hy : ∀ ξ : F, ψ (y * algebraMap F 𝔸 ξ) = 1) :
    y ∈ Set.range (algebraMap F 𝔸) :=
  mem_range_algebraMap_of_forall_apply_mul_eq_one_impl hψ y hy

end NumberField.AdelicR2Density

public theorem NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one
    (F : Type*) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : AutomorphicForm.IsGlobalAddChar F ψ)
    (y : AdeleRing (𝓞 F) F)
    (hy : ∀ ξ : F, ψ (y * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) :
    y ∈ Set.range (algebraMap F (AdeleRing (𝓞 F) F)) :=
  NumberField.AdelicR2Density.mem_range_algebraMap_of_forall_apply_mul_eq_one_impl hψ y hy

open NumberField IsDedekindDomain NumberField.AdelicBox
open scoped Pointwise

noncomputable section

namespace M4aP3B
namespace Rows
namespace DiscreteAdele

variable (F : Type*) [Field F] [NumberField F]

theorem fst_algebraMap (ξ : F) :
    (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl

theorem zero_mem_integralFiniteAdeles' :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun _ => zero_mem _

theorem finite_setOf_algebraMap_mem {C : Set (AdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C}.Finite := by
  classical

  have hO : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hCf : IsCompact (Prod.snd '' C) := hC.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hCf.elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' integralFiniteAdeles (𝓞 F) F) fun y _ =>
      (hO.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simpa only [Set.mem_preimage, Pi.sub_apply, id_eq, sub_self] using zero_mem_integralFiniteAdeles' F)

  have hCinf : IsCompact (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) :=
    (hC.image continuous_fst).image (continuous_ringEquiv_mixedSpace F)
  have hD : IsCompact ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F =>
      p.1 - p.2) '' ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)))) :=
    (hCinf.prod hCinf).image (continuous_fst.sub continuous_snd)

  haveI : DiscreteTopology (mixedEmbedding.integerLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))
  have hL : ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F => p.1 - p.2) ''
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C))) ∩
      (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))).Finite := by
    refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hD.isBounded ?_
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discrete

  have hT : ∀ y : FiniteAdeleRing (𝓞 F) F,
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F}.Finite := by
    intro y
    rcases Set.eq_empty_or_nonempty {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F} with h0 | ⟨ξ₀, hξ₀C, hξ₀y⟩
    · rw [h0]; exact Set.finite_empty
    refine (hL.preimage (f := fun ξ : F => mixedEmbedding F (ξ - ξ₀)) fun a _ b _ h =>
      sub_left_inj.1 (mixedEmbedding_injective F h)).subset ?_
    rintro ξ ⟨hξC, hξy⟩
    refine ⟨?_, ?_⟩
    ·
      refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1,
          InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1),
        ⟨⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ).1, ⟨_, hξC, rfl⟩, rfl⟩,
          ⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1, ⟨_, hξ₀C, rfl⟩, rfl⟩⟩, ?_⟩
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
          - InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1
        = mixedEmbedding F (ξ - ξ₀)
      rw [map_sub, fst_algebraMap, fst_algebraMap, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    ·
      have h2 : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2
          = (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).2 := by
        rw [map_sub]; rfl
      have hdiff : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2 ∈ integralFiniteAdeles (𝓞 F) F := by
        rw [h2, ← sub_sub_sub_cancel_right _ _ y]
        exact fun v => sub_mem (hξy v) (hξ₀y v)
      have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ - ξ₀) ≤ 1 := fun v => by
        have h := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hdiff v)
        rwa [NumberField.AdeleRing.algebraMap_snd_apply,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
      obtain ⟨o, ho⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ - ξ₀) hval
      show mixedEmbedding F (ξ - ξ₀) ∈ (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))
      rw [← ho]
      exact ⟨o, rfl⟩

  refine (t.finite_toSet.biUnion fun y _ => hT y).subset fun ξ hξ => ?_
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 ∈ Prod.snd '' C := ⟨_, hξ, rfl⟩
  obtain ⟨y, hy, hyO⟩ := Set.mem_iUnion₂.1 (hcover h2)
  exact Set.mem_iUnion₂.2 ⟨y, hy, hξ, hyO⟩

theorem finite_setOf_algebraMap_mem_of_isCompact_impl (F : Type*) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite :=
  finite_setOf_algebraMap_mem F hC

theorem gate_empty (F : Type*) [Field F] [NumberField F] :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (∅ : Set (AdeleRing (𝓞 F) F))} = ∅ := by
  ext ξ; simp

theorem gate_univ_infinite (F : Type*) [Field F] [NumberField F] :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (Set.univ : Set (AdeleRing (𝓞 F) F))}.Infinite := by
  simp only [Set.mem_univ, Set.setOf_true]
  exact Set.infinite_univ

end M4aP3B.Rows.DiscreteAdele

end

public theorem NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact
    (F : Type*) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite :=
  M4aP3B.Rows.DiscreteAdele.finite_setOf_algebraMap_mem_of_isCompact_impl F hC

public theorem NumberField.AdeleRing.compactSpace_quotient_principalSubgroup
    (F : Type*) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset F
  rw [← isCompact_univ_iff]
  have hcont : Continuous
      (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) :=
    continuous_quot_mk
  have hsurj : (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) '' C
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨x, rfl⟩ := Quot.exists_rep y
    obtain ⟨k, hk, -⟩ := NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F x
    refine ⟨algebraMap F (AdeleRing (𝓞 F) F) k + x, hsub hk, ?_⟩
    refine (QuotientAddGroup.eq (s := AdeleRing.principalSubgroup (𝓞 F) F)).mpr ?_
    refine ⟨-k, ?_⟩
    simp only [map_neg]
    abel
  rw [← hsurj]
  exact hC.image hcont
