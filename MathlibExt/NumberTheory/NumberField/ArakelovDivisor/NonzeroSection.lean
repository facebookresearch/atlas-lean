/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.ArakelovDivisor
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# A nonzero section of a large Arakelov divisor

Let `K` be a number field with `s` complex places and discriminant `D_K`.
For an Arakelov divisor `D = (I, (f_w))`, its size is
`‖D‖ = (∏_w f_w ^ mult w) / |Norm I|`, and its section set is
`L(D) = {x ∈ I | w x ≤ f_w for all w}`.

This is Proposition 15.9 of ATLAS `NumberTheoryI`, Section 15.1:
if `‖D‖ > B_K := (2 / π) ^ s * √|D_K|`, then `L(D)` contains a nonzero
element. The proof is Minkowski's convex body theorem
(`NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt`) applied to the
box `w x < f_w`, after the volume comparison
`minkowskiBound < volume (convexBodyLT)`, which is exactly the size
hypothesis once the covolume of the ring of integers
(`mixedEmbedding.covolume_integerLattice`) and the volume of the box
(`mixedEmbedding.convexBodyLT_volume`) are expanded.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure
open scoped NumberField nonZeroDivisors NNReal ENNReal

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Large Arakelov divisors have a nonzero section.** Let $K$ be a number field with $s$
complex places and discriminant $d_K$, and let $D$ be an Arakelov divisor on $K$. If the size
of $D$ is strictly greater than $(2/\pi)^s \sqrt{|d_K|}$, then the section set of $D$ contains
a nonzero element of $K$.

Source: Proposition 15.9 of ATLAS `NumberTheoryI`. -/
theorem ArakelovDivisor.exists_ne_zero_mem_sectionSet_of_size_gt
    (D : ArakelovDivisor K)
    (hD : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)| <
      (ArakelovDivisor.sizeHom K D : ℝ)) :
    ∃ x ∈ D.sectionSet, x ≠ 0 := by
  classical
  -- The archimedean radii as nonnegative reals, for the convex body.
  set f : InfinitePlace K → ℝ≥0 := fun w => Real.toNNReal (D.2 w : ℝ) with hf_def
  have hf_coe : ∀ w, (f w : ℝ) = (D.2 w : ℝ) :=
    fun w => Real.coe_toNNReal _ (le_of_lt (D.2 w).2)
  have hP_pos : 0 < ∏ w, (D.2 w : ℝ) ^ w.mult :=
    Finset.prod_pos (fun w _ => pow_pos (D.2 w).2 _)
  have hAbs_pos : (0 : ℝ) <
      ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) := by
    rw [Rat.cast_pos]
    exact FractionalIdeal.absNorm_units_pos D.1
  -- The size hypothesis, cleared of its denominator.
  have hD' : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)| *
        ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) <
      ∏ w, (D.2 w : ℝ) ^ w.mult := by
    rw [ArakelovDivisor.sizeHom_coe] at hD
    exact (lt_div_iff₀ hAbs_pos).mp hD
  -- The real-number core of the volume comparison.
  have hkey : ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)| * (2 : ℝ) ^ Module.finrank ℚ K <
      (2 : ℝ) ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K *
        ∏ w, (D.2 w : ℝ) ^ w.mult := by
    have hrank : Module.finrank ℚ K =
        InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K :=
      (InfinitePlace.card_add_two_mul_card_eq_rank K).symm
    have hpi : (0 : ℝ) < Real.pi ^ InfinitePlace.nrComplexPlaces K :=
      pow_pos Real.pi_pos _
    have h2r : (0 : ℝ) < (2 : ℝ) ^ InfinitePlace.nrRealPlaces K :=
      pow_pos two_pos _
    have h1 : (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)| *
          ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) <
        Real.pi ^ InfinitePlace.nrComplexPlaces K * ∏ w, (D.2 w : ℝ) ^ w.mult := by
      rw [div_pow] at hD'
      have h2 : (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)| *
            ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
          ((2 ^ InfinitePlace.nrComplexPlaces K / Real.pi ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)|) *
            ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)) *
            Real.pi ^ InfinitePlace.nrComplexPlaces K := by
        field_simp
      rw [h2]
      calc ((2 ^ InfinitePlace.nrComplexPlaces K / Real.pi ^ InfinitePlace.nrComplexPlaces K *
              Real.sqrt |(NumberField.discr K : ℝ)|) *
              ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)) *
            Real.pi ^ InfinitePlace.nrComplexPlaces K
          < (∏ w, (D.2 w : ℝ) ^ w.mult) * Real.pi ^ InfinitePlace.nrComplexPlaces K :=
        mul_lt_mul_of_pos_right hD' hpi
        _ = Real.pi ^ InfinitePlace.nrComplexPlaces K * ∏ w, (D.2 w : ℝ) ^ w.mult :=
        mul_comm _ _
    have hpow : (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * ((2 : ℝ) ^ 2) ^
        InfinitePlace.nrComplexPlaces K = (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by
      rw [← mul_pow]
      norm_num
    rw [hrank, pow_add, pow_mul]
    calc ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) *
          (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)| *
          ((2 : ℝ) ^ InfinitePlace.nrRealPlaces K * (2 ^ 2) ^ InfinitePlace.nrComplexPlaces K)
        = ((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)| *
            ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)) *
          (2 : ℝ) ^ InfinitePlace.nrRealPlaces K := by
          rw [← hpow]
          ring
      _ < (Real.pi ^ InfinitePlace.nrComplexPlaces K *
          ∏ w, (D.2 w : ℝ) ^ w.mult) * (2 : ℝ) ^ InfinitePlace.nrRealPlaces K :=
        mul_lt_mul_of_pos_right h1 h2r
      _ = (2 : ℝ) ^ InfinitePlace.nrRealPlaces K *
          Real.pi ^ InfinitePlace.nrComplexPlaces K *
          ∏ w, (D.2 w : ℝ) ^ w.mult := by ring
  -- The Minkowski bound, as an `ENNReal.ofReal`.
  have hfund : MeasureTheory.volume
        (ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis K)) =
      ENNReal.ofReal ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)|) := by
    have hfin : MeasureTheory.volume
        (ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis K)) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin]
    congr 1
    have hcov := NumberField.mixedEmbedding.covolume_integerLattice K
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (NumberField.mixedEmbedding.fundamentalDomain_integerLattice K),
      MeasureTheory.measureReal_def] at hcov
    exact hcov
  have hmb : NumberField.mixedEmbedding.minkowskiBound K D.1 =
      ENNReal.ofReal (((FractionalIdeal.absNorm
        (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)| * (2 : ℝ) ^ Module.finrank ℚ K) := by
    unfold NumberField.mixedEmbedding.minkowskiBound
    rw [NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
      hfund, NumberField.mixedEmbedding.finrank]
    have h2pow : (2 : ℝ≥0∞) ^ Module.finrank ℚ K =
        ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℚ K) := by
      rw [← ENNReal.ofReal_ofNat (n := 2),
        ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h2pow]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  -- The volume of the box, as an `ENNReal.ofReal`.
  have hvol : MeasureTheory.volume (NumberField.mixedEmbedding.convexBodyLT K f) =
      ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces K *
        Real.pi ^ InfinitePlace.nrComplexPlaces K *
        ∏ w, (D.2 w : ℝ) ^ w.mult) := by
    rw [NumberField.mixedEmbedding.convexBodyLT_volume]
    have hfactor : ((NumberField.mixedEmbedding.convexBodyLTFactor K : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces K *
          Real.pi ^ InfinitePlace.nrComplexPlaces K) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    have hprod : ((∏ w, f w ^ w.mult : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (∏ w, (D.2 w : ℝ) ^ w.mult) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [NNReal.coe_prod, NNReal.coe_pow, hf_coe]
    rw [hfactor, hprod, ← ENNReal.ofReal_mul (by positivity)]
  -- The volume comparison, then Minkowski's theorem.
  have hlt : NumberField.mixedEmbedding.minkowskiBound K D.1 <
      MeasureTheory.volume (NumberField.mixedEmbedding.convexBodyLT K f) := by
    rw [hmb, hvol]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (by positivity : 0 < (2 : ℝ) ^ InfinitePlace.nrRealPlaces K *
        Real.pi ^ InfinitePlace.nrComplexPlaces K *
        ∏ w, (D.2 w : ℝ) ^ w.mult)).mpr hkey
  obtain ⟨a, ha_mem, ha_ne, ha_lt⟩ :=
    NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt K D.1 hlt
  exact ⟨a, ⟨ha_mem, fun w => le_of_lt ((hf_coe w) ▸ ha_lt w)⟩, ha_ne⟩

end NumberField
