/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.MeasureTheory.Measure.RegularDominated
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Vector measures with regular total variation

This file records regularity of the total variation as a proposition, rather than a global
instance, and proves its stability under the standard vector-measure operations.  It also relates
regular variation of signed measures to regularity of their Jordan parts and regular variation of
complex measures to that of their real and imaginary parts.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace MeasureTheory

noncomputable section

universe u v

namespace VectorMeasure

variable {X : Type u} {V : Type v}
variable [TopologicalSpace X] [MeasurableSpace X]
variable [NormedAddCommGroup V]

/-- A vector measure has regular variation when its total-variation measure is regular. -/
def HasRegularVariation (μ : VectorMeasure X V) : Prop :=
  μ.variation.Regular

namespace HasRegularVariation

/-- The zero vector measure has regular variation. -/
theorem zero : HasRegularVariation (0 : VectorMeasure X V) := by
  rw [HasRegularVariation, variation_zero]
  infer_instance

/-- Negating a vector measure preserves regularity of its variation. -/
theorem neg {μ : VectorMeasure X V} (hμ : HasRegularVariation μ) :
    HasRegularVariation (-μ) := by
  rw [HasRegularVariation, variation_neg]
  exact hμ

/-- Adding vector measures with finite regular variations preserves regular variation. -/
theorem add [R1Space X] [BorelSpace X] {μ ν : VectorMeasure X V}
    (hμ : HasRegularVariation μ)
    (hν : HasRegularVariation ν) [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] : HasRegularVariation (μ + ν) := by
  let : μ.variation.Regular := hμ
  let : ν.variation.Regular := hν
  let : (μ.variation + ν.variation).Regular :=
    Measure.Regular.add_of_finite μ.variation ν.variation
  exact Measure.Regular.of_le variation_add_le

/-- Subtracting vector measures with finite regular variations preserves regular variation. -/
theorem sub [R1Space X] [BorelSpace X] {μ ν : VectorMeasure X V}
    (hμ : HasRegularVariation μ)
    (hν : HasRegularVariation ν) [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] : HasRegularVariation (μ - ν) := by
  let : μ.variation.Regular := hμ
  let : ν.variation.Regular := hν
  let : (μ.variation + ν.variation).Regular :=
    Measure.Regular.add_of_finite μ.variation ν.variation
  exact Measure.Regular.of_le variation_sub_le

/-- Scalar multiplication preserves regular variation of a vector measure. -/
theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V]
    {μ : VectorMeasure X V} (hμ : HasRegularVariation μ) (c : 𝕜) :
    HasRegularVariation (c • μ) := by
  let : μ.variation.Regular := hμ
  rw [HasRegularVariation, variation_smul]
  infer_instance

/-- A finite sum of vector measures with finite regular variations has regular variation. -/
theorem finsetSum [R1Space X] [BorelSpace X] {ι : Type*}
    (s : Finset ι) (μ : ι → VectorMeasure X V)
    (hfinite : ∀ i ∈ s, IsFiniteMeasure (μ i).variation)
    (hμ : ∀ i ∈ s, HasRegularVariation (μ i)) :
    HasRegularVariation (∑ i ∈ s, μ i) := by
  classical
  have hregularFinite : ∀ t : Finset ι,
      (∀ i ∈ t, IsFiniteMeasure (μ i).variation) →
      (∀ i ∈ t, HasRegularVariation (μ i)) →
      (∑ i ∈ t, (μ i).variation).Regular ∧
        IsFiniteMeasure (∑ i ∈ t, (μ i).variation) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _ _
        simp only [Finset.sum_empty]
        constructor <;> infer_instance
    | @insert i t hit ih =>
        intro htfinite htregular
        let _ : IsFiniteMeasure (μ i).variation :=
          htfinite i (Finset.mem_insert_self i t)
        let _ : (μ i).variation.Regular :=
          htregular i (Finset.mem_insert_self i t)
        obtain ⟨htRegular, htFinite⟩ := ih
          (fun j hj ↦ htfinite j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ htregular j (Finset.mem_insert_of_mem hj))
        let _ : (∑ j ∈ t, (μ j).variation).Regular := htRegular
        let _ : IsFiniteMeasure (∑ j ∈ t, (μ j).variation) := htFinite
        rw [Finset.sum_insert hit]
        exact ⟨Measure.Regular.add_of_finite _ _, by infer_instance⟩
  obtain ⟨hregular, hfiniteSum⟩ := hregularFinite s hfinite hμ
  let _ : (∑ i ∈ s, (μ i).variation).Regular := hregular
  let _ : IsFiniteMeasure (∑ i ∈ s, (μ i).variation) := hfiniteSum
  exact Measure.Regular.of_le (variation_finsetSum_le s μ)

end HasRegularVariation
end VectorMeasure

namespace SignedMeasure

variable {X : Type u}
variable [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
private theorem isFiniteMeasure_variation (s : SignedMeasure X) :
    IsFiniteMeasure s.variation := by
  rw [← s.totalVariation_eq_variation]
  infer_instance

omit [R1Space X] [BorelSpace X] in
/-- Regularity of a signed measure's total variation is exactly regular variation in the generic
vector-measure sense. -/
theorem totalVariation_regular_iff_hasRegularVariation (s : SignedMeasure X) :
    s.totalVariation.Regular ↔ VectorMeasure.HasRegularVariation s := by
  rw [VectorMeasure.HasRegularVariation, s.totalVariation_eq_variation]

/-- A signed measure has regular variation exactly when both measures in its Jordan decomposition
are regular. -/
theorem hasRegularVariation_iff_jordanParts_regular (s : SignedMeasure X) :
    VectorMeasure.HasRegularVariation s ↔
      s.toJordanDecomposition.posPart.Regular ∧
        s.toJordanDecomposition.negPart.Regular := by
  constructor
  · intro hs
    let : s.variation.Regular := hs
    let : IsFiniteMeasure s.variation := isFiniteMeasure_variation s
    have hpos : s.toJordanDecomposition.posPart ≤ s.variation := by
      rw [← s.totalVariation_eq_variation, totalVariation]
      exact Measure.le_add_right le_rfl
    have hneg : s.toJordanDecomposition.negPart ≤ s.variation := by
      rw [← s.totalVariation_eq_variation, totalVariation]
      exact Measure.le_add_left le_rfl
    exact ⟨Measure.Regular.of_le hpos, Measure.Regular.of_le hneg⟩
  · rintro ⟨hpos, hneg⟩
    let : s.toJordanDecomposition.posPart.Regular := hpos
    let : s.toJordanDecomposition.negPart.Regular := hneg
    have htotal : s.totalVariation.Regular := by
      rw [totalVariation]
      exact Measure.Regular.add_of_finite _ _
    rw [VectorMeasure.HasRegularVariation, ← s.totalVariation_eq_variation]
    exact htotal

omit [R1Space X] [BorelSpace X] in
/-- A finite regular positive measure has regular variation when regarded as a signed measure. -/
theorem hasRegularVariation_toSignedMeasure (μ : Measure X) [μ.Regular] [IsFiniteMeasure μ] :
    VectorMeasure.HasRegularVariation μ.toSignedMeasure := by
  rw [VectorMeasure.HasRegularVariation, Measure.variation_toSignedMeasure]
  infer_instance

/-- The difference of finite regular positive measures has regular variation as a signed measure. -/
theorem hasRegularVariation_toSignedMeasure_sub (μ ν : Measure X)
    [μ.Regular] [ν.Regular] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    VectorMeasure.HasRegularVariation (μ.toSignedMeasure - ν.toSignedMeasure) := by
  have hμ := hasRegularVariation_toSignedMeasure μ
  have hν := hasRegularVariation_toSignedMeasure ν
  let : IsFiniteMeasure μ.toSignedMeasure.variation :=
    isFiniteMeasure_variation μ.toSignedMeasure
  let : IsFiniteMeasure ν.toSignedMeasure.variation :=
    isFiniteMeasure_variation ν.toSignedMeasure
  exact hμ.sub hν

end SignedMeasure

namespace ComplexMeasure

variable {X : Type u}
variable [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- Total variation of a complex measure is bounded by the sum of the variations of its real and
imaginary parts. -/
theorem variation_le_re_add_im (c : ComplexMeasure X) :
    c.variation ≤ c.re.variation + c.im.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  rw [Measure.add_apply c.re.variation c.im.variation s]
  calc
    ‖c s‖ₑ ≤ ‖c.re s‖ₑ + ‖c.im s‖ₑ := by
      simp only [ComplexMeasure.re_apply, ComplexMeasure.im_apply]
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add,
        ENNReal.coe_le_coe]
      exact_mod_cast Complex.norm_le_abs_re_add_abs_im (c s)
    _ ≤ c.re.variation s + c.im.variation s :=
      add_le_add (VectorMeasure.enorm_measure_le_variation _ _)
        (VectorMeasure.enorm_measure_le_variation _ _)

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- The variation of the real part of a complex measure is bounded by its complex variation. -/
theorem variation_re_le (c : ComplexMeasure X) : c.re.variation ≤ c.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  calc
    ‖c.re s‖ₑ ≤ ‖c s‖ₑ := by
      simp only [ComplexMeasure.re_apply, enorm_eq_nnnorm]
      exact_mod_cast Complex.abs_re_le_norm (c s)
    _ ≤ c.variation s := VectorMeasure.enorm_measure_le_variation _ _

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- The variation of the imaginary part of a complex measure is bounded by its complex variation. -/
theorem variation_im_le (c : ComplexMeasure X) : c.im.variation ≤ c.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  calc
    ‖c.im s‖ₑ ≤ ‖c s‖ₑ := by
      simp only [ComplexMeasure.im_apply, enorm_eq_nnnorm]
      exact_mod_cast Complex.abs_im_le_norm (c s)
    _ ≤ c.variation s := VectorMeasure.enorm_measure_le_variation _ _

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- Complex measures have finite total variation. -/
theorem isFiniteMeasure_variation (c : ComplexMeasure X) : IsFiniteMeasure c.variation := by
  let : IsFiniteMeasure c.re.variation := SignedMeasure.isFiniteMeasure_variation c.re
  let : IsFiniteMeasure c.im.variation := SignedMeasure.isFiniteMeasure_variation c.im
  exact isFiniteMeasure_of_le (c.re.variation + c.im.variation) (variation_le_re_add_im c)

/-- A complex measure has regular variation exactly when its real and imaginary signed measures
do. -/
theorem hasRegularVariation_iff_re_im (c : ComplexMeasure X) :
    VectorMeasure.HasRegularVariation c ↔
      VectorMeasure.HasRegularVariation c.re ∧ VectorMeasure.HasRegularVariation c.im := by
  constructor
  · intro hc
    let : c.variation.Regular := hc
    let : IsFiniteMeasure c.variation := isFiniteMeasure_variation c
    exact ⟨Measure.Regular.of_le (variation_re_le c),
      Measure.Regular.of_le (variation_im_le c)⟩
  · rintro ⟨hre, him⟩
    let : c.re.variation.Regular := hre
    let : c.im.variation.Regular := him
    let : IsFiniteMeasure c.re.variation := SignedMeasure.isFiniteMeasure_variation c.re
    let : IsFiniteMeasure c.im.variation := SignedMeasure.isFiniteMeasure_variation c.im
    let : (c.re.variation + c.im.variation).Regular :=
      Measure.Regular.add_of_finite _ _
    exact Measure.Regular.of_le (variation_le_re_add_im c)

/-- Combining signed measures with regular variation produces a complex measure with regular
variation. -/
theorem hasRegularVariation_toComplexMeasure {s t : SignedMeasure X}
    (hs : VectorMeasure.HasRegularVariation s) (ht : VectorMeasure.HasRegularVariation t) :
    VectorMeasure.HasRegularVariation (s.toComplexMeasure t) := by
  rw [hasRegularVariation_iff_re_im]
  rw [SignedMeasure.re_toComplexMeasure, SignedMeasure.im_toComplexMeasure]
  exact ⟨hs, ht⟩

/-- Regular variation is preserved by addition of complex measures. -/
theorem HasRegularVariation.add {c d : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) (hd : VectorMeasure.HasRegularVariation d) :
    VectorMeasure.HasRegularVariation (c + d) := by
  let : IsFiniteMeasure c.variation := isFiniteMeasure_variation c
  let : IsFiniteMeasure d.variation := isFiniteMeasure_variation d
  exact hc.add hd

/-- Regular variation is preserved by subtraction of complex measures. -/
theorem HasRegularVariation.sub {c d : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) (hd : VectorMeasure.HasRegularVariation d) :
    VectorMeasure.HasRegularVariation (c - d) := by
  let : IsFiniteMeasure c.variation := isFiniteMeasure_variation c
  let : IsFiniteMeasure d.variation := isFiniteMeasure_variation d
  exact hc.sub hd

omit [R1Space X] [BorelSpace X] in
/-- Regular variation is preserved by negation of complex measures. -/
theorem HasRegularVariation.neg {c : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) :
    VectorMeasure.HasRegularVariation (-c) :=
  hc.neg

omit [R1Space X] [BorelSpace X] in
/-- Regular variation is preserved by complex scalar multiplication. -/
theorem HasRegularVariation.smul {c : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) (z : ℂ) :
    VectorMeasure.HasRegularVariation (z • c) :=
  hc.smul z

end ComplexMeasure

end
end MeasureTheory
