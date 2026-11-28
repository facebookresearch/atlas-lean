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
# Regular total variation of vector, signed and complex measures

A vector measure has regular variation when its positive variation measure is regular. Negation
and scalar multiplication preserve this property without finiteness assumptions. On an R₁ Borel
space, sums and differences preserve it when the variation measures are finite.

For signed measures on an R₁ Borel space, regular variation is equivalent to regularity of both
Jordan parts. For complex measures it is equivalent to regular variation of the real and
imaginary signed parts. Their variations satisfy `|Re c|≤|c|`, `|Im c|≤|c|≤|Re c|+|Im c|`.
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

/-- **Regularity predicate for vector-measure variation.** Let `X` have a topology and
measurable structure and `V` be a normed additive commutative group. `HasRegularVariation
μ` means the positive measure `μ.variation` is regular for `μ : VectorMeasure X V`. -/
def HasRegularVariation (μ : VectorMeasure X V) : Prop :=
  μ.variation.Regular

namespace HasRegularVariation

/-- **Regular variation of the zero vector measure.** Let `X` have a topology and measurable
structure and `V` be a normed additive commutative group. the zero vector measure has
regular variation. -/
theorem zero : HasRegularVariation (0 : VectorMeasure X V) := by
  rw [HasRegularVariation, variation_zero]
  infer_instance

/-- **Regular variation preserved by vector-measure negation.** Let `X` have a topology and
measurable structure and `V` be a normed additive commutative group. if `μ : VectorMeasure
X V` has regular variation, then `-μ` does too. -/
theorem neg {μ : VectorMeasure X V} (hμ : HasRegularVariation μ) :
    HasRegularVariation (-μ) := by
  rw [HasRegularVariation, variation_neg]
  exact hμ

/-- **Regular variation of a sum with finite variations.** Let `X` have a topology and
measurable structure and `V` be a normed additive commutative group. Assume `X` is an R₁
space and its measurable structure is Borel. if `μ,ν : VectorMeasure X V` have finite
regular variations, then `μ+ν` has regular variation. -/
theorem add [R1Space X] [BorelSpace X] {μ ν : VectorMeasure X V}
    (hμ : HasRegularVariation μ)
    (hν : HasRegularVariation ν) [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] : HasRegularVariation (μ + ν) := by
  let : μ.variation.Regular := hμ
  let : ν.variation.Regular := hν
  let : (μ.variation + ν.variation).Regular :=
    Measure.Regular.add_of_finite μ.variation ν.variation
  exact Measure.Regular.of_le variation_add_le

/-- **Regular variation of a difference with finite variations.** Let `X` have a topology and
measurable structure and `V` be a normed additive commutative group. Assume `X` is an R₁
space and its measurable structure is Borel. if `μ,ν : VectorMeasure X V` have finite
regular variations, then `μ-ν` has regular variation. -/
theorem sub [R1Space X] [BorelSpace X] {μ ν : VectorMeasure X V}
    (hμ : HasRegularVariation μ)
    (hν : HasRegularVariation ν) [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] : HasRegularVariation (μ - ν) := by
  let : μ.variation.Regular := hμ
  let : ν.variation.Regular := hν
  let : (μ.variation + ν.variation).Regular :=
    Measure.Regular.add_of_finite μ.variation ν.variation
  exact Measure.Regular.of_le variation_sub_le

/-- **Regular variation under normed-field scalar multiplication.** Let `X` have a topology
and measurable structure and `V` be a normed additive commutative group. if `V` is a
normed space over a normed field `𝕜`, `μ` has regular variation and `z∈𝕜`, then `z • μ`
has regular variation. Finite total variation is not assumed. -/
theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V]
    {μ : VectorMeasure X V} (hμ : HasRegularVariation μ) (c : 𝕜) :
    HasRegularVariation (c • μ) := by
  let : μ.variation.Regular := hμ
  rw [HasRegularVariation, variation_smul]
  infer_instance

/-- **Finite sum of vector measures with finite regular variations.** Let `X` have a topology
and measurable structure and `V` be a normed additive commutative group. Assume `X` is an
R₁ space and its measurable structure is Borel. for any finite index set `s`, if each
`μ_i` with `i∈s` has finite regular variation, then `Σ_i∈s μ_i` has regular variation. -/
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
/-- Every signed measure on an arbitrary measurable space has finite variation.
No topology or regularity assumption is needed. -/
theorem isFiniteMeasure_variation (s : SignedMeasure X) :
    IsFiniteMeasure s.variation := by
  rw [← s.totalVariation_eq_variation]
  infer_instance

omit [R1Space X] [BorelSpace X] in
/-- **Signed total-variation regularity equals vector regularity.** Let `X` have a topology
and measurable structure, and `s : SignedMeasure X`. Its total variation is regular
exactly when `VectorMeasure.HasRegularVariation s`; neither an R₁ nor a Borel assumption
is required for this identification. -/
theorem totalVariation_regular_iff_hasRegularVariation (s : SignedMeasure X) :
    s.totalVariation.Regular ↔ VectorMeasure.HasRegularVariation s := by
  rw [VectorMeasure.HasRegularVariation, s.totalVariation_eq_variation]

/-- **Regular signed variation exactly when both Jordan parts are regular.** Let `X` be an R₁
topological space with its Borel measurable structure. for `s : SignedMeasure X`,
`HasRegularVariation s` is equivalent to regularity of both `s⁺` and `s⁻` in its Jordan
decomposition. -/
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
/-- **Finite regular positive measure as a regular-variation signed measure.** Let `X` have a
topology and measurable structure, and `μ` a finite regular positive measure. Then
`μ.toSignedMeasure` has regular variation, without R₁ or Borel assumptions. -/
theorem hasRegularVariation_toSignedMeasure (μ : Measure X) [μ.Regular] [IsFiniteMeasure μ] :
    VectorMeasure.HasRegularVariation μ.toSignedMeasure := by
  rw [VectorMeasure.HasRegularVariation, Measure.variation_toSignedMeasure]
  infer_instance

/-- **Regular signed variation of two finite positive measures' difference.** Let `X` be an R₁
topological space with its Borel measurable structure. if `μ,ν` are finite regular
positive measures, `μ.toSignedMeasure-ν.toSignedMeasure` has regular variation. -/
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
/-- **Complex variation bounded by real and imaginary variations.** Let `X` be a measurable
space and `c : ComplexMeasure X`. as positive measures, `|c|≤|Re c|+|Im c|`. No topology
is required. -/
theorem variation_le_re_add_im (c : ComplexMeasure X) :
    c.variation ≤ c.re.variation + c.im.variation := by
  apply VectorMeasure.variation_le_of_forall_eNorm_le
  intro s hs
  rw [add_apply c.re.variation c.im.variation s]
  calc
    ‖c s‖ₑ ≤ ‖c.re s‖ₑ + ‖c.im s‖ₑ := by
      simp only [ComplexMeasure.re_apply, ComplexMeasure.im_apply]
      rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, eNorm_eq_nnNorm, ← ENNReal.coe_add,
        ENNReal.coe_le_coe]
      exact_mod_cast Complex.norm_le_abs_re_add_abs_im (c s)
    _ ≤ c.re.variation s + c.im.variation s :=
      add_le_add (VectorMeasure.eNorm_measure_le_variation _ _)
        (VectorMeasure.eNorm_measure_le_variation _ _)

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- **Real-part variation bounded by complex variation.** Let `X` be a measurable space and `c
: ComplexMeasure X`. `|Re c|≤|c|` as positive measures, without a topology assumption. -/
theorem variation_re_le (c : ComplexMeasure X) : c.re.variation ≤ c.variation := by
  apply VectorMeasure.variation_le_of_forall_eNorm_le
  intro s hs
  calc
    ‖c.re s‖ₑ ≤ ‖c s‖ₑ := by
      simp only [ComplexMeasure.re_apply, eNorm_eq_nnNorm]
      exact_mod_cast Complex.abs_re_le_norm (c s)
    _ ≤ c.variation s := VectorMeasure.eNorm_measure_le_variation _ _

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- **Imaginary-part variation bounded by complex variation.** Let `X` be a measurable space
and `c : ComplexMeasure X`. `|Im c|≤|c|` as positive measures, without a topology
assumption. -/
theorem variation_im_le (c : ComplexMeasure X) : c.im.variation ≤ c.variation := by
  apply VectorMeasure.variation_le_of_forall_eNorm_le
  intro s hs
  calc
    ‖c.im s‖ₑ ≤ ‖c s‖ₑ := by
      simp only [ComplexMeasure.im_apply, eNorm_eq_nnNorm]
      exact_mod_cast Complex.abs_im_le_norm (c s)
    _ ≤ c.variation s := VectorMeasure.eNorm_measure_le_variation _ _

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
/-- **Finite total variation of a complex measure.** Let `X` be a measurable space and `c :
ComplexMeasure X`. the positive measure `|c|` is finite; this is independent of any
topology on `X`. -/
theorem isFiniteMeasure_variation (c : ComplexMeasure X) : IsFiniteMeasure c.variation := by
  let : IsFiniteMeasure c.re.variation := SignedMeasure.isFiniteMeasure_variation c.re
  let : IsFiniteMeasure c.im.variation := SignedMeasure.isFiniteMeasure_variation c.im
  exact isFiniteMeasure_of_le (c.re.variation + c.im.variation) (variation_le_re_add_im c)

/-- **Regular complex variation exactly by the two signed coordinate parts.** Let `X` be an R₁
topological space with its Borel measurable structure. for `c : ComplexMeasure X`,
regularity of `|c|` is equivalent to regular variation of both `Re c` and `Im c`. -/
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

/-- **Regular complex measure from two regular-variation signed measures.** Let `X` be an R₁
topological space with its Borel measurable structure. if signed measures `s,t` have
regular variation, then `s+i t`, constructed as `s.toComplexMeasure t`, has regular
variation. -/
theorem hasRegularVariation_toComplexMeasure {s t : SignedMeasure X}
    (hs : VectorMeasure.HasRegularVariation s) (ht : VectorMeasure.HasRegularVariation t) :
    VectorMeasure.HasRegularVariation (s.toComplexMeasure t) := by
  rw [hasRegularVariation_iff_re_im]
  rw [SignedMeasure.re_toComplexMeasure, SignedMeasure.im_toComplexMeasure]
  exact ⟨hs, ht⟩

/-- **Addition of complex measures with regular variation.** Let `X` be an R₁ topological
space with its Borel measurable structure. if complex measures `c,d` have regular
variation, then `c+d` does too; their variations are automatically finite. -/
theorem HasRegularVariation.add {c d : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) (hd : VectorMeasure.HasRegularVariation d) :
    VectorMeasure.HasRegularVariation (c + d) := by
  let : IsFiniteMeasure c.variation := isFiniteMeasure_variation c
  let : IsFiniteMeasure d.variation := isFiniteMeasure_variation d
  exact hc.add hd

/-- **Subtraction of complex measures with regular variation.** Let `X` be an R₁ topological
space with its Borel measurable structure. if complex measures `c,d` have regular
variation, then `c-d` has regular variation. -/
theorem HasRegularVariation.sub {c d : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) (hd : VectorMeasure.HasRegularVariation d) :
    VectorMeasure.HasRegularVariation (c - d) := by
  let : IsFiniteMeasure c.variation := isFiniteMeasure_variation c
  let : IsFiniteMeasure d.variation := isFiniteMeasure_variation d
  exact hc.sub hd

omit [R1Space X] [BorelSpace X] in
/-- **Negation preserves regular complex variation.** Let `X` have a topology and measurable
structure. If a complex measure `c` has regular variation, then `-c` does too; no R₁ or
Borel premise is required. -/
theorem HasRegularVariation.neg {c : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) :
    VectorMeasure.HasRegularVariation (-c) :=
  VectorMeasure.HasRegularVariation.neg hc

omit [R1Space X] [BorelSpace X] in
/-- **Complex scaling preserves regular variation.** Let `X` have a topology and measurable
structure. If a complex measure `c` has regular variation, then so does `z • c` for every
`z∈ℂ`, without R₁ or Borel assumptions. -/
theorem HasRegularVariation.smul {c : ComplexMeasure X}
    (hc : VectorMeasure.HasRegularVariation c) (z : ℂ) :
    VectorMeasure.HasRegularVariation (z • c) :=
  VectorMeasure.HasRegularVariation.smul hc z

end ComplexMeasure

end
end MeasureTheory
