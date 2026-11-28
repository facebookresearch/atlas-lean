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

public import MathlibExt.MeasureTheory.VectorMeasure.RegularVariation
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Regular signed-measure subspace and continuous integration

On an R₁ Borel space, signed measures with regular total variation form a real submodule. On a
compact such space, integration defines the bounded real functional `I_s : C(X,ℝ) → ℝ`.

It satisfies `|I_s(f)|≤|s|(X)‖f‖∞` and is linear in the signed measure, including negative
scalars. The norm equality and inverse Riesz construction are established separately for compact
Hausdorff spaces.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace MathlibExt.MeasureTheory

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [R1Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Real submodule of signed measures with regular total variation.** Let `X` be an R₁
topological space with its Borel measurable structure. `regularSignedMeasureSubmodule X`
consists of signed measures `s` whose positive total-variation measure `|s|` is regular. -/
noncomputable def regularSignedMeasureSubmodule (X : Type u)
    [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X] :
    Submodule ℝ (SignedMeasure X) where
  carrier := {s | s.totalVariation.Regular}
  zero_mem' :=
    (SignedMeasure.totalVariation_regular_iff_hasRegularVariation
      (0 : SignedMeasure X)).2 VectorMeasure.HasRegularVariation.zero
  add_mem' := by
    intro s t hs ht
    apply (SignedMeasure.totalVariation_regular_iff_hasRegularVariation (s + t)).2
    let _ : IsFiniteMeasure s.variation := SignedMeasure.isFiniteMeasure_variation s
    let _ : IsFiniteMeasure t.variation := SignedMeasure.isFiniteMeasure_variation t
    exact ((SignedMeasure.totalVariation_regular_iff_hasRegularVariation s).1 hs).add
      ((SignedMeasure.totalVariation_regular_iff_hasRegularVariation t).1 ht)
  smul_mem' := by
    intro c s hs
    exact (SignedMeasure.totalVariation_regular_iff_hasRegularVariation (c • s)).2
      (((SignedMeasure.totalVariation_regular_iff_hasRegularVariation s).1 hs).smul c)

/-- **Signed measure with regular total variation.** Let `X` be an R₁ topological space with
its Borel measurable structure. `RegularSignedMeasure X` is the carrier of that real
submodule; it stores the signed measure and regularity of `|s|`. -/
abbrev RegularSignedMeasure (X : Type u) [TopologicalSpace X] [R1Space X]
    [MeasurableSpace X] [BorelSpace X] :=
  ↑(regularSignedMeasureSubmodule X)

namespace RegularSignedMeasure

/-- **Regularity of a regular signed measure's total variation.** Let `X` be an R₁ topological
space with its Borel measurable structure. Let `s` be a signed measure whose total
variation `|s|` is regular. the positive measure `|s|` is regular. -/
theorem totalVariation_regular (s : RegularSignedMeasure X) :
    (s : SignedMeasure X).totalVariation.Regular :=
  s.property

/-- **Regular signed measure as a vector-measure regularity predicate.** Let `X` be an R₁
topological space with its Borel measurable structure. Let `s` be a signed measure whose
total variation `|s|` is regular. the underlying signed vector measure satisfies
`VectorMeasure.HasRegularVariation s`. -/
theorem hasRegularVariation (s : RegularSignedMeasure X) :
    VectorMeasure.HasRegularVariation (s : SignedMeasure X) :=
  (SignedMeasure.totalVariation_regular_iff_hasRegularVariation (s : SignedMeasure X)).1
    s.property

variable [CompactSpace X]

omit [R1Space X] in
private theorem continuousMap_integrable (s : SignedMeasure X) (f : C(X, ℝ)) :
    s.Integrable fun x ↦ f x := by
  let _ : IsFiniteMeasure s.variation := SignedMeasure.isFiniteMeasure_variation s
  apply Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm x

private noncomputable def signedIntegralLinear (s : RegularSignedMeasure X) :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ᵛ x, f x ∂<•(s : SignedMeasure X)
  map_add' f g := by
    simpa only [ContinuousMap.add_apply] using
      (VectorMeasure.integral_fun_add
        (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
        (continuousMap_integrable (s : SignedMeasure X) f)
        (continuousMap_integrable (s : SignedMeasure X) g))
  map_smul' c f := by
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply] using
      (VectorMeasure.integral_fun_smul (s : SignedMeasure X)
        (ContinuousLinearMap.lsmul ℝ ℝ).flip c (fun x ↦ f x))

@[simp]
private theorem signedIntegralLinear_apply (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    signedIntegralLinear s f = ∫ᵛ x, f x ∂<•(s : SignedMeasure X) :=
  rfl

private theorem norm_signedIntegralLinear_apply_le
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    ‖signedIntegralLinear s f‖ ≤
      (s : SignedMeasure X).totalVariation.real univ * ‖f‖ := by
  let _ : IsFiniteMeasure (s : SignedMeasure X).variation :=
    SignedMeasure.isFiniteMeasure_variation (s : SignedMeasure X)
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := (s : SignedMeasure X))
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (f := fun x ↦ f x)
    (Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm x)
  simpa [signedIntegralLinear, SignedMeasure.totalVariation_eq_variation,
    mul_comm] using h

/-- **Bounded real functional of a regular signed measure.** Let `X` be an R₁ topological
space with its Borel measurable structure. Let `s` be a signed measure whose total
variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. `signedIntegralDual s : C(X,ℝ) →L[ℝ] ℝ` is `f ↦ I_s(f)` with the supremum norm
on continuous functions. -/
@[no_expose]
noncomputable def signedIntegralDual (s : RegularSignedMeasure X) :
    StrongDual ℝ C(X, ℝ) :=
  LinearMap.mkContinuous (signedIntegralLinear s)
    ((s : SignedMeasure X).totalVariation.real univ)
    (norm_signedIntegralLinear_apply_le s)

/-- **Value of the regular signed integral functional.** Let `X` be an R₁ topological space
with its Borel measurable structure. Let `s` be a signed measure whose total variation
`|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for `f∈C(X,ℝ)`. for
`f∈C(X,ℝ)`, `signedIntegralDual s f=∫ᵛ f ds`, the signed vector-measure integral. -/
@[simp]
theorem signedIntegralDual_apply (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    signedIntegralDual s f = ∫ᵛ x, f x ∂<•(s : SignedMeasure X) :=
  by
    simp only [signedIntegralDual, LinearMap.mkContinuous_apply,
      signedIntegralLinear_apply]

/-- **Pointwise total-variation bound for continuous signed integration.** Let `X` be an R₁
topological space with its Borel measurable structure. Let `s` be a signed measure whose
total variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. for `f∈C(X,ℝ)`, `|I_s(f)|≤|s|.real(X)*‖f‖∞`. -/
theorem norm_signedIntegralDual_apply_le
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    ‖signedIntegralDual s f‖ ≤
      (s : SignedMeasure X).totalVariation.real univ * ‖f‖ :=
  by
    simpa only [signedIntegralDual, LinearMap.mkContinuous_apply] using
      norm_signedIntegralLinear_apply_le s f

/-- **Operator norm upper bound of signed integration.** Let `X` be an R₁ topological space
with its Borel measurable structure. Let `s` be a signed measure whose total variation
`|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for `f∈C(X,ℝ)`.
`‖signedIntegralDual s‖≤|s|.real(X)`. -/
theorem norm_signedIntegralDual_le (s : RegularSignedMeasure X) :
    ‖signedIntegralDual s‖ ≤ (s : SignedMeasure X).totalVariation.real univ := by
  apply ContinuousLinearMap.opNorm_le_bound _ measureReal_nonneg
  exact norm_signedIntegralDual_apply_le s

/-- **Real-linear map from regular signed measures to continuous functionals.** Let `X` be an
R₁ topological space with its Borel measurable structure. Let `s` be a signed measure
whose total variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds`
for `f∈C(X,ℝ)`. `regularSignedMeasureIntegral` sends each regular signed measure `t` to
`I_t ∈ C(X,ℝ)*`. -/
@[no_expose]
noncomputable def regularSignedMeasureIntegral :
    RegularSignedMeasure X →ₗ[ℝ] StrongDual ℝ C(X, ℝ) where
  toFun := signedIntegralDual
  map_add' s t := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [signedIntegralDual_apply, add_apply]
    change (∫ᵛ x, f x ∂<•((s : SignedMeasure X) + (t : SignedMeasure X))) =
      (∫ᵛ x, f x ∂<•(s : SignedMeasure X)) +
        ∫ᵛ x, f x ∂<•(t : SignedMeasure X)
    exact VectorMeasure.integral_add_vectorMeasure
      (continuousMap_integrable (s : SignedMeasure X) f)
      (continuousMap_integrable (t : SignedMeasure X) f)
  map_smul' c s := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [signedIntegralDual_apply, smul_apply, RingHom.id_apply]
    change (∫ᵛ x, f x ∂<•(c • (s : SignedMeasure X))) =
      c • ∫ᵛ x, f x ∂<•(s : SignedMeasure X)
    exact VectorMeasure.integral_smul_vectorMeasure (fun x ↦ f x) c

/-- **Zero regular signed measure has zero continuous integral.** Let `X` be an R₁ topological
space with its Borel measurable structure. Let `s` be a signed measure whose total
variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. `signedIntegralDual 0=0`. -/
@[simp]
theorem signedIntegralDual_zero :
    signedIntegralDual (0 : RegularSignedMeasure X) = 0 :=
  (regularSignedMeasureIntegral (X := X)).map_zero

/-- **Additivity of the continuous signed-measure functional.** Let `X` be an R₁ topological
space with its Borel measurable structure. Let `s` be a signed measure whose total
variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. for another regular signed measure `t`, `I_(s+t)=I_s+I_t`. -/
@[simp]
theorem signedIntegralDual_add (s t : RegularSignedMeasure X) :
    signedIntegralDual (s + t) = signedIntegralDual s + signedIntegralDual t :=
  (regularSignedMeasureIntegral (X := X)).map_add s t

/-- **Real homogeneity of the signed integral functional.** Let `X` be an R₁ topological space
with its Borel measurable structure. Let `s` be a signed measure whose total variation
`|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for `f∈C(X,ℝ)`. for
every `c∈ℝ`, `I_(c • s)=c • I_s`. -/
@[simp]
theorem signedIntegralDual_smul (c : ℝ) (s : RegularSignedMeasure X) :
    signedIntegralDual (c • s) = c • signedIntegralDual s :=
  (regularSignedMeasureIntegral (X := X)).map_smul c s

/-- **Negation of a signed measure negates its integral functional.** Let `X` be an R₁
topological space with its Borel measurable structure. Let `s` be a signed measure whose
total variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. `I_(-s)=-I_s`. -/
@[simp]
theorem signedIntegralDual_neg (s : RegularSignedMeasure X) :
    signedIntegralDual (-s) = -signedIntegralDual s :=
  (regularSignedMeasureIntegral (X := X)).map_neg s

/-- **Difference of signed measures gives a difference of functionals.** Let `X` be an R₁
topological space with its Borel measurable structure. Let `s` be a signed measure whose
total variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. for regular signed `t`, `I_(s-t)=I_s-I_t`. -/
@[simp]
theorem signedIntegralDual_sub (s t : RegularSignedMeasure X) :
    signedIntegralDual (s - t) = signedIntegralDual s - signedIntegralDual t :=
  (regularSignedMeasureIntegral (X := X)).map_sub s t

/-- **Evaluation of the linear regular signed integration map.** Let `X` be an R₁ topological
space with its Borel measurable structure. Let `s` be a signed measure whose total
variation `|s|` is regular. Assume `X` is compact, and write `I_s(f)=∫ f ds` for
`f∈C(X,ℝ)`. for `f∈C(X,ℝ)`, `regularSignedMeasureIntegral s f=∫ᵛ f ds`. -/
@[simp]
theorem regularSignedMeasureIntegral_apply
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    regularSignedMeasureIntegral s f =
      ∫ᵛ x, f x ∂<•(s : SignedMeasure X) :=
  signedIntegralDual_apply s f

end RegularSignedMeasure

end

end MathlibExt.MeasureTheory
