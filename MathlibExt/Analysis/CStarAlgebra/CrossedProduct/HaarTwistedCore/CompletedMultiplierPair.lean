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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedCoefficientMultiplier
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedGroupMultiplier
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.ConvolutionSeminormIntegral

/-!
# Covariant coefficient and group multiplier pairs

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For a∈A, the multiplier j_p(a) has left and right
components extending L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The group multiplier u_p(g)
extends the left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹),
where δ(g)=Measure.modularCharacter g is viewed as a complex scalar. Their covariance is
u_p(g)j_p(a)=j_p(α_g(a))u_p(g). If p is L¹-dominated, then ∫ s, (j_p(f(s))*u_p(s)).fst(ιp(h))
∂μ=ιp(f*h) for compactly supported continuous coefficients f,h.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped MultiplierAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- **Covariance of the coefficient and group multipliers.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For a∈A, the multiplier j_p(a) has left and right
components extending L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The group multiplier u_p(g)
extends the left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹),
where δ(g)=Measure.modularCharacter g is viewed as a complex scalar. For g∈G and a∈A,
u_p(g)j_p(a)=j_p(α_g(a))u_p(g).
-/
theorem groupMultiplier_coefficientMultiplier (g : G) (a : A) :
    groupMultiplier μ α p g * coefficientMultiplier μ α p a =
      coefficientMultiplier μ α p (α g a) * groupMultiplier μ α p g := by
  apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
  · change groupLeftCompletion μ α p g (coefficientLeftCompletion μ α p a x) =
      coefficientLeftCompletion μ α p (α g a) (groupLeftCompletion μ α p g x)
    refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
      ((groupLeftCompletion μ α p g).continuous.comp
        (coefficientLeftCompletion μ α p a).continuous)
      ((coefficientLeftCompletion μ α p (α g a)).continuous.comp
        (groupLeftCompletion μ α p g).continuous) ?_) x
    funext f
    simp only [Function.comp_apply, coefficientLeftCompletion_apply, groupLeftCompletion_apply]
    simpa only [LinearMap.comp_apply] using
      congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => p.toNonUnitalCompletion (T f))
        (groupLeft_coefficientLeft μ α g a)
  · change coefficientRightCompletion μ α p a (groupRightCompletion μ α p g x) =
      groupRightCompletion μ α p g (coefficientRightCompletion μ α p (α g a) x)
    refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
      ((coefficientRightCompletion μ α p a).continuous.comp
        (groupRightCompletion μ α p g).continuous)
      ((groupRightCompletion μ α p g).continuous.comp
        (coefficientRightCompletion μ α p (α g a)).continuous) ?_) x
    funext f
    simp only [Function.comp_apply, coefficientRightCompletion_apply, groupRightCompletion_apply]
    simpa only [LinearMap.comp_apply] using
      congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => p.toNonUnitalCompletion (T f))
        (coefficientRight_groupRight μ α g a)

/-- **Conjugation of coefficients by group multipliers.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For a∈A, the multiplier j_p(a) has left and right
components extending L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The group multiplier u_p(g)
extends the left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹),
where δ(g)=Measure.modularCharacter g is viewed as a complex scalar. For g∈G and a∈A,
u_p(g)*j_p(a)*star(u_p(g))=j_p(α_g(a)).
-/
theorem groupMultiplier_conjugates_coefficient (g : G) (a : A) :
    groupMultiplier μ α p g * coefficientMultiplier μ α p a * star (groupMultiplier μ α p g) =
      coefficientMultiplier μ α p (α g a) := by
  rw [groupMultiplier_coefficientMultiplier, mul_assoc,
    Unitary.mul_star_self_of_mem (groupMultiplier_mem_unitary μ α p g), mul_one]

/-- **Canonical covariant multiplier pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For a∈A, the multiplier j_p(a) has left and right
components extending L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The group multiplier u_p(g)
extends the left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹),
where δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The pair
canonicalMultiplierPair μ α p consists of the nonunital complex star homomorphism
j_p:A→𝓜(ℂ,Xp) and unitary-valued group homomorphism u_p:G→unitary(𝓜(ℂ,Xp)), together with the
identity u_p(g)*j_p(a)*star(u_p(g))=j_p(α_g(a)).
-/
def canonicalMultiplierPair :
    { pair : (A →⋆ₙₐ[ℂ] 𝓜(ℂ, p.NonUnitalCompletion)) ×
        (G →* unitary 𝓜(ℂ, p.NonUnitalCompletion)) //
      ∀ g : G, ∀ a : A,
        (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) * pair.1 a *
          star (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) = pair.1 (α g a) } :=
  ⟨⟨coefficientMultiplierHom μ α p, groupUnitaryMultiplierHom μ α p⟩, fun g a => by
    change groupMultiplier μ α p g * coefficientMultiplier μ α p a *
      star (groupMultiplier μ α p g) = coefficientMultiplier μ α p (α g a)
    exact groupMultiplier_conjugates_coefficient μ α p g a⟩

/-- **Coefficient map of the canonical multiplier pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The coefficient homomorphism of
canonicalMultiplierPair μ α p is coefficientMultiplierHom μ α p, whose dense left component
sends ιp(f) to ιp(s↦a*f(s)) for a∈A.
-/
@[simp]
theorem canonicalMultiplierPair_coefficient :
    (canonicalMultiplierPair μ α p).val.1 = coefficientMultiplierHom μ α p := rfl

/-- **Group map of the canonical multiplier pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group homomorphism of canonicalMultiplierPair
μ α p is groupUnitaryMultiplierHom μ α p, whose dense left component sends ιp(f) to
ιp(s↦α_g(f(g⁻¹*s))) for g∈G.
-/
@[simp]
theorem canonicalMultiplierPair_group :
    (canonicalMultiplierPair μ α p).val.2 = groupUnitaryMultiplierHom μ α p := rfl

/-- **Conjugation covariance of the canonical pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For a∈A, the multiplier j_p(a) has left and right
components extending L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The group multiplier u_p(g)
extends the left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹),
where δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The coefficient and group
maps j_p,u_p in canonicalMultiplierPair μ α p satisfy u_p(g)*j_p(a)*star(u_p(g))=j_p(α_g(a))
for g∈G and a∈A.
-/
theorem canonicalMultiplierPair_covariance (g : G) (a : A) :
    ((canonicalMultiplierPair μ α p).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) *
        (canonicalMultiplierPair μ α p).val.1 a *
          star ((canonicalMultiplierPair μ α p).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) =
      (canonicalMultiplierPair μ α p).val.1 (α g a) :=
  (canonicalMultiplierPair μ α p).property g a

/-- **Multiplier slices on dense core vectors.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For j_p,u_p in canonicalMultiplierPair μ α p,
core coefficients f,h and s∈G, (j_p(f(s))*u_p(s)).fst(ιp(h))=ιp(x↦f(s)*α_s(h(s⁻¹*x))).
-/
theorem canonicalMultiplierPair_slice_apply (f : Carrier μ α) (s : G) (h : Carrier μ α) :
    ((canonicalMultiplierPair μ α p).val.1 (f s) *
        ((canonicalMultiplierPair μ α p).val.2 s : 𝓜(ℂ, p.NonUnitalCompletion))).fst
          (p.toNonUnitalCompletion h) =
      p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
  change coefficientLeftCompletion μ α p (f s)
    (groupLeftCompletion μ α p s (p.toNonUnitalCompletion h)) = _
  rw [groupLeftCompletion_apply, coefficientLeftCompletion_apply]

variable (hp : p ∈ admissibleCStarSeminorms μ α)

include hp in
/-- **Integrability of canonical multiplier slices.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For j_p,u_p in canonicalMultiplierPair μ α
p and core coefficients f,h, the curve s↦(j_p(f(s))*u_p(s)).fst(ιp(h)) is μ-integrable in Xp.
-/
theorem integrable_canonicalMultiplierPair_slice (f h : Carrier μ α) :
    let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
    Integrable (fun s : G =>
      ((canonicalMultiplierPair μ α p).val.1 (f s) *
          ((canonicalMultiplierPair μ α p).val.2 s : 𝓜(ℂ, p.NonUnitalCompletion))).fst
            (p.toNonUnitalCompletion h)) μ := by
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  apply (integrable_toNonUnitalCompletion_coefficientLeft_groupLeft μ α p hp f h).congr
  exact Eventually.of_forall fun s => (canonicalMultiplierPair_slice_apply μ α p f s h).symm

include hp in
/-- **Integrated multiplier slices equal convolution.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For j_p,u_p in canonicalMultiplierPair μ α
p and core coefficients f,h, ∫ s:G, (j_p(f(s))*u_p(s)).fst(ιp(h)) ∂μ=ιp(f*h), where (f*h)(x)=∫
s, f(s)*α_s(h(s⁻¹*x)) ∂μ.
-/
theorem integral_canonicalMultiplierPair_slice (f h : Carrier μ α) :
    let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
    (∫ s : G,
      ((canonicalMultiplierPair μ α p).val.1 (f s) *
          ((canonicalMultiplierPair μ α p).val.2 s : 𝓜(ℂ, p.NonUnitalCompletion))).fst
            (p.toNonUnitalCompletion h) ∂μ) = p.toNonUnitalCompletion (f * h) := by
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  calc
    _ = ∫ s : G, p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun s => canonicalMultiplierPair_slice_apply μ α p f s h)
    _ = _ := integral_toNonUnitalCompletion_coefficientLeft_groupLeft μ α p hp f h

end

end HaarTwistedCore
