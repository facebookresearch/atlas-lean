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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CharacterSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom
public import Mathlib.Topology.DenseEmbedding

/-!
# Character automorphisms of the full crossed-product completion

Let G be a locally compact topological group with regular left Haar measure μ, A a nonunital
complex C-star algebra, and α a point-norm action. Modulation Mχf(s)=χ(s)•f(s) by a continuous
unitary character preserves the maximal covariant C-star seminorm. It therefore induces a star
automorphism Dχ of the full covariance completion, characterized by Dχι(f)=ι(Mχf), with D1=id
and Dχη=Dχ∘Dη.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

attribute [local instance] fullCovariantCompletionCStarAlgebra

/-- **Completed character endomorphism.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let χ:G→𝕋 be a continuous unitary character. On the compactly supported twisted convolution
core put pmax(f)=sup{p(f): p is a C-star seminorm and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core
coefficient h}. Write X=FullCovariantCompletion μ α for the separated completion in pmax, and
ι for its dense core map. The complex star endomorphism Dχ:X→X satisfies
Dχ(ι(f))=ι(s↦χ(s)•f(s)).
-/
def completedCharacterHom (chi : PontryaginDual G) :
    FullCovariantCompletion mu alpha →⋆ₙₐ[ℂ] FullCovariantCompletion mu alpha := by
  let p := maximalCStarSeminorm mu alpha
  letI : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let f := p.toNonUnitalCompletion.comp (characterModulationEquiv mu alpha chi).toNonUnitalStarAlgHom
  exact p.fromNonUnitalCompletion f (fun x => by
    change ‖p.toNonUnitalCompletion (characterModulation mu alpha chi x)‖ ≤ p x
    rw [CStarSeminorm.norm_toNonUnitalCompletion, maximal_character_eq])

omit [mu.Regular] in
/-- **Character action on dense completed coefficients.**

For χ∈PontryaginDual G and a Haar-core coefficient f, `completedCharacterHom μ α χ
(toFullCovariantCompletion μ α f) = toFullCovariantCompletion μ α (characterModulation μ α χ
f)`, where characterModulation χ f(s)=χ(s)•f(s).
-/
@[simp]
theorem completedCharacterHom_apply (chi : PontryaginDual G) (f : Carrier mu alpha) :
    completedCharacterHom mu alpha chi (toFullCovariantCompletion mu alpha f) =
      toFullCovariantCompletion mu alpha (characterModulation mu alpha chi f) := by
  let p := maximalCStarSeminorm mu alpha
  let : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact p.fromNonUnitalCompletion_apply
    (p.toNonUnitalCompletion.comp (characterModulationEquiv mu alpha chi).toNonUnitalStarAlgHom)
    (fun x => by
      change ‖p.toNonUnitalCompletion (characterModulation mu alpha chi x)‖ ≤ p x
      rw [CStarSeminorm.norm_toNonUnitalCompletion, maximal_character_eq]) f

omit [mu.Regular] in
/-- **Trivial character on the full completion.**

The endomorphism D1 induced by the trivial character is the identity of
FullCovariantCompletion μ α.
-/
theorem completedCharacterHom_one : completedCharacterHom mu alpha 1 = NonUnitalStarAlgHom.id ℂ _ := by
  have := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    (F := FullCovariantCompletion mu alpha →⋆ₙₐ[ℂ] FullCovariantCompletion mu alpha)
  apply NonUnitalStarAlgHom.ext
  intro x
  refine (denseRange_toFullCovariantCompletion mu alpha).induction_on x
    (isClosed_eq (map_continuous (completedCharacterHom mu alpha 1)) continuous_id) ?_
  intro f
  rw [completedCharacterHom_apply, characterModulation_one]
  rfl

omit [mu.Regular] in
/-- **Composition of completed character maps.**

For unitary characters χ,η of G, the completed endomorphisms of FullCovariantCompletion μ α
satisfy Dχη=Dχ∘Dη.
-/
theorem completedCharacterHom_mul (chi eta : PontryaginDual G) :
    completedCharacterHom mu alpha (chi * eta) =
      (completedCharacterHom mu alpha chi).comp (completedCharacterHom mu alpha eta) := by
  have := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    (F := FullCovariantCompletion mu alpha →⋆ₙₐ[ℂ] FullCovariantCompletion mu alpha)
  apply NonUnitalStarAlgHom.ext
  intro x
  refine (denseRange_toFullCovariantCompletion mu alpha).induction_on x
    (isClosed_eq (map_continuous (completedCharacterHom mu alpha (chi * eta)))
      ((map_continuous (completedCharacterHom mu alpha chi)).comp
        (map_continuous (completedCharacterHom mu alpha eta)))) ?_
  intro f
  rw [completedCharacterHom_apply, characterModulation_mul_character]
  rw [NonUnitalStarAlgHom.comp_apply, completedCharacterHom_apply, completedCharacterHom_apply]

/-- **Completed unitary-character automorphism.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let χ:G→𝕋 be a continuous unitary character. On the compactly supported twisted convolution
core put pmax(f)=sup{p(f): p is a C-star seminorm and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core
coefficient h}. Write X=FullCovariantCompletion μ α for the separated completion in pmax, and
ι for its dense core map. The character action Dχ:X≃⋆ₐ[ℂ]X satisfies Dχ(ι(f))=ι(s↦χ(s)•f(s));
its inverse is Dχ⁻¹.
-/
def completedCharacterEquiv (chi : PontryaginDual G) :
    FullCovariantCompletion mu alpha ≃⋆ₐ[ℂ] FullCovariantCompletion mu alpha :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (completedCharacterHom mu alpha chi)
    (completedCharacterHom mu alpha chi⁻¹)
    (by rw [← completedCharacterHom_mul, inv_mul_cancel, completedCharacterHom_one])
    (by rw [← completedCharacterHom_mul, mul_inv_cancel, completedCharacterHom_one])

omit [mu.Regular] in
/-- **Character automorphism on the dense full core.**

For a Haar-core coefficient f and unitary character χ, `completedCharacterEquiv μ α χ
(toFullCovariantCompletion μ α f) = toFullCovariantCompletion μ α (characterModulation μ α χ
f)`, with characterModulation χ f(s)=χ(s)•f(s).
-/
@[simp]
theorem completedCharacterEquiv_apply (chi : PontryaginDual G) (f : Carrier mu alpha) :
    completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f) =
      toFullCovariantCompletion mu alpha (characterModulation mu alpha chi f) :=
  completedCharacterHom_apply mu alpha chi f

end HaarTwistedCore
