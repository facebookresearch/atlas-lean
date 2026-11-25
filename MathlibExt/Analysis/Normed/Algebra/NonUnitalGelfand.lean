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

public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# The Gelfand evaluation map for a nonunital complex Banach algebra

The existing weak character space consists of nonzero continuous complex
linear multiplicative functionals. Its union with the zero functional is
compact. Evaluation at an original algebra element therefore vanishes at
infinity on the actual character space.

These facts construct the nonunital Gelfand map into the existing functions
vanishing at infinity. No unit, commutativity, involution, C-star identity,
nonzero hypothesis or chosen character-space model is required. The zero
algebra has its ordinary empty character space. No isometry, surjectivity or
star-preservation assertion is part of the defining map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology
open scoped ZeroAtInfty

namespace WeakDual

universe uA

variable {A : Type uA} [NonUnitalNormedRing A] [NormedSpace ℂ A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

namespace CharacterSpace

/-- **Norm bound on character evaluation.** Let `A` be a nonunital complex Banach algebra, and let
`Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. For every
`χ ∈ Δ(A)` and `a ∈ A`, `|χ(a)| ≤ ‖a‖`. -/
theorem norm_apply_le (φ : characterSpace ℂ A) (a : A) : ‖φ a‖ ≤ ‖a‖ :=
  quasispectrum.norm_le_norm_of_mem (NonUnitalAlgHom.apply_mem_quasispectrum φ a)

/-- **Norm of a nonunital character.** Let `A` be a nonunital complex Banach algebra, and let `Δ(A)` be
the space of its nonzero continuous complex characters with pointwise topology. Every `χ ∈ Δ(A)`, as
a continuous complex-linear functional on `A`, has operator norm at most one. -/
theorem norm_le_one (φ : characterSpace ℂ A) :
    ‖toStrongDual (φ : WeakDual ℂ A)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [one_mul, toStrongDual_apply, CharacterSpace.coe_coe] using norm_apply_le φ a

/-- **Compactness of characters together with zero.** Let `A` be a nonunital complex Banach algebra, and
let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. The
set `Δ(A) ∪ {0}` is compact in the pointwise-topologized continuous dual of `A`. -/
theorem union_zero_isCompact : IsCompact (characterSpace ℂ A ∪ {0}) := by
  refine (WeakDual.isCompact_closedBall (𝕜 := ℂ) (E := A) 0 1).of_isClosed_subset
    (union_zero_isClosed ℂ A) ?_
  intro φ hφ
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rcases hφ with hφ | hφ
  · exact norm_le_one ⟨φ, hφ⟩
  · obtain rfl := Set.mem_singleton_iff.mp hφ
    simp

/-- **Local compactness of the character space.** Let `A` be a nonunital complex Banach algebra, and let
`Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. The
character space `Δ(A)` is locally compact. -/
theorem locallyCompactSpaceNonUnital : LocallyCompactSpace (characterSpace ℂ A) := by
  let K : Set (WeakDual ℂ A) := characterSpace ℂ A ∪ {0}
  let : CompactSpace K := isCompact_iff_compactSpace.mp (union_zero_isCompact (A := A))
  let i : characterSpace ℂ A → K := fun φ => ⟨φ, Or.inl φ.property⟩
  have hi : IsEmbedding i :=
    (IsEmbedding.of_comp_iff
      (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : K → WeakDual ℂ A))).mp
      (show IsEmbedding ((Subtype.val : K → WeakDual ℂ A) ∘ i) from
        IsEmbedding.subtypeVal)
  have hrange : Set.range i = {φ : K | (φ : WeakDual ℂ A) ≠ 0} := by
    ext φ
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ψ.property.1
    · intro hφ
      have hcharacter : (φ : WeakDual ℂ A) ∈ characterSpace ℂ A := by
        rcases φ.property with hcharacter | hzero
        · exact hcharacter
        · exact (hφ (Set.mem_singleton_iff.mp hzero)).elim
      exact ⟨⟨φ, hcharacter⟩, Subtype.ext rfl⟩
  have hopen : IsOpen (Set.range i) := by
    rw [hrange]
    exact isClosed_singleton.isOpen_compl.preimage
      (continuous_subtype_val : Continuous (Subtype.val : K → WeakDual ℂ A))
  exact (show IsOpenEmbedding i from ⟨hi, hopen⟩).locallyCompactSpace

/-- **Compact superlevels of character evaluation.** Let `A` be a nonunital complex Banach algebra, and
let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. For
every `a ∈ A` and `ε > 0`, the set `{χ ∈ Δ(A) : ε ≤ |χ(a)|}` is compact. -/
theorem isCompact_norm_superlevel (a : A) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {φ : characterSpace ℂ A | ε ≤ ‖φ a‖} := by
  rw [Subtype.isCompact_iff]
  have himage : Subtype.val '' {φ : characterSpace ℂ A | ε ≤ ‖φ a‖} =
      (characterSpace ℂ A ∪ {0}) ∩ {φ : WeakDual ℂ A | ε ≤ ‖φ a‖} := by
    ext φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      exact ⟨Or.inl ψ.property, hψ⟩
    · rintro ⟨hφ, hvalue⟩
      have hcharacter : φ ∈ characterSpace ℂ A := by
        rcases hφ with hcharacter | hzero
        · exact hcharacter
        · obtain rfl := Set.mem_singleton_iff.mp hzero
          change ε ≤ ‖(0 : ℂ)‖ at hvalue
          rw [norm_zero] at hvalue
          exact ((not_le.mpr hε) hvalue).elim
      exact ⟨⟨φ, hcharacter⟩, hvalue, rfl⟩
  rw [himage]
  exact (union_zero_isCompact (A := A)).inter_right
    (isClosed_le continuous_const (WeakDual.eval_continuous a).norm)

/-- **Character evaluation vanishes at infinity.** Let `A` be a nonunital complex Banach algebra, and
let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. For
each `a ∈ A`, the function `χ ↦ χ(a)` tends to zero along the cocompact filter of `Δ(A)`. -/
theorem eval_zero_at_infty (a : A) :
    Tendsto (fun φ : characterSpace ℂ A => φ a)
      (cocompact (characterSpace ℂ A)) (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [(isCompact_norm_superlevel a hε).compl_mem_cocompact] with φ hφ
  have hvalue : ¬ ε ≤ ‖φ a‖ := hφ
  simpa only [dist_zero_right] using lt_of_not_ge hvalue

end CharacterSpace

/-- **Nonunital Banach-algebra Gelfand transform.** Let `A` be a nonunital complex Banach algebra, and
let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. The
evaluation formula `a ↦ (χ ↦ χ(a))` defines a nonunital complex algebra homomorphism `A →
C₀(Δ(A),ℂ)`. -/
def nonUnitalGelfandTransform : A →ₙₐ[ℂ] C₀(characterSpace ℂ A, ℂ) where
  toFun a :=
    { toFun := fun φ => φ a
      continuous_toFun := (WeakDual.eval_continuous a).comp continuous_subtype_val
      zero_at_infty' := CharacterSpace.eval_zero_at_infty a }
  map_zero' := by ext φ; exact map_zero φ
  map_add' a b := by ext φ; exact map_add φ a b
  map_mul' a b := by ext φ; exact map_mul φ a b
  map_smul' z a := by ext φ; exact map_smul φ z a

/-- **Evaluation of the nonunital Gelfand transform.** Let `A` be a nonunital complex Banach algebra,
and let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology.
The Gelfand transform of `a ∈ A` has value `χ(a)` at every `χ ∈ Δ(A)`. -/
@[simp]
theorem nonUnitalGelfandTransform_apply (a : A) (φ : characterSpace ℂ A) :
    nonUnitalGelfandTransform a φ = φ a := rfl

/-- **Contractivity of the nonunital Gelfand transform.** Let `A` be a nonunital complex Banach algebra,
and let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology.
The supremum norm of the Gelfand transform of `a ∈ A` is at most `‖a‖`. -/
theorem norm_nonUnitalGelfandTransform_le (a : A) :
    ‖nonUnitalGelfandTransform a‖ ≤ ‖a‖ := by
  change ‖(nonUnitalGelfandTransform a).toBCF‖ ≤ ‖a‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg a)).mpr
  intro φ
  exact CharacterSpace.norm_apply_le φ a

/-- **Continuous linear Gelfand transform.** Let `A` be a nonunital complex Banach algebra, and let
`Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology. The
evaluation Gelfand transform is a continuous complex-linear map `A → C₀(Δ(A),ℂ)`, with the supremum
norm on the function space. -/
def nonUnitalGelfandTransformCLM : A →L[ℂ] C₀(characterSpace ℂ A, ℂ) :=
  (LinearMap.ofClass
    (nonUnitalGelfandTransform (A := A) : A →ₙₐ[ℂ] C₀(characterSpace ℂ A, ℂ))).mkContinuous 1 (by
      intro a
      change ‖nonUnitalGelfandTransform a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using norm_nonUnitalGelfandTransform_le a)

/-- **Values of the continuous linear Gelfand transform.** Let `A` be a nonunital complex Banach
algebra, and let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise
topology. The continuous linear Gelfand transform of `a` is the same `C₀` function as the algebraic
Gelfand transform. -/
@[simp]
theorem nonUnitalGelfandTransformCLM_apply (a : A) :
    nonUnitalGelfandTransformCLM a = nonUnitalGelfandTransform a := rfl

/-- **Continuity of the nonunital Gelfand transform.** Let `A` be a nonunital complex Banach algebra,
and let `Δ(A)` be the space of its nonzero continuous complex characters with pointwise topology.
The Gelfand transform from `A` to `C₀(Δ(A),ℂ)` is continuous in the algebra norm and the function
supremum norm. -/
theorem continuous_nonUnitalGelfandTransform :
    Continuous (nonUnitalGelfandTransform (A := A) : A → C₀(characterSpace ℂ A, ℂ)) :=
  (nonUnitalGelfandTransformCLM (A := A)).continuous

end WeakDual

end
