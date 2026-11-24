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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.CovariantRepresentation
public import MathlibExt.Analysis.CStarAlgebra.EssentialNondegeneracy

/-!
# Actual essential restriction of a covariant representation

Covariance makes the actual closed span of coefficient-operator ranges
invariant under every group unitary. Restrict the group and coefficient
operators to that closed Hilbert subspace. The inherited vector values give
unitarity, strong continuity and covariance, while the existing essential
representation theorem gives actual nondegeneracy.

This computes a nondegenerate source covariant pair from the completed Gram
pair. No invariant subspace, continuity, norm model or nondegeneracy is an
additional constructor input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra InnerProductSpace

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {α : PointNormCStarAction G A}

/-- Covariance transports every original coefficient vector value under the actual group unitary. -/
theorem group_algebra_apply (ρ : CovariantRepresentation α H) (g : G) (a : A) (ξ : H) :
    (ρ.group g : H →L[ℂ] H) (ρ.algebra a ξ) =
      ρ.algebra (α g a) ((ρ.group g : H →L[ℂ] H) ξ) := by
  have hStar : star (ρ.group g : H →L[ℂ] H) = (ρ.group g⁻¹ : H →L[ℂ] H) :=
    congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
      (ρ.group.toMonoidHom.map_inv g).symm
  have h := congrArg (fun T : H →L[ℂ] H => T ((ρ.group g : H →L[ℂ] H) ξ))
    (ρ.covariance g a)
  change (ρ.group g : H →L[ℂ] H)
      (ρ.algebra a (star (ρ.group g : H →L[ℂ] H) ((ρ.group g : H →L[ℂ] H) ξ))) = _ at h
  rw [hStar, ← ρ.group.apply_mul g⁻¹ g ξ, inv_mul_cancel, ρ.group.apply_one] at h
  exact h

/-- Covariance preserves the actual coefficient essential space under every group element. -/
theorem group_preserves_essentialSpace (ρ : CovariantRepresentation α H) (g : G)
    (ξ : H) (hξ : ξ ∈ ρ.algebra.essentialSpace) :
    (ρ.group g : H →L[ℂ] H) ξ ∈ ρ.algebra.essentialSpace := by
  let S : Submodule ℂ H := Submodule.span ℂ
    (Set.range fun p : A × H => ρ.algebra p.1 p.2)
  let P : Submodule ℂ H := ρ.algebra.essentialSpace.comap
    (ρ.group g : H →L[ℂ] H).toLinearMap
  have hSpan : S ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, η⟩, rfl⟩
    change (ρ.group g : H →L[ℂ] H) (ρ.algebra a η) ∈ ρ.algebra.essentialSpace
    rw [ρ.group_algebra_apply]
    exact ρ.algebra.range_mem_essentialSpace (α g a) _
  have hClosed : IsClosed (P : Set H) :=
    S.isClosed_topologicalClosure.preimage (ρ.group g : H →L[ℂ] H).continuous
  have hEssential : ρ.algebra.essentialSpace ≤ P :=
    S.topologicalClosure_minimal hSpan hClosed
  exact hEssential hξ

/-- The original group unitary restricted to the actual coefficient essential space. -/
def essentialGroupIsometry (ρ : CovariantRepresentation α H) (g : G) :
    ρ.algebra.essentialSpace ≃ₗᵢ[ℂ] ρ.algebra.essentialSpace where
  toFun ξ := ⟨(ρ.group g : H →L[ℂ] H) ξ, ρ.group_preserves_essentialSpace g ξ ξ.property⟩
  invFun ξ := ⟨(ρ.group g⁻¹ : H →L[ℂ] H) ξ, ρ.group_preserves_essentialSpace g⁻¹ ξ ξ.property⟩
  left_inv ξ := by
    apply Subtype.ext
    change (ρ.group g⁻¹ : H →L[ℂ] H) ((ρ.group g : H →L[ℂ] H) ξ) = (ξ : H)
    rw [← ρ.group.apply_mul, inv_mul_cancel, ρ.group.apply_one]
  right_inv ξ := by
    apply Subtype.ext
    change (ρ.group g : H →L[ℂ] H) ((ρ.group g⁻¹ : H →L[ℂ] H) ξ) = (ξ : H)
    rw [← ρ.group.apply_mul, mul_inv_cancel, ρ.group.apply_one]
  map_add' ξ η := by
    apply Subtype.ext
    change (ρ.group g : H →L[ℂ] H) ((ξ : H) + η) = _
    exact map_add (ρ.group g : H →L[ℂ] H) (ξ : H) (η : H)
  map_smul' c ξ := by
    apply Subtype.ext
    change (ρ.group g : H →L[ℂ] H) (c • (ξ : H)) = _
    exact map_smul (ρ.group g : H →L[ℂ] H) c (ξ : H)
  norm_map' ξ := ρ.group.norm_apply g (ξ : H)

/-- The actual strongly continuous group representation on the coefficient essential space. -/
def essentialGroup (ρ : CovariantRepresentation α H) :
    StronglyContinuousUnitaryRepresentation G ρ.algebra.essentialSpace where
  toMonoidHom :=
    { toFun g := Unitary.linearIsometryEquiv.symm (ρ.essentialGroupIsometry g)
      map_one' := by
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro ξ
        apply Subtype.ext
        change (ρ.group (1 : G) : H →L[ℂ] H) (ξ : H) = (ξ : H)
        exact ρ.group.apply_one (ξ : H)
      map_mul' g h := by
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro ξ
        apply Subtype.ext
        change (ρ.group (g * h) : H →L[ℂ] H) (ξ : H) =
          (ρ.group g : H →L[ℂ] H) ((ρ.group h : H →L[ℂ] H) ξ)
        exact ρ.group.apply_mul g h (ξ : H) }
  continuous_orbit ξ := by
    change Continuous (fun g : G =>
      (⟨(ρ.group g : H →L[ℂ] H) (ξ : H),
        ρ.group_preserves_essentialSpace g ξ ξ.property⟩ : ρ.algebra.essentialSpace))
    exact (ρ.group.continuous_orbit (ξ : H)).subtype_mk _

/-- The restricted group action retains every original essential-vector value. -/
@[simp]
theorem essentialGroup_apply_coe (ρ : CovariantRepresentation α H) (g : G)
    (ξ : ρ.algebra.essentialSpace) :
    ((ρ.essentialGroup g : ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) ξ : H) =
      (ρ.group g : H →L[ℂ] H) ξ := rfl

/-- The original covariant pair restricted to its actual coefficient essential Hilbert space. -/
def essentialCovariantRepresentation (ρ : CovariantRepresentation α H) :
    CovariantRepresentation α ρ.algebra.essentialSpace where
  algebra := ρ.algebra.essentialRepresentation
  group := ρ.essentialGroup
  covariance g a := by
    have hStar :
        star (ρ.essentialGroup g : ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) =
          (ρ.essentialGroup g⁻¹ : ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) :=
      congrArg (fun u : unitary (ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) =>
        (u : ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace))
        (ρ.essentialGroup.toMonoidHom.map_inv g).symm
    rw [hStar]
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change (ρ.group g : H →L[ℂ] H) (ρ.algebra a ((ρ.group g⁻¹ : H →L[ℂ] H) ξ)) =
      ρ.algebra (α g a) (ξ : H)
    rw [ρ.group_algebra_apply, ← ρ.group.apply_mul, mul_inv_cancel, ρ.group.apply_one]

/-- Essential restriction retains the literal existing coefficient representation. -/
@[simp]
theorem essentialCovariantRepresentation_algebra (ρ : CovariantRepresentation α H) :
    ρ.essentialCovariantRepresentation.algebra = ρ.algebra.essentialRepresentation := rfl

/-- The actual essential covariant pair retains the original group vector values. -/
@[simp]
theorem essentialCovariantRepresentation_group_apply_coe
    (ρ : CovariantRepresentation α H) (g : G) (ξ : ρ.algebra.essentialSpace) :
    ((ρ.essentialCovariantRepresentation.group g :
      ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) ξ : H) =
        (ρ.group g : H →L[ℂ] H) ξ := rfl

/-- The actual essential covariant coefficient map satisfies the neutral nondegeneracy condition. -/
theorem essentialCovariantRepresentation_essentialSpace_eq_top (ρ : CovariantRepresentation α H) :
    ρ.essentialCovariantRepresentation.algebra.essentialSpace = ⊤ :=
  ρ.algebra.essentialRepresentation_essentialSpace_eq_top

/-- Compatibility with the original dense-span essential covariant statement. -/
theorem nondegenerate_essentialCovariantRepresentation (ρ : CovariantRepresentation α H) :
    Dense (Submodule.span ℂ (Set.range fun p : A × ρ.algebra.essentialSpace =>
      ρ.essentialCovariantRepresentation.algebra p.1 p.2) : Set ρ.algebra.essentialSpace) :=
  ρ.essentialCovariantRepresentation.algebra.essentialSpace_eq_top_iff_dense.mp
    (ρ.essentialCovariantRepresentation_essentialSpace_eq_top)

end

end CovariantRepresentation
