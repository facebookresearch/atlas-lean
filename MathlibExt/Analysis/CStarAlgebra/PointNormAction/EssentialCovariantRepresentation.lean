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
# Essential restriction of a covariant representation

Let (π,U) be a covariant representation of an action α on a nonunital complex C-star algebra
A, acting on a complex Hilbert space H. The closed span Eπ of vectors π(a)ξ is invariant under
every Ug. Restricting π and U to Eπ gives a strongly continuous covariant representation whose
coefficient action is nondegenerate.
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

/-- **Vector covariance.**

For a covariant representation (π,U), g ∈ G, a ∈ A and ξ ∈ H, `U_g (π(a) ξ) = π(α_g(a)) (U_g
ξ)`.
-/
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

/-- **Invariance of the coefficient essential space.**

Each group unitary Ug preserves Eπ, the closed linear span of the coefficient-generated
vectors π(a)ξ.
-/
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

/-- **Unitary restriction to the essential space.**

The restriction of Ug to the closed Hilbert subspace Eπ is a surjective complex linear
isometry.
-/
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

/-- **Strongly continuous action on the essential space.**

The restrictions Ug|Eπ form a strongly continuous unitary representation of G on Eπ.
-/
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

/-- **Restricted group action agrees on vectors.**

For ξ ∈ Eπ, including the restricted vector Ug|Eπ ξ into H gives Ug ξ.
-/
@[simp]
theorem essentialGroup_apply_coe (ρ : CovariantRepresentation α H) (g : G)
    (ξ : ρ.algebra.essentialSpace) :
    ((ρ.essentialGroup g : ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) ξ : H) =
      (ρ.group g : H →L[ℂ] H) ξ := rfl

/-- **Essential covariant representation.**

Restricting the coefficient representation π and group representation U to Eπ gives a
covariant representation of α on Eπ.
-/
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

/-- **Coefficient representation after essential restriction.**

The coefficient part of the essential covariant representation is the restriction of π to Eπ.
-/
@[simp]
theorem essentialCovariantRepresentation_algebra (ρ : CovariantRepresentation α H) :
    ρ.essentialCovariantRepresentation.algebra = ρ.algebra.essentialRepresentation := rfl

/-- **Group vectors after essential restriction.**

For g ∈ G and ξ ∈ Eπ, the group part of the essential covariant representation acts as Ug ξ
when viewed in H.
-/
@[simp]
theorem essentialCovariantRepresentation_group_apply_coe
    (ρ : CovariantRepresentation α H) (g : G) (ξ : ρ.algebra.essentialSpace) :
    ((ρ.essentialCovariantRepresentation.group g :
      ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) ξ : H) =
        (ρ.group g : H →L[ℂ] H) ξ := rfl

/-- **Nondegeneracy of the essential coefficient representation.**

The coefficient essential space of the representation on Eπ is all of Eπ.
-/
theorem essentialCovariantRepresentation_essentialSpace_eq_top (ρ : CovariantRepresentation α H) :
    ρ.essentialCovariantRepresentation.algebra.essentialSpace = ⊤ :=
  ρ.algebra.essentialRepresentation_essentialSpace_eq_top

/-- **Density of coefficient-generated vectors.**

The complex linear span of πess(a)ξ, for a ∈ A and ξ ∈ Eπ, is dense in Eπ.
-/
theorem nondegenerate_essentialCovariantRepresentation (ρ : CovariantRepresentation α H) :
    Dense (Submodule.span ℂ (Set.range fun p : A × ρ.algebra.essentialSpace =>
      ρ.essentialCovariantRepresentation.algebra p.1 p.2) : Set ρ.algebra.essentialSpace) :=
  ρ.essentialCovariantRepresentation.algebra.essentialSpace_eq_top_iff_dense.mp
    (ρ.essentialCovariantRepresentation_essentialSpace_eq_top)

end

end CovariantRepresentation
