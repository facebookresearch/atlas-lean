/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.InitialVertex
public import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertexIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSliceOpposite
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Native under-slice characterization of initiality

The opposite of each original boundary inclusion is the same boundary inclusion
through the actual standard-simplex reversal. The whole under-slice isomorphism
and its literal projection equation then transport every lifting square and its
filler. This proves the under-projection criterion for the original point.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet
namespace boundary

/-- The full original opposite boundary maps into the same standard boundary. -/
def oppositeHom (n : ℕ) : (∂Δ[n] : SSet.{u}).op ⟶ (∂Δ[n] : SSet.{u}) :=
  Subcomplex.lift (opFunctor.map ∂Δ[n].ι ≫ (stdSimplex.opIso ⦋n⦌).hom) (by
    intro d x hx
    rw [Subfunctor.range_obj] at hx
    obtain ⟨s, rfl⟩ := hx
    change (stdSimplex.opIso ⦋n⦌).hom.app d s.val ∈ ∂Δ[n].obj d
    have h : (stdSimplex.opIso ⦋n⦌).hom.app d s.val ∈
        (∂Δ[n].op.preimage (stdSimplex.opIso ⦋n⦌).inv).obj d := by
      change (stdSimplex.opIso ⦋n⦌).inv.app d
        ((stdSimplex.opIso ⦋n⦌).hom.app d s.val) ∈ ∂Δ[n].op.obj d
      have hi : (stdSimplex.opIso ⦋n⦌).inv.app d
          ((stdSimplex.opIso ⦋n⦌).hom.app d s.val) = s.val := by
        change ((stdSimplex.opIso ⦋n⦌).hom ≫
          (stdSimplex.opIso ⦋n⦌).inv).app d s.val = s.val
        rw [Iso.hom_inv_id]
        rfl
      rw [hi]
      exact s.property
    rwa [op_boundary] at h)

/-- The inverse reversal retains every original boundary simplex. -/
def oppositeInv (n : ℕ) : (∂Δ[n] : SSet.{u}) ⟶ (∂Δ[n] : SSet.{u}).op :=
  Subcomplex.lift (B := (boundary.{u} n).op)
    (∂Δ[n].ι ≫ (stdSimplex.opIso ⦋n⦌).inv) (by
    intro d x hx
    rw [Subfunctor.range_obj] at hx
    obtain ⟨s, rfl⟩ := hx
    change s.val ∈ (∂Δ[n].op.preimage (stdSimplex.opIso ⦋n⦌).inv).obj d
    rw [op_boundary]
    exact s.property)

/-- Reversal identifies the whole original boundary with the same standard boundary. -/
def oppositeIso (n : ℕ) : (∂Δ[n] : SSet.{u}).op ≅ (∂Δ[n] : SSet.{u}) where
  hom := oppositeHom n
  inv := oppositeInv n
  hom_inv_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change ((stdSimplex.opIso ⦋n⦌).hom ≫
      (stdSimplex.opIso ⦋n⦌).inv).app d s.val = s.val
    rw [Iso.hom_inv_id]
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change ((stdSimplex.opIso ⦋n⦌).inv ≫
      (stdSimplex.opIso ⦋n⦌).hom).app d s.val = s.val
    rw [Iso.inv_hom_id]
    rfl

/-- The whole boundary comparison commutes with the literal original inclusion. -/
@[reassoc]
theorem oppositeIso_hom_ι (n : ℕ) :
    (oppositeIso.{u} n).hom ≫ ∂Δ[n].ι =
      opFunctor.map ∂Δ[n].ι ≫ (stdSimplex.opIso ⦋n⦌).hom :=
  rfl

/-- The opposite of the original standard boundary inclusion is the same inclusion as an arrow. -/
def opArrowIso (n : ℕ) :
    Arrow.mk (opFunctor.map (boundary.{u} n).ι) ≅ Arrow.mk (boundary.{u} n).ι :=
  Arrow.isoMk (oppositeIso n) (stdSimplex.opIso ⦋n⦌) (oppositeIso_hom_ι n)

end boundary

/-- Every boundary lifting condition is unchanged by the original opposite functor. -/
theorem hasLiftingProperty_boundary_op_iff {X Y : SSet.{u}} (n : ℕ) (p : X ⟶ Y) :
    HasLiftingProperty (boundary n).ι (opFunctor.map p) ↔
      HasLiftingProperty (boundary n).ι p := by
  calc
    HasLiftingProperty (boundary n).ι (opFunctor.map p) ↔
        HasLiftingProperty (opFunctor.map (boundary n).ι) (opFunctor.map p) :=
      (HasLiftingProperty.iff_of_arrow_iso_left (boundary.opArrowIso n)
        (opFunctor.map p)).symm
    _ ↔ HasLiftingProperty (boundary n).ι p :=
      Functor.hasLiftingProperty_iff_of_isEquivalence opEquivalence.functor (boundary n).ι p

/-- The original under-projection and the opposite point's over-projection are isomorphic arrows. -/
def initialVertexProjectionOppositeArrowIso {X : SSet.{u}}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    Arrow.mk (opFunctor.map (sliceUnder.proj X x)) ≅
      Arrow.mk (sliceOver.proj X.op (oppositeVertex x)) := by
  refine sliceUnderOppositeProjectionArrowIso X x ≪≫
    Arrow.isoMk (sliceOver.indexIso X.op (opFunctor.map x)
      (stdSimplex.opIso ⦋0⦌).symm) (Iso.refl X.op) ?_
  rw [sliceOver.indexIso_hom]
  change sliceOver.restrict X.op (opFunctor.map x) (stdSimplex.opIso ⦋0⦌).inv ≫
      sliceOver.proj X.op ((stdSimplex.opIso ⦋0⦌).inv ≫ opFunctor.map x) =
    sliceOver.proj X.op (opFunctor.map x) ≫ 𝟙 _
  rw [Category.comp_id]
  exact sliceOver.restrict_proj X.op (opFunctor.map x) (stdSimplex.opIso ⦋0⦌).inv

/-- Initiality of the original point is all-boundary lifting for its actual
whole under-projection. -/
theorem isInitialVertex_iff {X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) :
    IsInitialVertex x ↔ ∀ n : ℕ, HasLiftingProperty (boundary n).ι (sliceUnder.proj X x) := by
  unfold IsInitialVertex
  rw [isTerminalVertex_iff]
  apply forall_congr'
  intro n
  exact (HasLiftingProperty.iff_of_arrow_iso_right (boundary n).ι
    (initialVertexProjectionOppositeArrowIso x)).symm.trans
      (hasLiftingProperty_boundary_op_iff n (sliceUnder.proj X x))

/-- Initiality of the given point is unchanged by an actual ambient isomorphism. -/
theorem isInitialVertex_iff_of_iso {X Y : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X)
    (e : X ≅ Y) :
    IsInitialVertex x ↔ IsInitialVertex (x ≫ e.hom) := by
  unfold IsInitialVertex
  rw [oppositeVertex_comp]
  exact isTerminalVertex_iff_of_iso (oppositeVertex x) (opFunctor.mapIso e)

end SSet
