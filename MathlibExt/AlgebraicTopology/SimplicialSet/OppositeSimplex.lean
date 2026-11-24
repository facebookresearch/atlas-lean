/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.HomCongr

/-!
# Original opposite simplices and vertices

The low-level standard simplex reversal retains the original whole maps,
all original simplex operators, the original Yoneda simplex and the original
vertices. Mapping-space and general join-slice clients share this supplier.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u

namespace SSet

/-- The original representable map postcomposes the original ordinal map. -/
theorem stdSimplex_map_app_apply {n m d : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (stdSimplex.map f).app (op ⦋d⦌) x i = f.toOrderHom (x i) := rfl

/-- The genuine standard-simplex opposite Iso intertwines every original simplex operator
as a whole simplicial map. -/
theorem stdSimplex_opIso_naturality {n m : SimplexCategory} (φ : n ⟶ m) :
    (SSet.stdSimplex.opIso.{u} n).inv ≫ opFunctor.map (SSet.stdSimplex.map φ) =
      SSet.stdSimplex.map (SimplexCategory.rev.map φ) ≫ (SSet.stdSimplex.opIso m).inv := by
  ext q σ
  apply ULift.ext
  change SimplexCategory.rev.map σ.down ≫ φ =
    SimplexCategory.rev.map (σ.down ≫ SimplexCategory.rev.map φ)
  rw [Functor.map_comp, SimplexCategory.rev_map_rev_map]


/-- The genuine opposite bijection on the whole original standard simplex. -/
def oppositeSimplexEquiv (X : SSet.{u}) (n : ℕ) :
    ((Δ[n] : SSet.{u}) ⟶ X) ≃ ((Δ[n] : SSet.{u}) ⟶ X.op) :=
  opEquivalence.fullyFaithfulFunctor.homEquiv.trans
    ((SSet.stdSimplex.opIso ⦋n⦌).homCongr (Iso.refl X.op))

/-- The opposite bijection reads the literal opposite simplex,
with the original standard-simplex identification. -/
theorem oppositeSimplexEquiv_apply (X : SSet.{u}) (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    oppositeSimplexEquiv X n σ = (SSet.stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ := by
  change ((SSet.stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ) ≫ 𝟙 X.op = _
  exact Category.comp_id _


/-- The opposite whole simplex has precisely the unchanged Yoneda element
in the reversed ambient presheaf. -/
theorem oppositeSimplexEquiv_yoneda (B : SSet.{u}) (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ B) :
    yonedaEquiv (oppositeSimplexEquiv B n σ) = opObjEquiv.symm (yonedaEquiv σ) := by
  rw [oppositeSimplexEquiv_apply, yonedaEquiv_comp, opFunctor_map]
  have h : opObjEquiv ((SSet.stdSimplex.opIso ⦋n⦌).inv.app (op ⦋n⦌)
      (yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))) = yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := by
    apply ULift.ext
    change SimplexCategory.rev.map (𝟙 ⦋n⦌) = 𝟙 ⦋n⦌
    exact SimplexCategory.rev.map_id _
  exact congrArg (fun z => opObjEquiv.symm (σ.app (op ⦋n⦌) z)) h


/-- The original point in the opposite simplicial set, using the actual simplex reversal. -/
def oppositeVertex {X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ X.op :=
  (stdSimplex.opIso ⦋0⦌).inv ≫ opFunctor.map x


/-- Reversing a point commutes with an actual map of ambient simplicial sets. -/
@[reassoc]
theorem oppositeVertex_comp {X Y : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X)
    (f : X ⟶ Y) :
    oppositeVertex (x ≫ f) = oppositeVertex x ≫ opFunctor.map f := by
  unfold oppositeVertex
  rw [CategoryTheory.Functor.map_comp, Category.assoc]


/-- The standard simplex reversal is natural in the original unreversed operator form. -/
theorem stdSimplex_opIso_inv_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    stdSimplex.{u}.map f ≫ (stdSimplex.opIso m).inv =
      (stdSimplex.opIso n).inv ≫ opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)) := by
  simpa only [SimplexCategory.rev_obj, SimplexCategory.rev_map_rev_map] using
    (stdSimplex_opIso_naturality (SimplexCategory.rev.map f)).symm

/-- Reversing a representing simplex gives the same original opposite Yoneda simplex. -/
theorem yonedaEquiv_opposite {X : SSet.{u}} (n : SimplexCategory)
    (f : stdSimplex.obj n ⟶ X) :
    yonedaEquiv ((stdSimplex.opIso n).inv ≫ opFunctor.map f) =
      opObjEquiv.symm (yonedaEquiv f) := by
  cases n with | mk n =>
    rw [← oppositeSimplexEquiv_apply]
    exact oppositeSimplexEquiv_yoneda X n f

end SSet
