/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SliceLeftFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.OppositeSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-!
# Exact opposite operators for the two original mapping-space orientations

Reversal exchanges the normalized first-vertex ordinal shift with the
last-vertex shift. The actual standard-simplex opposite isomorphism
intertwines every original simplex operator. These whole equations are
the operator prerequisite for the right/opposite-left mapping comparison.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.MappingSpaceOppositeOperators

private def leftShift {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) : ⦋n + 1⦌ ⟶ ⦋m + 1⦌ :=
  (zeroAddSuccIso n).inv ≫ AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) φ ≫
    (zeroAddSuccIso m).hom

private theorem tensorInl {a b c d : SimplexCategory} (f : a ⟶ b) (g : c ⟶ d) :
    AugmentedSimplexCategory.inl' a c ≫ AugmentedSimplexCategory.tensorHomOf f g =
      f ≫ AugmentedSimplexCategory.inl' b d :=
  congrArg WithInitial.down
    (AugmentedSimplexCategory.inl_comp_tensorHom (Join.ofHom f) (Join.ofHom g))

private theorem tensorInr {a b c d : SimplexCategory} (f : a ⟶ b) (g : c ⟶ d) :
    AugmentedSimplexCategory.inr' a c ≫ AugmentedSimplexCategory.tensorHomOf f g =
      g ≫ AugmentedSimplexCategory.inr' b d :=
  congrArg WithInitial.down
    (AugmentedSimplexCategory.inr_comp_tensorHom (Join.ofHom f) (Join.ofHom g))

private theorem rightInl (n : ℕ) :
    AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ = SimplexCategory.δ (Fin.last (n + 1)) := by
  apply SSet.stdSimplex.{0}.map_injective
  exact (joinInl_comp_joinStdSimplexIso_hom.{0} n 0).symm.trans (frontInclusion_eq n)

private theorem rightInr (n : ℕ) :
    AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)) := by
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  rw [AugmentedSimplexCategory.inr'_eval]
  simp [SimplexCategory.const]

private theorem leftShift_source {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 ≫ leftShift φ =
      SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0 := by
  rw [← inl'_zero_comp_zeroAddSuccIso_hom n]
  simp only [leftShift, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, tensorInl, Category.id_comp]
  exact inl'_zero_comp_zeroAddSuccIso_hom m

private theorem leftShift_back {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ leftShift φ =
      φ ≫ SimplexCategory.δ (0 : Fin (m + 2)) := by
  rw [← inr'_zero_comp_zeroAddSuccIso_hom n]
  simp only [leftShift, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, tensorInr, Category.assoc, inr'_zero_comp_zeroAddSuccIso_hom m]

private theorem revSource (n : ℕ) :
    SimplexCategory.rev.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)) := by
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  simp [SimplexCategory.rev_map_apply, SimplexCategory.const]

/-- Reversal exchanges every actual normalized first-vertex operator with the original last-vertex operator. -/
theorem rev_normalizedLeftShift {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.rev.map
        ((zeroAddSuccIso n).inv ≫ AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) φ ≫
          (zeroAddSuccIso m).hom) =
      AugmentedSimplexCategory.tensorHomOf (SimplexCategory.rev.map φ) (𝟙 ⦋0⦌) := by
  change SimplexCategory.rev.map (leftShift φ) = _
  have hback : SimplexCategory.δ (Fin.last (n + 1)) ≫ SimplexCategory.rev.map (leftShift φ) =
      SimplexCategory.rev.map φ ≫ SimplexCategory.δ (Fin.last (m + 1)) := by
    have h := congrArg (fun f => SimplexCategory.rev.map f) (leftShift_back φ)
    simpa only [Functor.map_comp, SimplexCategory.rev_map_δ, Fin.rev_zero] using h
  have hsource : SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)) ≫
        SimplexCategory.rev.map (leftShift φ) =
      SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ (Fin.last (m + 1)) := by
    have h := congrArg (fun f => SimplexCategory.rev.map f) (leftShift_source φ)
    simpa only [Functor.map_comp, revSource] using h
  have h : Join.ofHom (SimplexCategory.rev.map (leftShift φ)) =
      Join.ofHom (AugmentedSimplexCategory.tensorHomOf (SimplexCategory.rev.map φ) (𝟙 ⦋0⦌)) := by
    refine AugmentedSimplexCategory.tensorObj_hom_ext
      (x := WithInitial.of ⦋n⦌) (y := WithInitial.of ⦋0⦌) _ _ ?_ ?_
    · change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ ≫
          SimplexCategory.rev.map (leftShift φ) =
        AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ ≫
          AugmentedSimplexCategory.tensorHomOf (SimplexCategory.rev.map φ) (𝟙 ⦋0⦌)
      rw [tensorInl, rightInl, rightInl]
      exact hback
    · change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ ≫
          SimplexCategory.rev.map (leftShift φ) =
        AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ ≫
          AugmentedSimplexCategory.tensorHomOf (SimplexCategory.rev.map φ) (𝟙 ⦋0⦌)
      rw [tensorInr, Category.id_comp, rightInr, rightInr]
      exact hsource
  exact congrArg WithInitial.down h

/-- The genuine standard-simplex opposite Iso intertwines every original simplex operator as a whole simplicial map. -/
theorem stdSimplex_opIso_naturality {n m : SimplexCategory} (φ : n ⟶ m) :
    (SSet.stdSimplex.opIso.{u} n).inv ≫ opFunctor.map (SSet.stdSimplex.map φ) =
      SSet.stdSimplex.map (SimplexCategory.rev.map φ) ≫ (SSet.stdSimplex.opIso m).inv :=
  SSet.stdSimplex_opIso_naturality φ

end SSet.MappingSpaceOppositeOperators
