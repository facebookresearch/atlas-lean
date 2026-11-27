/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

/-!
# Tests for the cotangent normalization of global perfect obstruction theories

The naturality of the chart comparisons and the pure-differential normalization of chart
refinements together compute restrictions: restricting the comparison image of `1 ⊗ d p` from a
chart to a refinement gives the comparison image of `1 ⊗ d p'`, where `p'` is the image of `p`
under the refinement's polynomial map.
-/

noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

namespace MathlibExtTest.GlobalPerfectObstructionTheory

variable {X Y : Scheme.{0}} {f : X ⟶ Y} (N : CotangentNormalization f) (a b : AffineChart f)
  (hU : b.source ≤ a.source) (hV : b.target ≤ a.target) (n : ℕ)

/-- The pure differential `1 ⊗ d p` in degree `-n` of the cotangent complex of a chart. -/
abbrev pureDifferential (c : AffineChart f) (p : (N.resolution c).algebra.obj (op ⦋n⦌)) :
    (affineComplex (N.resolution c)).X (-(n : ℤ)) :=
  (affineDegreeIso (N.resolution c) n).inv
    (CommAlgCat.resolutionCotangentTermDifferential c.base (CommAlgCat.of c.base c.ring)
      (N.resolution c).algebra (N.resolution c).augmentation (op ⦋n⦌) p)

/-- Restricting the comparison image of a pure differential from `a` to the refinement `b` gives
the comparison image of the refined pure differential. -/
example (p : (N.resolution a).algebra.obj (op ⦋n⦌)) :
    (sectionRestriction N.complex hU).f (-(n : ℤ))
        ((N.comparison a).f (-(n : ℤ)) (pureDifferential N n a p)) =
      (N.comparison b).f (-(n : ℤ))
        (pureDifferential N n b ((N.refinement a b hU hV).polynomialMap (op ⦋n⦌) p)) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (N.naturality a b hU hV) (-(n : ℤ))) (pureDifferential N n a p)
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at h
  rw [h]
  have h2 := congrArg (affineDegreeIso (N.resolution b) n).inv
    ((N.refinement a b hU hV).pure_differential n p)
  erw [Iso.hom_inv_id_apply] at h2
  erw [h2]
  rfl

/-- On the trivial refinement of a chart, the polynomial maps are identities. -/
example (p : (N.resolution a).algebra.obj (op ⦋n⦌)) :
    (N.refinement a a le_rfl le_rfl).polynomialMap (op ⦋n⦌) p = p := by
  rw [N.identity]
  rfl

end MathlibExtTest.GlobalPerfectObstructionTheory
