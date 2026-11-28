/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIntegral
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeAffineChart

/-!
# A Weierstrass cubic over a field is an integral proper curve

Let `W` be a Weierstrass curve over a field `F`, of any discriminant, with projective curve
`C = Proj S_W ⊆ ℙ²_F` (`WeierstrassCurve.ProjectiveScheme`). Then `C` is an integral scheme,
proper over `Spec F`, of dimension `1`, and its affine chart `C ∩ {Z ≠ 0} = Spec A_W`
(`WeierstrassCurve.affineChart`) is dense in `C`
(`WeierstrassCurve.isIntegral_isProper_dim_one_dense_affineChart`).

## References

* B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2.
* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1: the plane cubic (9), displayed on
  p. 45 and referred back to on p. 46, and its affine part.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace WeierstrassCurve

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

/-- Over a field, the affine chart `Spec A_W` of the projective Weierstrass curve is dense. -/
theorem dense_range_affineChart : Dense (Set.range W.affineChart.base) := by
  have hne : (Set.range W.affineChart.base).Nonempty := by
    have : Nonempty (Spec (CommRingCat.of W.toAffine.CoordinateRing)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum W.toAffine.CoordinateRing))
    exact Set.range_nonempty _
  exact W.affineChart.isOpenEmbedding.isOpen_range.dense hne

/-- **A Weierstrass cubic over a field is an integral proper curve.** Let `F` be a field and let
`W` be a Weierstrass curve over `F`, of any discriminant, with projective curve
`C = Proj (F[X, Y, Z] / (F_W))`, the zero scheme in `ℙ²_F` of
`Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³`. Then `C` is an integral scheme, the
structure morphism `C ⟶ Spec F` is proper, `C` has topological Krull dimension `1`, and the image
of the affine chart `Spec A_W ⟶ C`, the open subscheme `C ∩ {Z ≠ 0}` with
`A_W = F[x, y] / (y² + (a₁ x + a₃) y - x³ - a₂ x² - a₄ x - a₆)`, is dense in `C`.

Source: B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2 ("the 1-dimensional special
fiber of such a `W` is geometrically irreducible and geometrically reduced"; the geometric
statements are not formalized here, only integrality over `F`); J. S. Milne, *Elliptic Curves*,
2nd ed., author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, equation (9),
p. 45, referred back to on p. 46. -/
theorem isIntegral_isProper_dim_one_dense_affineChart :
    IsIntegral W.ProjectiveScheme ∧ IsProper W.projectiveSchemeToSpec ∧
      topologicalKrullDim W.ProjectiveScheme = 1 ∧ Dense (Set.range W.affineChart.base) :=
  ⟨inferInstance, inferInstance, W.topologicalKrullDim_projectiveScheme, W.dense_range_affineChart⟩

end WeierstrassCurve
