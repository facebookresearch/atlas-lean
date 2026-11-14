/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.PerverseSheaves
public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage

@[expose] public noncomputable section

/-!
# Smooth proper perverse and ordinary filtration comparison

For a smooth proper map of relative dimension `d` to a smooth base of
dimension `m`, the perverse truncation at `k-d` of
`Rf_* ℚ_X[m+d]` compares with the ordinary truncation at `k-(m+d)`.
The inclusion into the actual direct image fixes the comparison.

The shift is essential: on the smooth base a local system shifted by `m`
is perverse. No multiplicativity theorem for a singular map is assumed.

References: de Cataldo–Migliorini, *The decomposition theorem, perverse
sheaves and the topology of algebraic maps*, §§1.6–1.7,
https://arxiv.org/abs/0712.0349; *The Hodge theory of algebraic maps*, §3.6,
https://arxiv.org/abs/math/0306030.
-/

namespace WantedExt.AlgebraicGeometry.SmoothPerverseFiltrationComparisonWanted

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.MathlibExt.AlgebraicGeometry.PerverseSheaves
open _root_.MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted

attribute [local instance] HasDerivedCategory.standard

/-- The canonical comparison of filtration truncations in the smooth proper
case, with commutation against their actual inclusion maps. -/
public def_wanted smoothPerverseTruncationComparison
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    [PerverseSheafTheory Y] (f : X ⟶ Y) (d m : ℕ)
    [IsProper f.left] [SmoothOfRelativeDimension d f.left]
    [SmoothOfRelativeDimension m Y.hom]
    (hK : boundedConstructible Y (normalizedDirectImage X Y f (m + d)))
    (k : ℤ) :
    let K := normalizedDirectImage X Y f (m + d)
    let KC : (boundedConstructible Y).FullSubcategory := ⟨K, hK⟩
    let t := perverseTStructure Y
    let u := DerivedCategory.TStructure.t (C := RationalSheaf
      (MathlibExt.AlgebraicGeometry.ComplexAnalytification.space Y))
    {e : (boundedConstructible Y).ι.obj ((t.truncLE (k - d)).obj KC) ≅
        (u.truncLE (k - (m + d : ℕ))).obj K //
      e.hom ≫ (u.truncLEι (k - (m + d : ℕ))).app K =
        (boundedConstructible Y).ι.map ((t.truncLEι (k - d)).app KC)}

end WantedExt.AlgebraicGeometry.SmoothPerverseFiltrationComparisonWanted
