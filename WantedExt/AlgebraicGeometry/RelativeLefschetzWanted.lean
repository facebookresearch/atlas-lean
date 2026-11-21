/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeLefschetz

/-!
# Geometric relative hard Lefschetz

The relatively very-ample direction is fixed by an actual closed embedding
over `Y` into `Y × P^n`. A nonzero class of the actual `H²(P^n,Q)` for `n≥1`
is a nonzero scalar multiple of the hyperplane generator. Its pulled-back
power is mapped through actual derived direct image and actual perverse
cohomology. Arbitrary classes of `H²(X,Q)` are not treated as ample.

The completed comparisons/operators are in the proved core; this file asks
only the scoped isomorphism theorem, beyond the decomposition requests of
PR1970. Source: BBD (1982), Theorem 6.2.10; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, Theorem 1.6.3.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeLefschetzWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves RelativeLefschetz

attribute [local instance] HasDerivedCategory.standard

/-- Relative hard Lefschetz for the geometrically relatively very-ample
direction, including every nonzero scalar normalization of the projective
hyperplane generator. -/
public theorem_wanted relative_hard_lefschetz (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d n k : ℕ) [SmoothOfRelativeDimension d X.hom] (hn : 1 ≤ n)
    (f : X ⟶ Y) [IsProper f.left] (E : RelativeProjectiveEmbedding f n)
    (η : unitComplex (projectiveSpace n) ⟶ (unitComplex (projectiveSpace n))⟦(2 : ℤ)⟧)
    (hη : η ≠ 0) (C : HyperplaneComparisons E d k)
    (hK : boundedConstructible Y (imageComplex f d)) :
    IsIso (perversePowerMap Y ⟨imageComplex f d, hK⟩ k (hyperplaneImageMap E d k η C))

end WantedExt.AlgebraicGeometry.RelativeLefschetzWanted
