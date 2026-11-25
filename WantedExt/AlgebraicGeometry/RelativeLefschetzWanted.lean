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

The relatively very ample direction is fixed by an actual closed embedding
over `Y` into `Y ×_ℂ ℙⁿ`. A nonzero class of the actual `H²(ℙⁿ, ℚ)` for
`n ≥ 1` is a nonzero scalar multiple of the hyperplane class. Its pulled-back
power is mapped through the actual derived direct image and actual perverse
cohomology. Arbitrary classes of `H²(X, ℚ)` are not treated as ample.

The request also asserts that the direct image `Rf_* ℚ_X[d]` is bounded
constructible, so that its perverse cohomology is defined; it does not assume
it. The comparison isomorphisms of the pullback/direct-image pipeline (the
standard identifications of constant sheaves under shift and inverse image,
and of `Rf_*` with shifts) are constructed by a request in this file rather
than assumed; being isomorphisms, they do not affect whether the power map is
invertible. The perverse t-structure is the characterized
`[PerverseSheafTheory Y]`, unique when it exists.

Sources: A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
Astérisque 100 (1982), Theorem 6.2.10; M. A. de Cataldo and L. Migliorini,
https://arxiv.org/abs/0712.0349, Theorem 1.6.3.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeLefschetzWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves RelativeLefschetz

attribute [local instance] HasDerivedCategory.standard

/-- The comparison isomorphisms of the hyperplane pipeline exist. -/
public def_wanted hyperplaneComparisons {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) (d k : ℕ) : HyperplaneComparisons E d k

/-- Relative hard Lefschetz (Beilinson–Bernstein–Deligne, Theorem 6.2.10): let $X$ and $Y$ be
complex varieties, with the given perverse t-structure on $Y$ (`PerverseSheafTheory Y`), $X$ smooth
of relative dimension $d$ over $ℂ$, $f : X → Y$ proper with a closed embedding `E` of $X$ into
$Y × \mathbb P^n$ over $Y$, where $n ≥ 1$, and $η ∈ H^2(\mathbb P^n, \mathbb Q)$ nonzero. Then
$Rf_*\mathbb Q_X[d]$ is bounded constructible, and for every $k$ the $k$-th power of the pullback of
$η$ induces an isomorphism ${}^pH^{-k}(Rf_*\mathbb Q_X[d]) → {}^pH^{k}(Rf_*\mathbb Q_X[d])$. -/
public theorem_wanted relative_hard_lefschetz (X Y : ComplexScheme)
    [IsComplexVariety X] [IsComplexVariety Y] [PerverseSheafTheory Y]
    (d n k : ℕ) [SmoothOfRelativeDimension d X.hom] (hn : 1 ≤ n)
    (f : X ⟶ Y) [IsProper f.left] (E : RelativeProjectiveEmbedding f n)
    (η : unitComplex (ProjectiveSpace.projectiveSpace ℂ n) ⟶ (unitComplex (ProjectiveSpace.projectiveSpace ℂ n))⟦(2 : ℤ)⟧)
    (hη : η ≠ 0) :
    ∃ hK : boundedConstructible Y (ConstructibleComplexes.normalizedDirectImage ℚ X Y f d),
      IsIso (perversePowerMap Y ⟨_, hK⟩ k
        (hyperplaneImageMap E d k η (❰hyperplaneComparisons❱ E d k)))

end WantedExt.AlgebraicGeometry.RelativeLefschetzWanted
