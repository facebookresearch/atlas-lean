/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

/-!
# Proper images, semismall defect and support data

The normalized image of `f : X ⟶ Y` is the actual `Rf_* ℚ_X[d]`,
`ConstructibleComplexes.normalizedDirectImage ℚ X Y f d`: the derived direct
image of the rational constant sheaf placed in cohomological degree `-d`. Here
it is packaged as a bounded constructible complex. The defect bound is
geometric: `dim (X ×_Y X) ≤ d + r`, measured on the actual scheme fiber
product. Fibers over complex points are actual scheme pullbacks.

Everything here is a complete definition. The decomposition, semisimplicity,
amplitude and relevance statements, and the constructibility of the image, are
requested in `WantedExt/AlgebraicGeometry/ProperDecompositionWanted.lean`.

## References

* M. A. de Cataldo and L. Migliorini, *The decomposition theorem, perverse
  sheaves and the topology of algebraic maps*, https://arxiv.org/abs/0712.0349,
  Theorem 1.6.1, §§3.3.2 and 4.2.
* A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
  Astérisque 100 (1982), Theorem 6.2.5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperDecomposition

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- The rational image `Rf_* ℚ_X[d]` as an object of the bounded constructible
category, given its constructibility. -/
def constructibleImage (X Y : ComplexScheme) (f : X ⟶ Y) (d : ℕ)
    (hK : boundedConstructible Y (ConstructibleComplexes.normalizedDirectImage ℚ X Y f d)) :
    (boundedConstructible Y).FullSubcategory :=
  ⟨ConstructibleComplexes.normalizedDirectImage ℚ X Y f d, hK⟩

/-- Geometric defect bound: the self-fiber product `X ×_Y X` has Krull
dimension at most `d + r`. For `X` smooth of dimension `d`, the least such `r`
is the defect of semismallness of `f`. -/
def DefectLE {X Y : ComplexScheme} (f : X ⟶ Y) (d r : ℕ) : Prop :=
  topologicalKrullDim (pullback f.left f.left : Scheme.{0}) ≤
    ((d + r : ℕ∞) : WithBot ℕ∞)

/-- The actual fiber over a complex point, as a scheme pullback. -/
def pointFiber {X Y : ComplexScheme} (f : X ⟶ Y) (p : space Y) : Scheme.{0} :=
  pullback f.left p.hom

end MathlibExt.AlgebraicGeometry.ProperDecomposition
