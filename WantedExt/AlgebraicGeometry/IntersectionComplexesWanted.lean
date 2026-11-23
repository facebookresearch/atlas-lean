/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.IntersectionComplexes

/-!
# Intermediate extension and normalized intersection complexes

Request the perversity of `L[d]` for a finite-rank local system `L` on a
smooth complex variety of pure dimension `d`, and the existence, fullness and
uniqueness up to natural isomorphism of intermediate extension along an open
immersion of complex varieties, characterized by its restriction and the
absence of boundary-supported subobjects and quotients.

Sources: A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
Astérisque 100 (1982), §1.4; M. A. de Cataldo and
L. Migliorini, https://arxiv.org/abs/0712.0349, §§2.1 and 2.3.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IntersectionComplexesWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves IntersectionComplexes

attribute [local instance] HasDerivedCategory.standard

/-- Construct the normalized local system in the characterized perverse heart
on a smooth pure-dimensional complex variety. -/
public def_wanted localSystemPerverseRealization (U : ComplexScheme)
    [IsComplexVariety U] [PerverseSheafTheory U] (d : ℕ)
    [SmoothOfRelativeDimension d U.hom] (L : RationalSheaf (space U))
    (hL : IsFiniteRankLocalSystem (space U) L) :
    LocalSystemPerverseRealization U L d

/-- Construct the actual middle extension, with natural restriction and no
boundary subobjects/quotients. -/
public def_wanted intermediateExtension {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    IntermediateExtensionData j

/-- Middle extension is full; ordinary sheaf simplicity is not substituted
for simplicity in the perverse/local-system categories. -/
public theorem_wanted intermediateExtension_full {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    (❰intermediateExtension❱ j).functor.Full

/-- The concrete minimal-extension conditions determine the functor up to
natural isomorphism. -/
public theorem_wanted intermediateExtension_unique {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (J J' : IntermediateExtensionData j) : Nonempty (J.functor ≅ J'.functor)

end WantedExt.AlgebraicGeometry.IntersectionComplexesWanted
