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
# Intermediate-extension providers and normalized intersection complexes

This row extends PR1970 to IC/intermediate extension. It imports only its
completed definition cores, and repeats neither its perverse-provider requests
nor decomposition requests. Exact inverse image and abelian perverse hearts
are displayed toolbox assumptions on the actual functors/categories.

Source: BBD (1982), §1.4; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, §§2.1 and 2.3.
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
    [Abelian (PerverseSheaf U)] [Abelian (PerverseSheaf X)]
    (j : U ⟶ X) [IsOpenImmersion j.left] [OpenRestrictionExact j] :
    IntermediateExtensionData j

/-- Middle extension is full; ordinary sheaf simplicity is not substituted
for simplicity in the perverse/local-system categories. -/
public theorem_wanted intermediateExtension_full {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    [Abelian (PerverseSheaf U)] [Abelian (PerverseSheaf X)]
    (j : U ⟶ X) [IsOpenImmersion j.left] [OpenRestrictionExact j] :
    (❰intermediateExtension❱ j).functor.Full

/-- The concrete minimal-extension conditions determine the functor up to
natural isomorphism. -/
public theorem_wanted intermediateExtension_unique {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    [Abelian (PerverseSheaf U)] [Abelian (PerverseSheaf X)]
    (j : U ⟶ X) [IsOpenImmersion j.left] [OpenRestrictionExact j]
    (J J' : IntermediateExtensionData j) : Nonempty (J.functor ≅ J'.functor)

end WantedExt.AlgebraicGeometry.IntersectionComplexesWanted
