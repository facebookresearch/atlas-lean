/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CyclicEvenResolutionComparison

/-!
# Quotient formula for the explicit cyclic-even H2 comparison

The explicit short-complex comparison from inhomogeneous degree-two
cochains to the cyclic even complex induces a map from ordinary H2 to the
concrete quotient of `ker(ρ(g)-1)` by the representation norm.  On a class
represented by a two-cocycle `z`, this map is represented by the explicit
invariant `∑ h, z(h,g)`.

This gives the quotient-level representative formula needed to analyze
Kummer cup classes.  It does not identify the map with Mathlib's separately
constructed abstract projective-resolution isomorphism: that comparison
requires extending the low-degree morphism to a full augmented resolution
map and applying homotopy uniqueness.  Consequently no cyclic symbol
surjectivity or Brauer-group theorem is asserted here.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace groupCohomology
universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- Map from ordinary H2 to the concrete homology quotient of the cyclic
even complex. -/
noncomputable def cyclicEvenComparisonQuotientMap (A : Rep k G) (g : G) :
    H2 A ⟶
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.H :=
  (H2Iso A).hom ≫
    ShortComplex.leftHomologyMap'
      (cyclicEvenComparisonHom A g)
      (shortComplexH2 A).moduleCatLeftHomologyData
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData

/-- On explicit cycles, the comparison's cycle map is the cyclic invariant
`∑ h, z(h,g)`. -/
theorem cyclesMap_cyclicEvenComparisonHom_apply
    (A : Rep k G) (g : G) (z : cocycles₂ A) :
    ShortComplex.cyclesMap'
        (cyclicEvenComparisonHom A g)
        (shortComplexH2 A).moduleCatLeftHomologyData
        (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData z =
      cyclicTwoCocycleInvariant A g z := by
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The quotient comparison sends the class of `z` to the quotient class of
its explicit cyclic invariant. -/
theorem cyclicEvenComparisonQuotientMap_H2π
    (A : Rep k G) (g : G) (z : cocycles₂ A) :
    cyclicEvenComparisonQuotientMap A g (H2π A z) =
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.π
        (cyclicTwoCocycleInvariant A g z) := by
  have hH2m : H2π A ≫ (H2Iso A).hom =
      (shortComplexH2 A).moduleCatLeftHomologyData.π := by
    simp [H2π, Category.assoc]
  have hm : H2π A ≫ cyclicEvenComparisonQuotientMap A g =
      ShortComplex.cyclesMap'
          (cyclicEvenComparisonHom A g)
          (shortComplexH2 A).moduleCatLeftHomologyData
          (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData ≫
        (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.π := by
    unfold cyclicEvenComparisonQuotientMap
    rw [← Category.assoc, hH2m]
    exact ShortComplex.leftHomologyπ_naturality'
        (cyclicEvenComparisonHom A g)
        (shortComplexH2 A).moduleCatLeftHomologyData
        (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData
  have hz := ConcreteCategory.congr_hom hm z
  change cyclicEvenComparisonQuotientMap A g (H2π A z) = _
  rw [← cyclesMap_cyclicEvenComparisonHom_apply A g z]
  exact hz

end groupCohomology
