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

public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.CyclicEvenResolutionComparison

/-!
# Quotient representatives for the cyclic degree-two comparison

Let k be a commutative ring, G a finite abelian group, A a k-linear representation in universe
u, and g∈G. With N_G=Σ_{h∈G}ρ(h), the short complex A --N_G→ A --(ρ(g)-id)→ A has concrete
homology ker(ρ(g)-id)/im(N_G).

The comparison from inhomogeneous degree-two cohomology to this quotient sends a cocycle z to
the class of ν_g(z)=Σ_{h∈G}z(h,g). The cycle map produces this g-fixed vector, and naturality of
the homology projection gives the representative formula on H²(G,A). No generator hypothesis is
needed to define this comparison.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace groupCohomology
universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in the
given universe u. For g∈G, put N_G=Σ_{h∈G}ρ(h) and Q_g(A)=ker(ρ(g)-id)/im(N_G). The comparison
H²(G,A)→Q_g(A) is induced by the map from the degree-two inhomogeneous short complex to A --N_G→
A --(ρ(g)-id)→ A, followed by its concrete homology quotient. -/
noncomputable def cyclicEvenComparisonQuotientMap (A : Rep k G) (g : G) :
    H2 A ⟶
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.H :=
  (H2Iso A).hom ≫
    ShortComplex.leftHomologyMap'
      (cyclicEvenComparisonHom A g)
      (shortComplexH2 A).moduleCatLeftHomologyData
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in the
given universe u. For g∈G and a two-cocycle z∈Z²(G,A), the induced cycle map of the cyclic
short-complex comparison sends z to ν_g(z)=Σ_{h∈G}z(h,g), viewed in ker(ρ(g)-id). Both source
and target use their concrete coefficient-module cycle descriptions. -/
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
/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in the
given universe u. For g∈G and z∈Z²(G,A), let [z]∈H²(G,A) be its class and ν_g(z)=Σ_{h∈G}z(h,g)
the g-fixed cyclic invariant. The quotient comparison sends [z] to [ν_g(z)] in
ker(ρ(g)-id)/im(N_G), where N_G is the representation norm. -/
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
