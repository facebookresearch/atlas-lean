/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationFiniteRelativeFactor

/-!
# Tests for finite relative factorization

These clients pin the complete retained-restriction equation, the ambient
factor equation, arbitrary restriction domains, empty and universal set
boundaries, independent universes, and the absence of a global finite-support
choice or later approximation surface.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Topology
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace SSetRealizationFiniteRelativeFactorTests

section SymbolicRestriction

variable {X : SSet.{u}} {K L : TopCat.{u}} [CompactSpace K]
variable (B : X.Subcomplex) (hB : SSet.Finite (B : SSet.{u}))
variable (i : L ⟶ K)
variable (b : L ⟶ SSet.toTop.obj (B : SSet.{u}))
variable (f : K ⟶ SSet.toTop.obj X)
variable (hrestrict : i ≫ f = b ≫ SSet.toTop.map B.ι)

/-- The exact relative equation is returned first, followed by the ambient
factor equation. -/
example :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      i ≫ g =
          b ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBA) ∧
        f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
    B hB i b f hrestrict

end SymbolicRestriction

section EmptyRestrictionDomain

/-- An empty restriction domain recovers ordinary finite support without any
compactness, closedness, or nonemptiness assumption on the restriction
domain. -/
example {X : SSet.{u}} {K : TopCat.{u}} [CompactSpace K]
    (f : K ⟶ SSet.toTop.obj X)
    (hB : SSet.Finite ((⊥ : X.Subcomplex) : SSet.{u}))
    (i : (TopCat.of PEmpty : TopCat.{u}) ⟶ K)
    (b : (TopCat.of PEmpty : TopCat.{u}) ⟶
      SSet.toTop.obj ((⊥ : X.Subcomplex) : SSet.{u})) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hBA : (⊥ : X.Subcomplex) ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      i ≫ g =
          b ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBA) ∧
        f = g ≫ SSet.toTop.map A.ι := by
  apply SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
    (⊥ : X.Subcomplex) hB i b f
  apply ConcreteCategory.hom_ext
  intro z
  exact PEmpty.elim z

end EmptyRestrictionDomain

section MapsTo

variable {X : SSet.{u}} {K : TopCat.{u}} [CompactSpace K]
variable (B : X.Subcomplex) (hB : SSet.Finite (B : SSet.{u}))
variable (f : K ⟶ SSet.toTop.obj X)

/-- The empty prescribed set is accepted without any additional condition. -/
example :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      Set.MapsTo g (∅ : Set K)
          (Set.range
            (SSet.toTop.map (SSet.Subcomplex.homOfLE hBA))) ∧
        f = g ≫ SSet.toTop.map A.ι := by
  apply SSet.exists_finite_subcomplex_factor_topCatHom_of_mapsTo
    B hB ∅ f
  intro z hz
  exact hz.elim

/-- A universal-set hypothesis is retained as landing in the realized
prescribed subcomplex inside the finite enlargement. -/
example
    (hS : Set.MapsTo f Set.univ
      (Set.range (SSet.toTop.map B.ι))) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      Set.MapsTo g Set.univ
          (Set.range
            (SSet.toTop.map (SSet.Subcomplex.homOfLE hBA))) ∧
        f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom_of_mapsTo
    B hB Set.univ f hS

end MapsTo

section Universes

example {X : SSet.{0}} {K L : TopCat.{0}} [CompactSpace K]
    (B : X.Subcomplex) (hB : SSet.Finite (B : SSet.{0}))
    (i : L ⟶ K) (b : L ⟶ SSet.toTop.obj (B : SSet.{0}))
    (f : K ⟶ SSet.toTop.obj X)
    (hrestrict : i ≫ f = b ≫ SSet.toTop.map B.ι) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{0}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{0})),
      i ≫ g =
          b ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBA) ∧
        f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
    B hB i b f hrestrict

example {X : SSet.{1}} {K L : TopCat.{1}} [CompactSpace K]
    (B : X.Subcomplex) (hB : SSet.Finite (B : SSet.{1}))
    (i : L ⟶ K) (b : L ⟶ SSet.toTop.obj (B : SSet.{1}))
    (f : K ⟶ SSet.toTop.obj X)
    (hrestrict : i ≫ f = b ≫ SSet.toTop.map B.ι) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{1}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{1})),
      i ≫ g =
          b ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBA) ∧
        f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
    B hB i b f hrestrict

end Universes

section SurfaceAndNonclaims

#check SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
#check SSet.exists_finite_subcomplex_factor_topCatHom_of_mapsTo

#guard_msgs (error, substring := true) in
#check SSet.finite_sup_subcomplex_relative

#guard_msgs (error, substring := true) in
#check SSet.finiteSubcomplexFactorChoice

#guard_msgs (error, substring := true) in
#check SSet.exists_finite_subcomplex_factor_homotopyRel

#guard_msgs (error, substring := true) in
#check SSet.exists_finite_nonsingular_subcomplex_factor_topCatHom

#guard_msgs (error, substring := true) in
#check SSet.finiteSubcomplex_simplicialApproximation

end SurfaceAndNonclaims

#print axioms SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
#print axioms SSet.exists_finite_subcomplex_factor_topCatHom_of_mapsTo

end SSetRealizationFiniteRelativeFactorTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
