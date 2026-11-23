/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationFiniteFactor

/-!
# Tests for compact finite factorization in simplicial realizations

The clients pin universe-zero and universe-one compact sources, exact factor
equations, the point and interval boundaries, and the literal lifted realized
vertex supplied by the based theorem.  No simplicial approximation,
nullhomotopy, homotopy-group, or weak-equivalence conclusion is tested or
introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Topology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace SSetRealizationFiniteFactorTests

section TypeZero

variable {X : SSet.{0}} {K : TopCat.{0}} [CompactSpace K]

example (f : K ⟶ SSet.toTop.obj X) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{0}))
      (g : K ⟶ SSet.toTop.obj (A : SSet.{0})),
      f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom f

example (x : X _⦋0⦌) (k : K)
    (f : K ⟶ SSet.toTop.obj X)
    (hk : f k = SSet.realizedVertex x) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{0}))
      (hx : x ∈ A.obj (op ⦋0⦌))
      (g : K ⟶ SSet.toTop.obj (A : SSet.{0})),
      g k = SSet.realizedVertex
          (⟨x, hx⟩ : (A : SSet.{0}) _⦋0⦌) ∧
        f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom_at_realizedVertex x k f hk

end TypeZero

section TypeOne

variable {X : SSet.{1}} {K : TopCat.{1}} [CompactSpace K]

example (f : K ⟶ SSet.toTop.obj X) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{1}))
      (g : K ⟶ SSet.toTop.obj (A : SSet.{1})),
      f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom f

example (x : X _⦋0⦌) (k : K)
    (f : K ⟶ SSet.toTop.obj X)
    (hk : f k = SSet.realizedVertex x) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{1}))
      (hx : x ∈ A.obj (op ⦋0⦌))
      (g : K ⟶ SSet.toTop.obj (A : SSet.{1})),
      g k = SSet.realizedVertex
          (⟨x, hx⟩ : (A : SSet.{1}) _⦋0⦌) ∧
        f = g ≫ SSet.toTop.map A.ι :=
  SSet.exists_finite_subcomplex_factor_topCatHom_at_realizedVertex x k f hk

end TypeOne

section PointAndInterval

variable {X : SSet.{0}}

example (x : X _⦋0⦌) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{0}))
      (hx : x ∈ A.obj (op ⦋0⦌))
      (g : TopCat.of PUnit ⟶ SSet.toTop.obj (A : SSet.{0})),
      g PUnit.unit = SSet.realizedVertex
          (⟨x, hx⟩ : (A : SSet.{0}) _⦋0⦌) ∧
        TopCat.ofHom (ContinuousMap.const PUnit (SSet.realizedVertex x)) =
          g ≫ SSet.toTop.map A.ι := by
  let f : TopCat.of PUnit ⟶ SSet.toTop.obj X :=
    TopCat.ofHom (ContinuousMap.const PUnit (SSet.realizedVertex x))
  have hk : f PUnit.unit = SSet.realizedVertex x := rfl
  exact SSet.exists_finite_subcomplex_factor_topCatHom_at_realizedVertex
    x PUnit.unit f hk

example (f : TopCat.I ⟶ SSet.toTop.obj X) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{0}))
      (g : TopCat.I ⟶ SSet.toTop.obj (A : SSet.{0})),
      f = g ≫ SSet.toTop.map A.ι := by
  let _ : CompactSpace TopCat.I :=
    TopCat.I.homeomorph.symm.compactSpace
  exact SSet.exists_finite_subcomplex_factor_topCatHom f

end PointAndInterval

section ScopeGuards

variable (X : SSet.{0})

#guard_msgs (error, substring := true) in
#synth SSet.Finite X

#guard_msgs (error, substring := true) in
#check SSet.finite_sup_subcomplex_for_factor

#guard_msgs (error, substring := true) in
#check SSet.finiteSubcomplexFactorTopCatHom

#guard_msgs (error, substring := true) in
#check SSet.exists_finite_nonsingular_factor_topCatHom

#guard_msgs (error, substring := true) in
#check SSet.FiniteNonsingularLastVertexNullity

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalence_to_point_of_finiteNonsingularLastVertexNullity

#guard_msgs (error, substring := true) in
#check SSet.exists_finite_subcomplex_factor_topCatHom_nullhomotopic

#guard_msgs (error, substring := true) in
#check SSet.exists_finite_subcomplex_factor_topCatHom_homotopyGroup

#guard_msgs (error, substring := true) in
#synth ContractibleSpace (SSet.toTop.obj X)

end ScopeGuards

#print axioms SSet.exists_finite_subcomplex_factor_topCatHom
#print axioms SSet.exists_finite_subcomplex_factor_topCatHom_at_realizedVertex

end SSetRealizationFiniteFactorTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

end
