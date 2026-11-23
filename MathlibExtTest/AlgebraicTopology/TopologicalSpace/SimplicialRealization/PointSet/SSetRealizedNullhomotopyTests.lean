/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedNullhomotopy

/-!
# Tests for realized simplicial nullhomotopies

These clients pin the realized constant endpoint and the common-source
orientation. No weak equivalence, chosen inverse, last-vertex cancellation,
contractibility, Approximation, or K-theory endpoint is imported or claimed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace SSetRealizedNullhomotopyTests

section Symbolic

universe u

variable {A Y : SSet.{u}} {r f : A ⟶ Y}
variable (y : Y _⦋0⦌)

example :
    (SSet.toTop.map (SSet.const (X := A) y)).hom =
      ContinuousMap.const _ (SSet.realizedVertex y) :=
  SSet.toTop_map_const_hom y

example (hrf : SSet.Homotopy r f)
    (hrconst : SSet.Homotopy r (SSet.const y)) :
    ContinuousMap.Nullhomotopic (SSet.toTop.map f).hom :=
  SSet.toTop_map_nullhomotopic_of_common_source y hrf hrconst

#guard_msgs (error, substring := true) in
example (hfr : SSet.Homotopy f r)
    (hrconst : SSet.Homotopy r (SSet.const y)) :
    ContinuousMap.Nullhomotopic (SSet.toTop.map f).hom :=
  SSet.toTop_map_nullhomotopic_of_common_source y hfr hrconst

end Symbolic

section Universes

example {A Y : SSet.{0}} (y : Y _⦋0⦌) :
    (SSet.toTop.map (SSet.const (X := A) y)).hom =
      ContinuousMap.const _ (SSet.realizedVertex y) :=
  SSet.toTop_map_const_hom y

example {A Y : SSet.{1}} (y : Y _⦋0⦌) :
    (SSet.toTop.map (SSet.const (X := A) y)).hom =
      ContinuousMap.const _ (SSet.realizedVertex y) :=
  SSet.toTop_map_const_hom y

end Universes

section SurfaceAndNonclaims

#check SSet.toTop_map_const_hom
#check SSet.toTop_map_nullhomotopic_of_common_source

#guard_msgs (error, substring := true) in
#check SSet.lastVertexRealizedHomotopyEquiv

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalence_to_point_of_finiteNonsingularLastVertexNullity

#guard_msgs (error, substring := true) in
#check SSet.nerveMap_mem_realizationWeakEquivalences_of_finiteNullity

end SurfaceAndNonclaims

#print axioms SSet.toTop_map_const_hom
#print axioms SSet.toTop_map_nullhomotopic_of_common_source

end SSetRealizedNullhomotopyTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
