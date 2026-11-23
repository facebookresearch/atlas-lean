/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.Contractible
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Tests for nullhomotopy invariance and homotopy-equivalence cancellation

These clients pin independent universes, invariance under an explicit
homotopy, and cancellation of precomposition only when a chosen
`ContinuousMap.HomotopyEquiv` is supplied.  No conversion from a weak
homotopy equivalence and no last-vertex or G3 conclusion is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContinuousMap

universe u v w

namespace MathlibExtTest.Topology.Homotopy
namespace ContractibleTests

section Symbolic

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example {f g : C(X, Y)}
    (hf : f.Nullhomotopic) (hfg : ContinuousMap.Homotopic f g) :
    g.Nullhomotopic :=
  hf.of_homotopic hfg

example (e : X ≃ₕ Y) (q : C(Y, Z))
    (h : (q.comp e.toFun).Nullhomotopic) :
    q.Nullhomotopic :=
  h.cancel_precomp_homotopyEquiv e q

example (f : C(X, Y)) (hf : f.Nullhomotopic) (x₀ x₁ : X) :
    Joined (f x₀) (f x₁) :=
  hf.joined_apply f x₀ x₁

example (f : C(X, Y)) (hf : f.Nullhomotopic) (x : X) :
    Joined (f x) (f x) :=
  hf.joined_apply f x x

end Symbolic

section Constant

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

example (y : Y) (x₀ x₁ : X) :
    Joined ((ContinuousMap.const X y) x₀)
      ((ContinuousMap.const X y) x₁) := by
  have h : (ContinuousMap.const X y).Nullhomotopic :=
    ⟨y, ContinuousMap.Homotopic.refl _⟩
  exact h.joined_apply (ContinuousMap.const X y) x₀ x₁

end Constant

section Identity

variable {X : Type u} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Z]

example (q : C(X, Z))
    (h : (q.comp (ContinuousMap.HomotopyEquiv.refl X).toFun).Nullhomotopic) :
    q.Nullhomotopic :=
  h.cancel_precomp_homotopyEquiv
    (ContinuousMap.HomotopyEquiv.refl X) q

end Identity

section MereWeakEquivalenceBoundary

#check TopCat.weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check ContinuousMap.Nullhomotopic.cancel_precomp_weakHomotopyEquivalence

end MereWeakEquivalenceBoundary

section Nonclaims

#guard_msgs (error, substring := true) in
#check SSet.lastVertexRealizedHomotopyEquiv

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalence_to_point_of_finiteNonsingularLastVertexNullity

#guard_msgs (error, substring := true) in
#check ContinuousMap.Nullhomotopic.pathConnectedSpace

#guard_msgs (error, substring := true) in
#check ContinuousMap.Nullhomotopic.contractibleSpace

end Nonclaims

#print axioms ContinuousMap.Nullhomotopic.joined_apply
#print axioms ContinuousMap.Nullhomotopic.of_homotopic
#print axioms ContinuousMap.Nullhomotopic.cancel_precomp_homotopyEquiv

end ContractibleTests
end MathlibExtTest.Topology.Homotopy

end
