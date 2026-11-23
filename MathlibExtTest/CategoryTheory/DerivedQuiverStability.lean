/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DerivedQuiverStability

@[expose] public section

namespace MathlibExt.CategoryTheory.DerivedQuiverStability

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

variable (k V : Type) [Field k] [Quiver V] [Fintype V]

-- The central charge is additive and sends a vertex vector to the vertex charge.
example (z : V → ℂ) [DecidableEq V] (v : V) :
    centralCharge V z (Pi.single v 1) = z v := by
  simp [centralCharge, Pi.single_apply]

example (z : V → ℂ) : centralCharge V z 0 = 0 := map_zero _

-- The zero object is bounded: all its cohomology vanishes.
example : Bounded k V 0 :=
  Set.finite_empty.subset fun n hn ↦
    hn (Functor.map_isZero (DerivedCategory.homologyFunctor (Representations k V) n)
      (isZero_zero (D k V)))

-- Elements of the bounded subcategory are bounded objects.
example (K : BoundedDerivedQuiver k V) : Bounded k V K.obj := K.property

-- Slicing objects are bounded, so their charge is defined.
noncomputable example (z : V → ℂ) (phi : ℝ) (K : D k V) (hK : slicing k V z phi K) : ℂ :=
  derivedCharge k V z K hK.1

end MathlibExt.CategoryTheory.DerivedQuiverStability
