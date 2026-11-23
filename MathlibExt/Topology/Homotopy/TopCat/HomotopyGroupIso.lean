/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Positive homotopy groups under topological isomorphisms

Transfer triviality of positive homotopy groups along a topological
isomorphism, preserving the induced maps and actual basepoints. The proof
uses the existing loop-shift and pointed homotopy-group comparison APIs.
-/

@[expose] public section

universe u

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology Topology.Homotopy

namespace TopCat

section Part1


private theorem positiveMapOfEq_congr
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (n : ℕ) {a : A} {b : B} (f g : C(A, B))
    (hf : f a = b) (hg : g a = b) (hfg : f = g) :
    HomotopyGroup.mapHomOfEq f hf n = HomotopyGroup.mapHomOfEq g hg n := by
  cases hfg
  rfl

/-- An actual topological Iso transports subsingleton positive groups via
its original maps and their exact inverse equations. -/
theorem positiveGroup_subsingleton_of_iso
    (n : ℕ) {X Y : TopCat.{u}} (d : X ≅ Y)
    (hX : ∀ x : X, Subsingleton (HomotopyGroup.Pi (n + 1) X x)) (y : Y) :
    Subsingleton (HomotopyGroup.Pi (n + 1) Y y) := by
  let f : C(Y, X) := d.inv.hom
  let g : C(X, Y) := d.hom.hom
  have hg : g (f y) = y := ConcreteCategory.congr_hom d.inv_hom_id y
  have hfg : g.comp f = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    intro z
    exact ConcreteCategory.congr_hom d.inv_hom_id z
  have hBack (a : HomotopyGroup.Pi (n + 1) Y y) :
      HomotopyGroup.mapHomOfEq g hg n (HomotopyGroup.map f a) = a := by
    have hComp : HomotopyGroup.mapHomOfEq (g.comp f) hg n a =
        HomotopyGroup.mapHomOfEq g hg n (HomotopyGroup.map f a) :=
      HomotopyGroup.mapHomOfEq_comp f g rfl hg hg n a
    have hId := positiveMapOfEq_congr n (g.comp f) (ContinuousMap.id Y) hg rfl hfg
    have h1 : HomotopyGroup.mapHomOfEq g hg n (HomotopyGroup.map f a) =
        HomotopyGroup.mapHomOfEq (g.comp f) hg n a := hComp.symm
    have h2 : HomotopyGroup.mapHomOfEq (g.comp f) hg n a =
        HomotopyGroup.mapHomOfEq (ContinuousMap.id Y) rfl n a :=
      congrArg (fun k : HomotopyGroup.Pi (n + 1) Y y →ₙ* HomotopyGroup.Pi (n + 1) Y y => k a) hId
    have h3 : HomotopyGroup.mapHomOfEq (ContinuousMap.id Y) rfl n a = a :=
      HomotopyGroup.mapHomOfEq_id y n a
    exact h1.trans (h2.trans h3)
  constructor
  intro a b
  have hMap : HomotopyGroup.map f a = HomotopyGroup.map f b := (hX (f y)).elim _ _
  exact (hBack a).symm.trans
    ((congrArg (HomotopyGroup.mapHomOfEq g hg n) hMap).trans (hBack b))

end Part1

end TopCat

end
