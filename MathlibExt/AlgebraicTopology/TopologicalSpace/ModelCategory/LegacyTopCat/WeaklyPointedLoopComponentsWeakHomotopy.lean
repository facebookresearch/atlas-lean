/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.ZerothHomotopyWeakHomotopy
public import MathlibExt.Topology.Homotopy.LoopComponentsMap
public import MathlibExt.Topology.Homotopy.WeaklyPointedMap

/-!
# Weak homotopy equivalences and weakly pointed loop components

Applying the neutral zeroth-homotopy weak-invariance bridge to the continuous
loop map of a weakly pointed map gives bijectivity on loop components and,
through the canonical loop-component description of the fundamental group,
a multiplicative equivalence of fundamental groups.

The component map itself is mixed-universe and has the literal conjugation
formula determined by the chosen root path.  The weak-equivalence bridge is
same-universe.  This file installs no group structure on loop components and
constructs no continuous inverse, pointed equivalence, homotopy equivalence,
or spectrum map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe w v u

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- The map on path components of loop spaces induced by a weakly pointed
map. -/
noncomputable def loopComponentsMap (f : WeaklyPointed x y) :
    ZerothHomotopy (LoopSpace X x) →
      ZerothHomotopy (LoopSpace Y y) :=
  _root_.loopComponentsMap f.hom f.rootPath

/-- On a representative, the weakly pointed component map is induced by the
literal conjugated loop map. -/
@[simp]
theorem loopComponentsMap_mk
    (f : WeaklyPointed x y) (gamma : LoopSpace X x) :
    f.loopComponentsMap (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk (f.loopMap gamma) := by
  exact _root_.loopComponentsMap_mk f.hom f.rootPath gamma

/-- Maps on loop components respect weakly pointed composition, in
source-first order. -/
theorem loopComponentsMap_comp
    (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    (f.comp g).loopComponentsMap =
      g.loopComponentsMap ∘ f.loopComponentsMap := by
  funext q
  induction q using ZerothHomotopy.rec with
  | mk gamma =>
      simp only [loopComponentsMap_mk, Function.comp_apply]
      exact zerothHomotopy_mk_eq_of_pathHomotopic
        (loopMap_comp_homotopic f g gamma)

/-- In one universe, the weakly pointed component map is the ordinary
zeroth-homotopy map of the continuous loop map. -/
theorem loopComponentsMap_eq_zerothHomotopyMap
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : WeaklyPointed x y) :
    f.loopComponentsMap =
      TopCat.zerothHomotopyMap (TopCat.ofHom f.loopMap) := by
  funext q
  induction q using ZerothHomotopy.rec with
  | mk gamma =>
      rw [loopComponentsMap_mk, TopCat.zerothHomotopyMap_mk]
      rfl

/-- A weak equivalence on loop spaces makes the induced map on loop
components bijective. -/
theorem loopComponentsMap_bijective_of_loopMap_weakEquivalence
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap)) :
    Function.Bijective f.loopComponentsMap := by
  rw [loopComponentsMap_eq_zerothHomotopyMap f]
  exact hf.bijective_zerothHomotopyMap

/-- A weak equivalence on loop spaces makes the induced homomorphism on
fundamental groups bijective. -/
theorem basedFundamentalGroupMap_bijective_of_loopMap_weakEquivalence
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap)) :
    Function.Bijective
      (_root_.basedFundamentalGroupMap f.hom f.rootPath) := by
  let eX := loopComponentsEquivFundamentalGroup X x
  let eY := loopComponentsEquivFundamentalGroup Y y
  have hc :=
    loopComponentsMap_bijective_of_loopMap_weakEquivalence f hf
  change Function.Bijective
    (eY.symm ∘ _root_.basedFundamentalGroupMap f.hom f.rootPath ∘ eX) at hc
  have hright : Function.Bijective
      (_root_.basedFundamentalGroupMap f.hom f.rootPath ∘ eX) :=
    (Function.Bijective.of_comp_iff' eY.symm.bijective _).mp hc
  exact (Function.Bijective.of_comp_iff _ eX.bijective).mp hright

/-- A weak equivalence on loop spaces induces a multiplicative equivalence
of fundamental groups.  Its forward map is the existing root-path
conjugation homomorphism. -/
noncomputable def fundamentalGroupMulEquivOfLoopMapWeakEquivalence
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap)) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  MulEquiv.ofBijective (_root_.basedFundamentalGroupMap f.hom f.rootPath)
    (basedFundamentalGroupMap_bijective_of_loopMap_weakEquivalence f hf)

end ContinuousMap.WeaklyPointed
