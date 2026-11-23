/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.WeaklyPointedLoopComponentsWeakHomotopy

/-!
# Tests for weakly pointed loop components and weak homotopy equivalences

These clients pin the literal root-path conjugation formula on loop
representatives, mixed-universe composition, and the same-universe
fundamental-group equivalence obtained from a weak equivalence of loop
spaces.

No group structure on loop components, continuous inverse, pointed or
homotopy equivalence, Quillen comparison, K₀ square, or spectrum consequence
is added or tested.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open ContinuousMap.WeaklyPointed

universe w v u

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace WeaklyPointedLoopComponentsWeakHomotopyTests

section ComponentFormulas

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}
variable (f : ContinuousMap.WeaklyPointed x y)

example : ZerothHomotopy (LoopSpace X x) →
    ZerothHomotopy (LoopSpace Y y) :=
  f.loopComponentsMap

example (gamma : LoopSpace X x) :
    f.loopComponentsMap (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk (f.loopMap gamma) :=
  ContinuousMap.WeaklyPointed.loopComponentsMap_mk f gamma

example (gamma : LoopSpace X x) :
    f.loopComponentsMap (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk
        (f.rootPath.symm.trans
          ((gamma.map f.hom.continuous).trans f.rootPath)) := by
  rw [ContinuousMap.WeaklyPointed.loopComponentsMap_mk,
    ContinuousMap.WeaklyPointed.loopMap_apply]

end ComponentFormulas

section MixedUniverseComposition

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}
variable (f : ContinuousMap.WeaklyPointed x y)
  (g : ContinuousMap.WeaklyPointed y z)

example : (f.comp g).loopComponentsMap =
    g.loopComponentsMap ∘ f.loopComponentsMap :=
  ContinuousMap.WeaklyPointed.loopComponentsMap_comp f g

example (q : ZerothHomotopy (LoopSpace X x)) :
    (f.comp g).loopComponentsMap q =
      g.loopComponentsMap (f.loopComponentsMap q) := by
  rw [ContinuousMap.WeaklyPointed.loopComponentsMap_comp]
  rfl

end MixedUniverseComposition

section WeakEquivalenceConsequences

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}
variable (f : ContinuousMap.WeaklyPointed x y)
  (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap))

example : f.loopComponentsMap =
    TopCat.zerothHomotopyMap (TopCat.ofHom f.loopMap) :=
  ContinuousMap.WeaklyPointed.loopComponentsMap_eq_zerothHomotopyMap f

example : Function.Bijective f.loopComponentsMap :=
  loopComponentsMap_bijective_of_loopMap_weakEquivalence f hf

example : Function.Bijective
    (_root_.basedFundamentalGroupMap f.hom f.rootPath) :=
  basedFundamentalGroupMap_bijective_of_loopMap_weakEquivalence f hf

example : FundamentalGroup X x ≃* FundamentalGroup Y y :=
  fundamentalGroupMulEquivOfLoopMapWeakEquivalence f hf

example (q : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfLoopMapWeakEquivalence f hf q =
      _root_.basedFundamentalGroupMap f.hom f.rootPath q :=
  rfl

example (gamma : LoopSpace X x) :
    fundamentalGroupMulEquivOfLoopMapWeakEquivalence f hf
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (f.rootPath.symm.trans
          ((gamma.map f.hom.continuous).trans f.rootPath))) := by
  exact _root_.basedFundamentalGroupMap_mk f.hom f.rootPath gamma

end WeakEquivalenceConsequences

section TypeZero

variable {X₀ Y₀ : Type 0} [TopologicalSpace X₀] [TopologicalSpace Y₀]
  {x₀ : X₀} {y₀ : Y₀}
variable (f₀ : ContinuousMap.WeaklyPointed x₀ y₀)
  (hf₀ : TopCat.weakHomotopyEquivalences (TopCat.ofHom f₀.loopMap))

example : FundamentalGroup X₀ x₀ ≃* FundamentalGroup Y₀ y₀ :=
  fundamentalGroupMulEquivOfLoopMapWeakEquivalence f₀ hf₀

end TypeZero

section TypeOne

variable {X₁ Y₁ : Type 1} [TopologicalSpace X₁] [TopologicalSpace Y₁]
  {x₁ : X₁} {y₁ : Y₁}
variable (f₁ : ContinuousMap.WeaklyPointed x₁ y₁)
  (hf₁ : TopCat.weakHomotopyEquivalences (TopCat.ofHom f₁.loopMap))

example : Function.Bijective f₁.loopComponentsMap :=
  loopComponentsMap_bijective_of_loopMap_weakEquivalence f₁ hf₁

end TypeOne

section Nonclaims

variable {X : Type u} [TopologicalSpace X] {x : X}

#guard_msgs (error, substring := true) in
#synth Group (ZerothHomotopy (LoopSpace X x))

#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.loopMapHomotopyEquivOfWeakEquivalence

#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.pointedEquivOfLoopMapWeakEquivalence

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenQStageFundamentalMulEquiv

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.NQKSpacePiZeroEquivK0

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenQSContinuousMap

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridToStageSpectrumMap

end Nonclaims

#print axioms ContinuousMap.WeaklyPointed.loopComponentsMap
#print axioms ContinuousMap.WeaklyPointed.loopComponentsMap_mk
#print axioms ContinuousMap.WeaklyPointed.loopComponentsMap_comp
#print axioms
  ContinuousMap.WeaklyPointed.loopComponentsMap_eq_zerothHomotopyMap
#print axioms
  loopComponentsMap_bijective_of_loopMap_weakEquivalence
#print axioms
  basedFundamentalGroupMap_bijective_of_loopMap_weakEquivalence
#print axioms
  fundamentalGroupMulEquivOfLoopMapWeakEquivalence

end WeaklyPointedLoopComponentsWeakHomotopyTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
