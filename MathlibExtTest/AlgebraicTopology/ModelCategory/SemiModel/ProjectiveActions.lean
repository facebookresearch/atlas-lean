/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.ProjectiveActions
import all MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.ProjectiveActions
import Batteries.Tactic.Lint

/-!
# Full variable projective subgroup restriction contracts

The original action maps, actual initial map, both projective lifting
classes, and the injective-map coinduction retract are exercised directly.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uH uG
open CategoryTheory Limits HomotopicalAlgebra
open HomotopicalAlgebra.SemiModel.ProjectiveActions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Group H] {G : Type uG} [Group G]
  [HasProductsOfShape G C] [HasProductsOfShape (H × G) C]
  (φ : H →* G) (hφ : Function.Injective φ)

example {X Y : Action C G} (i : X ⟶ Y) (hi : projectiveCofibrations C G i) :
    projectiveCofibrations C H ((Action.res C φ).map i) :=
  restriction_projectiveCofibration φ hφ i hi

example {X Y : Action C G} (i : X ⟶ Y) (hi : projectiveTrivialCofibrations C G i) :
    projectiveTrivialCofibrations C H ((Action.res C φ).map i) :=
  restriction_projectiveTrivialCofibration φ hφ i hi

example (X : Action C G) (hX : projectiveCofibrantObject C G X) :
    projectiveCofibrantObject C H ((Action.res C φ).obj X) :=
  restriction_projectiveCofibrantObject φ hφ X hX

example {X Y : Action C H} (p : X ⟶ Y) (hp : fibrations C p.hom) :
    fibrations C ((coinduction φ).map p).hom :=
  coinductionMap_fibration φ hφ p hp

example {X Y : Action C H} (p : X ⟶ Y) (hp : trivialFibrations C p.hom) :
    trivialFibrations C ((coinduction φ).map p).hom :=
  coinductionMap_trivialFibration φ hφ p hp

example {X Y : Action C H} (p : X ⟶ Y) :
    RetractArrow (coinductionMap φ p) (coinductionProductMap (G := G) p) :=
  coinductionArrowRetract φ hφ p

example (A : Action C G) (X : Action C H) :
    ((Action.res C φ).obj A ⟶ X) ≃ (A ⟶ (coinduction φ).obj X) :=
  (restrictionCoinductionAdjunction φ).homEquiv A X

example {X Y : Action C H} (p : X ⟶ Y) :
    coinductionSplit φ hφ X ≫ coinductionMap φ p =
      coinductionProductMap (G := G) p ≫ coinductionSplit φ hφ Y :=
  coinductionSplit_naturality φ hφ p

#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.restrictionCoinductionAdjunction
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.coinductionArrowRetract
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.coinductionMap_fibration
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.coinductionMap_trivialFibration
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.restriction_projectiveCofibration
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.restriction_projectiveTrivialCofibration
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.restriction_projectiveCofibrantObject
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.projectiveCofibrations_eq
#print axioms HomotopicalAlgebra.SemiModel.ProjectiveActions.projectiveTrivialCofibrations_eq

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.ProjectiveActions
#lint+ in MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.ProjectiveActions
