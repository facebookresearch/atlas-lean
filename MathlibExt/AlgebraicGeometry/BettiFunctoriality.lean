/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BettiRealization
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

@[expose] public noncomputable section

/-!
# Canonical coefficient normalization for Betti inverse image

The constant-sheaf comparison is the uniqueness isomorphism between the
actual two left adjoints to global sections. It fixes the coefficient unit
and determines pullback on shifted derived endomorphisms. Exactness of the
inverse-image functor is the completed provider in `ConstructibleComplexes`.
Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, §2.3.
-/

namespace MathlibExt.AlgebraicGeometry.BettiFunctoriality

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

/-- Actual global sections, evaluated at the top open. -/
abbrev globalSections (Z : TopCat.{0}) : RationalSheaf Z ⥤ ModuleCat.{0} ℚ :=
  (sheafSections (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj
    (op (⊤ : Opens Z))

/-- The actual rational constant-sheaf functor. -/
abbrev constantFunctor (Z : TopCat.{0}) : ModuleCat.{0} ℚ ⥤ RationalSheaf Z :=
  constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)

/-- Canonical comparison fixed by the two global-section adjunctions. -/
def constantPullbackIso {Z W : TopCat.{0}} (f : Z ⟶ W) :
    constantFunctor W ⋙ pullback ℚ f ≅ constantFunctor Z := by
  let a := (constantSheafAdj (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)
    (isTerminalTop (α := Opens W))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
  let b := constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)
    (isTerminalTop (α := Opens Z))
  exact a.leftAdjointUniq b

/-- The induced coefficient-unit isomorphism in the actual derived category. -/
def unitInverseImageIso {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (derivedPullback ℚ f).obj (rationalUnit W) ≅ rationalUnit Z :=
  ((pullback ℚ f).mapDerivedCategorySingleFunctor 0).app
      (rationalConstantSheaf W) ≪≫
    (DerivedCategory.singleFunctor (RationalSheaf Z) 0).mapIso
      ((constantPullbackIso f).app (ModuleCat.of ℚ ℚ))

instance derivedPullbackCommShift {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (derivedPullback ℚ f).CommShift ℤ := by
  dsimp [derivedPullback]
  infer_instance

instance derivedPullbackAdditive {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (derivedPullback ℚ f).Additive := by
  dsimp [derivedPullback]
  infer_instance

/-- Pullback on actual rational Betti cohomology, with its fixed unit comparison. -/
def cohomologyPullback {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℤ) :
    BettiRealization.Cohomology W n →ₗ[ℚ] BettiRealization.Cohomology Z n where
  toFun a := (unitInverseImageIso f).inv ≫ (derivedPullback ℚ f).map a ≫
    ((derivedPullback ℚ f).commShiftIso n).hom.app (rationalUnit W) ≫
      (shiftFunctor (RationalDerived Z) n).map (unitInverseImageIso f).hom
  map_add' a b := by
    simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r a := by
    simp [Functor.map_smul, Linear.comp_smul, Linear.smul_comp]

/-- The canonical coefficient map into direct image, fixed by the
constant-sheaf/global-section adjunction. -/
def unitPushforward {Z W : TopCat.{0}} (f : Z ⟶ W) :
    rationalConstantSheaf W ⟶ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).obj
      (rationalConstantSheaf Z) :=
  ((constantSheafAdj (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)
    (isTerminalTop (α := Opens W))).homEquiv (ModuleCat.of ℚ ℚ) _).symm
      ((constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)
        (isTerminalTop (α := Opens Z))).unit.app (ModuleCat.of ℚ ℚ))

end MathlibExt.AlgebraicGeometry.BettiFunctoriality
