/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSConstantEvaluation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial
open SimplicialPresheaf

namespace MathlibExtTest.ConstantEvaluation

namespace GeneralSite

variable {D : Type w} [Category.{v} D] {z : D} (hz : IsTerminal z)

-- The ordinary adjunction does not require object or Hom smallness.
example : SimplicialPresheaf.ConstantEvaluation.constant (D := D) ⊣
    SimplicialPresheaf.ConstantEvaluation.evaluation z :=
  SimplicialPresheaf.ConstantEvaluation.adjunction hz

variable [Small.{u} D] [LocallySmall.{u} D]

example (K : SSet.{u}) (X : SimplicialPresheaf.{u} D) :
    (SimplicialPresheaf.ConstantEvaluation.iso hz K X).hom =
      innerHomπ (SimplicialPresheaf.ConstantEvaluation.constant.obj K) X (op z) :=
  rfl

example {K L : SSet.{u}} (k : K ⟶ L) (X : SimplicialPresheaf.{u} D) :
    innerHomPre (SimplicialPresheaf.ConstantEvaluation.constant.map k) X ≫
        (SimplicialPresheaf.ConstantEvaluation.iso hz K X).hom =
      (SimplicialPresheaf.ConstantEvaluation.iso hz L X).hom ≫
        (pre k).app (X.obj (op z)) :=
  SimplicialPresheaf.ConstantEvaluation.iso_source hz k X

example (K : SSet.{u}) {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    innerHomPost (SimplicialPresheaf.ConstantEvaluation.constant.obj K) f ≫
        (SimplicialPresheaf.ConstantEvaluation.iso hz K Y).hom =
      (SimplicialPresheaf.ConstantEvaluation.iso hz K X).hom ≫
        (ihom K).map (f.app (op z)) :=
  SimplicialPresheaf.ConstantEvaluation.iso_target hz K f

end GeneralSite

-- A site can have both declared universes above the scalar smallness bound.
example {D : Type (u + 3)} [Category.{u + 2} D] [Small.{u} D] [LocallySmall.{u} D]
    {z : D} (hz : IsTerminal z) (K : SSet.{u}) (X : SimplicialPresheaf.{u} D) :
    innerHom (SimplicialPresheaf.ConstantEvaluation.constant.obj K) X ≅
      (ihom K).obj (X.obj (op z)) :=
  SimplicialPresheaf.ConstantEvaluation.iso hz K X

namespace OrderedSite

open SimplicialPresheaf.OrderedJFS.ConstantEvaluation

local instance sourceLocallySmall (n : ℕ) : LocallySmall.{u} (FinitePowerSite.Source n) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

example (n : ℕ) (K : SSet.{u}) (X : SimplicialPresheaf.{u} (FinitePowerSite.Source n))
    (a : (FinitePowerSite.Source n)ᵒᵖ) :
    (iso n K X).inv ≫ innerHomπ ((constant n).obj K) X a =
      (ihom K).map (X.map (toZero a.unop).op) :=
  iso_inv_projection n K X a

example (K L : SSet.{u}) :
    (zeroIso K L).hom =
      innerHomπ ((constant 0).obj K) ((constant 0).obj L) (op (zeroTuple 0)) :=
  rfl

example (K L : SSet.{u}) (a : (FinitePowerSite.Source 0)ᵒᵖ) :
    (zeroIso K L).inv ≫ innerHomπ ((constant 0).obj K) ((constant 0).obj L) a =
      𝟙 ((ihom K).obj L) :=
  zeroIso_inv_projection K L a

-- These calls keep two and zero outer coordinates as actual original sites.
example (K : SSet.{u}) (X : SimplicialPresheaf.{u} (FinitePowerSite.Source 2)) :
    (iso 2 K X).hom = innerHomπ ((constant 2).obj K) X (op (zeroTuple 2)) :=
  rfl

end OrderedSite

namespace NonconstantRepresentable

local instance : LocallySmall.{u} SimplexCategory :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

abbrev K : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} PUnit)

abbrev X : SimplicialPresheaf.{u} SimplexCategory :=
  discreteYoneda.obj ⦋1⦌

-- At outer zero this representable has two labels; at outer one it has
-- three. Extending label one must give the constant-one operator, not the
-- identity operator on [1].
def labelOne : K ⟶ X.obj (op ⦋0⦌) where
  app n := ↾fun _ => (discreteYonedaObjEquiv ⦋1⦌ (op ⦋0⦌) n).symm
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
  naturality _ _ _ := by rfl

abbrev hz : IsTerminal (⦋0⦌ : SimplexCategory) :=
  SimplexCategory.isTerminalZero

abbrev h : 𝟙_ SSet.{u} ⟶ (ihom K).obj (X.obj (op ⦋0⦌)) :=
  curry ((ρ_ K).hom ≫ labelOne)

theorem inverse_uncurry_at_one :
    uncurry (h ≫ (SimplicialPresheaf.ConstantEvaluation.iso hz K X).inv ≫
      innerHomπ (SimplicialPresheaf.ConstantEvaluation.constant.obj K) X (op ⦋1⦌)) =
      (ρ_ K).hom ≫ labelOne ≫ X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op := by
  have he : hz.from ⦋1⦌ = SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 :=
    SimplexCategory.eq_const_to_zero _
  rw [SimplicialPresheaf.ConstantEvaluation.iso_inv_projection, he]
  rw [← curry_natural_right, uncurry_curry]
  exact Category.assoc _ _ _

example :
    discreteYonedaObjEquiv ⦋1⦌ (op ⦋1⦌) (op ⦋0⦌)
      ((uncurry (h ≫ (SimplicialPresheaf.ConstantEvaluation.iso hz K X).inv ≫
        innerHomπ (SimplicialPresheaf.ConstantEvaluation.constant.obj K) X (op ⦋1⦌))).app
        (op ⦋0⦌) (⟨PUnit.unit⟩, PUnit.unit)) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 := by
  rw [inverse_uncurry_at_one]
  change discreteYonedaObjEquiv ⦋1⦌ (op ⦋1⦌) (op ⦋0⦌)
    (((X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op).app (op ⦋0⦌))
      ((labelOne.app (op ⦋0⦌)) ⟨PUnit.unit⟩)) = _
  rw [discreteYoneda_obj_map]
  dsimp only [labelOne]
  rw [ConcreteCategory.hom_ofHom]
  change SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ≫
      discreteYonedaObjEquiv ⦋1⦌ (op ⦋0⦌) (op ⦋0⦌)
        ((discreteYonedaObjEquiv ⦋1⦌ (op ⦋0⦌) (op ⦋0⦌)).symm
          (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) = _
  rw [Equiv.apply_symm_apply]
  rfl

end NonconstantRepresentable

end MathlibExtTest.ConstantEvaluation
