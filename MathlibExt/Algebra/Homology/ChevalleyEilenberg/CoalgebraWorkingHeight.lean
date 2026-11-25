/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraULift

/-!
# Chevalley–Eilenberg coalgebra maps at a common universe height

Carrier lifts and the exterior chain comparison bundle a Lie algebra map
as a coalgebra map at any height containing the ring and both Lie carriers.
An additional independent height supports simultaneous matrix-size and
coefficient diagrams. The scalar tensor unit is lifted to the same height.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChevalleyEilenberg.LieLift

universe u v w x z

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {L' : Type w} [LieRing L'] [LieAlgebra R L']

local instance : HasFiniteBiproducts (ModuleCat.{max u z} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u z} R)
/-- The canonical closed tensor structure at the chosen common carrier height. -/
local instance workingHeightClosed :
    letI : MonoidalCategoryStruct (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u,z} (R := R)
    MonoidalClosed (ModuleCat.{max u z} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u,z} (R := R)
  exact ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,z} (R := R)

/-- The existing CE comparisons and native Lie map, placed at the full common height. -/
def nativeLiftedComplexMapAtHeight (f : L →ₗ⁅R⁆ L') :
    canonicalComplexULift.{u,v,max u v w z} R L ⟶
      canonicalComplexULift.{u,w,max u v w z} R L' :=
  (complexLiftComparisonIso.{u,v,max u v w z} R L).inv ≫
    nativeComplexMap R (ULift.{max u v w z} L) (LieLift.map.{u,v,w,max u v w z} f) ≫
      (complexLiftComparisonIso.{u,w,max u v w z} R L').hom

/-- The map keeps exactly the original exterior-map value under the native lift. -/
theorem nativeLiftedComplexMapAtHeight_f_up (f : L →ₗ⁅R⁆ L') (n : ℕ) (a : ⋀[R]^n L) :
    ((nativeLiftedComplexMapAtHeight.{u,v,w,z} R L f).f n).hom (ULift.up a) =
      ULift.up (exteriorPower.map n f.toLinearMap a) := by
  change exteriorULiftEquiv.{u,w,max u v w z} R L' n
      (exteriorPower.map n (LieLift.map.{u,v,w,max u v w z} f).toLinearMap
        ((exteriorULiftEquiv.{u,v,max u v w z} R L n).symm (ULift.up a))) = _
  rw [exteriorULiftEquiv_apply, exteriorULiftEquiv_symm_apply,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have h : ((LieLift.downEquiv.{u,w,max u v w z} R L').toLinearMap.comp
      (LieLift.map.{u,v,w,max u v w z} f).toLinearMap).comp
      (LieLift.downEquiv.{u,v,max u v w z} R L).symm.toLinearMap = f.toLinearMap := by
    ext y
    rfl
  rw [h]

/-- The general working-height adapter extends the existing independent-universe map exactly. -/
theorem nativeLiftedComplexMapAtHeight_zero (f : L →ₗ⁅R⁆ L') :
    nativeLiftedComplexMapAtHeight.{u,v,w,0} R L f = nativeLiftedComplexMap R L f := rfl

/-- The full-height map preserves the transported coaugmentation. -/
theorem nativeLiftedComplexMapAtHeight_coaug (f : L →ₗ⁅R⁆ L') :
    liftedComplexCoaug.{u,v,max u v w z} R L ≫
        nativeLiftedComplexMapAtHeight.{u,v,w,z} R L f =
      liftedComplexCoaug.{u,w,max u v w z} R L' := by
  unfold liftedComplexCoaug nativeLiftedComplexMapAtHeight
  rw [Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc (nativeComplexCoaug R (ULift.{max u v w z} L)),
    nativeComplexMap_coaug]

/-- The full-height map is a native comonoid homomorphism. -/
def nativeLiftedComplexMapAtHeightIsComonHom (f : L →ₗ⁅R⁆ L') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max u v w z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max u v w z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v w z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,max u v w z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v w z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u,max u v w z} (R := R)
    letI : ComonObj (canonicalComplexULift.{u,v,max u v w z} R L) :=
      liftedComonObj.{u,v,max u v w z} R L
    letI : ComonObj (canonicalComplexULift.{u,w,max u v w z} R L') :=
      liftedComonObj.{u,w,max u v w z} R L'
    IsComonHom (nativeLiftedComplexMapAtHeight.{u,v,w,z} R L f) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max u v w z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max u v w z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v w z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,max u v w z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v w z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u,max u v w z} (R := R)
  letI : ComonObj (canonicalChainData R (ULift.{max u v w z} L)).complex :=
    nativeComonObj R (ULift.{max u v w z} L)
  letI : ComonObj (canonicalChainData R (ULift.{max u v w z} L')).complex :=
    nativeComonObj R (ULift.{max u v w z} L')
  letI : ComonObj (canonicalComplexULift.{u,v,max u v w z} R L) :=
    liftedComonObj.{u,v,max u v w z} R L
  letI : ComonObj (canonicalComplexULift.{u,w,max u v w z} R L') :=
    liftedComonObj.{u,w,max u v w z} R L'
  letI : IsComonHom (complexLiftComparisonIso.{u,v,max u v w z} R L).hom :=
    ComonObj.isComonHom_ofIso _
  letI : IsComonHom (complexLiftComparisonIso.{u,w,max u v w z} R L').hom :=
    ComonObj.isComonHom_ofIso _
  letI : IsComonHom (nativeComplexMap R (ULift.{max u v w z} L)
      (LieLift.map.{u,v,w,max u v w z} f)) := nativeComplexMapIsComonHom _ _ _
  unfold nativeLiftedComplexMapAtHeight
  infer_instance

/-- The full-height identity map is the native chain identity. -/
theorem nativeLiftedComplexMapAtHeight_id :
    nativeLiftedComplexMapAtHeight.{u,v,v,z} R L (LieHom.id : L →ₗ⁅R⁆ L) =
      𝟙 (canonicalComplexULift.{u,v,max u v z} R L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  cases a with
  | up a =>
      change ((nativeLiftedComplexMapAtHeight.{u,v,v,z} R L LieHom.id).f n).hom
        (ULift.up a) = ULift.up a
      exact (nativeLiftedComplexMapAtHeight_f_up.{u,v,v,z} R L LieHom.id n a).trans
        (congrArg ULift.up (LinearMap.congr_fun (exteriorPower.map_id (R := R) (M := L) (n := n)) a))

/-- Three original worlds use one common-height composite, with the original exterior maps. -/
theorem nativeLiftedComplexMapAtHeight_comp
    {L'' : Type x} [LieRing L''] [LieAlgebra R L'']
    (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    nativeLiftedComplexMapAtHeight.{u,v,w,max u v w x z} R L f ≫
        nativeLiftedComplexMapAtHeight.{u,w,x,max u v w x z} R L' g =
      nativeLiftedComplexMapAtHeight.{u,v,x,max u v w x z} R L (g.comp f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  cases a with
  | up a =>
      change ((nativeLiftedComplexMapAtHeight.{u,w,x,max u v w x z} R L' g).f n).hom
          (((nativeLiftedComplexMapAtHeight.{u,v,w,max u v w x z} R L f).f n).hom (ULift.up a)) =
        ((nativeLiftedComplexMapAtHeight.{u,v,x,max u v w x z} R L (g.comp f)).f n).hom (ULift.up a)
      have hf := nativeLiftedComplexMapAtHeight_f_up.{u,v,w,max u v w x z} R L f n a
      have hg := nativeLiftedComplexMapAtHeight_f_up.{u,w,x,max u v w x z} R L' g n
        (exteriorPower.map n f.toLinearMap a)
      have hc := nativeLiftedComplexMapAtHeight_f_up.{u,v,x,max u v w x z} R L (g.comp f) n a
      have hm := congrArg ULift.up
        (LinearMap.congr_fun (exteriorPower.map_comp f.toLinearMap g.toLinearMap) a).symm
      exact (congrArg (((nativeLiftedComplexMapAtHeight.{u,w,x,max u v w x z} R L' g).f n).hom)
        hf).trans (hg.trans (hm.trans hc.symm))

end ChevalleyEilenberg
