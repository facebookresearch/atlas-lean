/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Actual finite Tate coefficients from roots of unity

The degree-one coefficient is the kernel of u ↦ u^(p^r) on the units of
the original ring presheaf, sheafified with its native Z/p^r module action.
Positive twists use actual tensor powers over Z/p^r. Negative twists use
the explicit enriched presheaf internal Hom into the sheaf of constant
coefficients, followed by tensor powers and sheafification. This internal
Hom records naturality on the whole slice category, not just Hom of the
global root groups. No primitive root is selected or called canonical.

Native finite-module construction: Mathlib/Algebra/Module/ZMod.lean at
56a005855ea17e0b0958f73ec801ae140b0a1679 (Lawrence Wu, Apache 2.0).
The tensor and enriched internal-Hom constructions are completed Mathlib.
References: BMS19 arXiv:1802.03261v2, Theorem 10.1 and Remark 10.3;
SGA4, Exposé IX, Section 3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteTateRootCoefficients

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.Enriched.FunctorCategory
open scoped TensorProduct MonoidalClosed

variable (p r : ℕ)

/-- Only the harmless ring-universe lift needed by native monoidal ModuleCat. -/
abbrev Coeff := ULift.{1} (ZMod (p ^ r))

def coefficientDown : Coeff p r →+* ZMod (p ^ r) where
  toFun x := x.down
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def roots (S : CommRingCat.{0}) : Subgroup Sˣ :=
  (powMonoidHom (p ^ r) : Sˣ →* Sˣ).ker

abbrev RootModule (S : CommRingCat.{0}) := ULift.{1} (Additive (roots p r S))

instance rootModuleStructure (S : CommRingCat.{0}) : Module (ZMod (p ^ r)) (RootModule p r S) :=
  AddCommGroup.zmodModule (fun x ↦ by
    apply ULift.ext
    apply Additive.ext
    apply Subtype.ext
    exact x.down.toMul.property)

instance rootCoeffModule (S : CommRingCat.{0}) : Module (Coeff p r) (RootModule p r S) :=
  Module.compHom _ (coefficientDown p r)

def rootsMap {S T : CommRingCat.{0}} (f : S →+* T) : roots p r S →* roots p r T where
  toFun x :=
    ⟨Units.map f.toMonoidHom x.val, by
      change (Units.map f.toMonoidHom x.val) ^ (p ^ r) = 1
      have hx : x.val ^ (p ^ r) = 1 := x.property
      rw [← map_pow, hx, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

def rootAdditiveMap {S T : CommRingCat.{0}} (f : S →+* T) :
    RootModule p r S →+ RootModule p r T where
  toFun x := ULift.up (Additive.ofMul (rootsMap p r f x.down.toMul))
  map_zero' := by
    apply ULift.ext
    apply Additive.ext
    change rootsMap p r f 1 = 1
    exact map_one _
  map_add' x y := by
    apply ULift.ext
    apply Additive.ext
    change rootsMap p r f (x.down.toMul * y.down.toMul) =
      rootsMap p r f x.down.toMul * rootsMap p r f y.down.toMul
    exact map_mul _ _ _

def rootLinearMap {S T : CommRingCat.{0}} (f : S →+* T) :
    RootModule p r S →ₗ[ZMod (p ^ r)] RootModule p r T :=
  (rootAdditiveMap p r f).toZModLinearMap (p ^ r)

def rootCoeffLinearMap {S T : CommRingCat.{0}} (f : S →+* T) :
    RootModule p r S →ₗ[Coeff p r] RootModule p r T where
  toFun := rootLinearMap p r f
  map_add' := map_add _
  map_smul' a x := (rootLinearMap p r f).map_smul a.down x

variable {C : Type 1} [Category.{0} C] (O : Cᵒᵖ ⥤ CommRingCat.{0})

def rootPresheaf : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r) where
  obj U := ModuleCat.of (Coeff p r) (RootModule p r (O.obj U))
  map f := ModuleCat.ofHom (rootCoeffLinearMap p r (O.map f).hom)
  map_id U := by
    apply ModuleCat.hom_ext
    ext x
    change (O.map (𝟙 U)).hom x.down.toMul.val.val = x.down.toMul.val.val
    have h := congrArg (fun f : O.obj U ⟶ O.obj U ↦ f.hom x.down.toMul.val.val) (O.map_id U)
    exact h
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    ext x
    change (O.map (f ≫ g)).hom x.down.toMul.val.val =
      (O.map g).hom ((O.map f).hom x.down.toMul.val.val)
    exact congrArg (fun f : O.obj U ⟶ O.obj W ↦ f.hom x.down.toMul.val.val) (O.map_comp f g)

variable (J : GrothendieckTopology C)

instance moduleSheafify : HasSheafify J (ModuleCat.{1} (Coeff p r)) := by
  let : HasLimits (ModuleCat.{1} (Coeff p r)) := ModuleCat.hasLimitsOfSize.{1, 1, 1, 1}
  let : PreservesColimitsOfSize.{1, 1}
      (forget₂ (ModuleCat.{1} (Coeff p r)) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 1, 1, 1} (Coeff p r)
  let : PreservesFilteredColimits (forget (ModuleCat.{1} (Coeff p r))) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (ModuleCat.{1} (Coeff p r)) AddCommGrpCat.{1}) (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1}
      (forget (ModuleCat.{1} (Coeff p r))) := inferInstance
  infer_instance

instance instHasFunctorEnrichedHom (M N : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)) :
    HasFunctorEnrichedHom (ModuleCat.{1} (Coeff p r)) M N := by
  infer_instance

abbrev Sheaves := Sheaf J (ModuleCat.{1} (Coeff p r))

def rootSheaf : Sheaves p r J :=
  (presheafToSheaf J _).obj (rootPresheaf p r O)

def constantUnit : Sheaves p r J :=
  (presheafToSheaf J (ModuleCat.{1} (Coeff p r))).obj
    (𝟙_ (Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)))

def tensorWord (M : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)) :
    ℕ → Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)
  | 0 => 𝟙_ _
  | n + 1 => M ⊗ tensorWord M n

def dualPresheaf : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r) :=
  functorEnrichedHom (ModuleCat.{1} (Coeff p r)) (rootSheaf p r O J).obj (constantUnit p r J).obj

def signedWord : ℤ → Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)
  | Int.ofNat n => tensorWord p r (rootSheaf p r O J).obj n
  | Int.negSucc n => tensorWord p r (dualPresheaf p r O J) (n + 1)

def finiteTate (i : ℤ) : Sheaves p r J :=
  (presheafToSheaf J _).obj (signedWord p r O J i)

abbrev integerModules : ModuleCat.{1} (Coeff p r) ⥤ ModuleCat.{1} ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom (Coeff p r))

instance integerModules_isRightAdjoint : (integerModules p r).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{1, 0, 1} (Int.castRingHom (Coeff p r))).isRightAdjoint

def integerTate (i : ℤ) : Sheaf J (ModuleCat.{1} ℤ) :=
  (sheafCompose J (integerModules p r)).obj (finiteTate p r O J i)

def rootOneUnit : rootPresheaf p r O ⟶ (finiteTate p r O J 1).obj :=
  toSheafify J (rootPresheaf p r O) ≫ (ρ_ (rootSheaf p r O J).obj).inv ≫
    toSheafify J (signedWord p r O J 1)

/-- The actual finite-level cyclotomic transition is u ↦ u^p. -/
def rootPowerMap (S : CommRingCat.{0}) : RootModule p (r + 1) S →+ RootModule p r S where
  toFun x := ULift.up (Additive.ofMul
    ⟨x.down.toMul.val ^ p, by
      change (x.down.toMul.val ^ p) ^ (p ^ r) = 1
      rw [← pow_mul]
      have hm : p * p ^ r = p ^ (r + 1) := by rw [pow_succ, mul_comm]
      rw [hm]
      exact x.down.toMul.property⟩)
  map_zero' := by
    apply ULift.ext
    apply Additive.ext
    apply Subtype.ext
    exact one_pow p
  map_add' x y := by
    apply ULift.ext
    apply Additive.ext
    apply Subtype.ext
    exact mul_pow x.down.toMul.val y.down.toMul.val p

set_option backward.isDefEq.respectTransparency false in
def rootPowerPresheafMap :
    rootPresheaf p (r + 1) O ⋙ integerModules p (r + 1) ⟶
      rootPresheaf p r O ⋙ integerModules p r where
  app U := ModuleCat.ofHom
    (X := (integerModules p (r + 1)).obj ((rootPresheaf p (r + 1) O).obj U))
    (Y := (integerModules p r).obj ((rootPresheaf p r O).obj U))
    { toFun := rootPowerMap p r (O.obj U)
      map_add' := map_add _
      map_smul' a x := by
        change rootPowerMap p r (O.obj U)
          ((a : Coeff p (r + 1)) • (x : RootModule p (r + 1) (O.obj U))) =
          (a : Coeff p r) • rootPowerMap p r (O.obj U) x
        exact map_intCast_smul (rootPowerMap p r (O.obj U)) (Coeff p (r + 1)) (Coeff p r) a
          (x : RootModule p (r + 1) (O.obj U)) }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    apply ULift.ext
    apply Additive.ext
    apply Subtype.ext
    apply Units.ext
    exact (map_pow (O.map f).hom x.down.toMul.val.val p).symm

end MathlibExt.AlgebraicGeometry.FiniteTateRootCoefficients
