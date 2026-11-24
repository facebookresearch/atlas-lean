/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Monoidal
public import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import MathlibExt.CategoryTheory.Monoidal.ObjectProperty.Lift

/-!
# Base change for `FGProjectiveCat`

Extension of scalars preserves finite projective modules.
The lifted functor `FGProjectiveCat.baseChange` is additive, exact from the split
source, and strong monoidal for commutative rings.
-/

@[expose] public section

open CategoryTheory

universe v uR uS

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S)

/-- Extension of scalars preserves `isFGProjective`. -/
lemma ModuleCat.isFGProjective_extendScalars {M : ModuleCat.{v} R}
    (hM : ModuleCat.isFGProjective R M) :
    ModuleCat.isFGProjective.{max uS v} S ((ModuleCat.extendScalars f).obj M) := by
  obtain ⟨hFin, hProj⟩ := hM
  let _alg : Algebra R S := f.toAlgebra
  have _tower : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' rfl
  have _fin : Module.Finite R M := hFin
  have _proj : Module.Projective R M := hProj
  change ModuleCat.isFGProjective S (ModuleCat.ExtendScalars.obj' f M)
  constructor
  · have : Module.Finite S (TensorProduct R S M) :=
      Module.Finite.base_change (R := R) (A := S) (M := M)
    change Module.Finite S (ModuleCat.ExtendScalars.obj' f M)
    exact this
  · have : Module.Projective S (TensorProduct R S M) :=
      Module.Projective.tensorProduct (R := S) (R₀ := R) (M := S) (N := M)
    change Module.Projective S (ModuleCat.ExtendScalars.obj' f M)
    exact this

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Extension of scalars lifted to `FGProjectiveCat`. -/
noncomputable def baseChange (f : R →+* S) :
    FGProjectiveCat.{v} R ⥤ FGProjectiveCat.{max uS v} S :=
  (ModuleCat.isFGProjective.{max uS v} (R := S)).lift
    (toModuleCat (R := R) ⋙ ModuleCat.extendScalars f)
    (fun X => ModuleCat.isFGProjective_extendScalars f X.property)

@[simp]
lemma baseChange_obj_obj (f : R →+* S) (X : FGProjectiveCat.{v} R) :
    ((baseChange f).obj X).obj = (ModuleCat.extendScalars f).obj X.obj :=
  rfl

@[simp]
lemma baseChange_map_hom (f : R →+* S) {X Y : FGProjectiveCat.{v} R} (g : X ⟶ Y) :
    ((baseChange f).map g).hom = (ModuleCat.extendScalars f).map g.hom :=
  rfl

instance (f : R →+* S) : (baseChange (R := R) (S := S) f).Additive := by
  dsimp [baseChange]
  infer_instance

instance (f : R →+* S) : (baseChange (R := R) (S := S) f).IsExact :=
  ExactCategory.isExact_splitSource _

end FGProjectiveCat

section Monoidal

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

namespace FGProjectiveCat

/-- Base change is strong monoidal in the same-universe case `u`. -/
noncomputable instance :
    (baseChange (R := R) (S := S) f :
      FGProjectiveCat.{u} R ⥤ FGProjectiveCat.{u} S).Monoidal := by
  dsimp only [baseChange]
  have : (ModuleCat.isFGProjective (R := S)).IsMonoidal :=
    ModuleCat.isFGProjective_isMonoidal S
  have : (toModuleCat (R := R)).Monoidal := by
    dsimp only [FGProjectiveCat.toModuleCat]
    infer_instance
  have : (ModuleCat.extendScalars f).Monoidal := inferInstance
  have : (toModuleCat (R := R) ⋙ ModuleCat.extendScalars f).Monoidal := inferInstance
  infer_instance

end FGProjectiveCat

end Monoidal
