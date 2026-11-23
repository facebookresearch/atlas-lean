/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import MathlibExt.CategoryTheory.SheafLocalExtScalars
public import MathlibExt.CategoryTheory.ExtTargetScalarModules
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Actual local Ext modules on a ringed slice site

Local Ext uses the original abelian sheaves restricted to each slice.
The coefficient action is original target multiplication. All restriction,
unit and composition maps use native slice inverse image and Ext maps.
This generic construction is reused on both full and nilpotent PD bases.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.RingedSliceExtModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.Opposite
open MathlibExt.CategoryTheory.SheafLocalExtScalars
open MathlibExt.CategoryTheory.ExtTargetScalarModules

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)
  (O : Sheaf J CommRingCat.{1})

/-- The original slice coefficient category at a genuine nilpotent PD test. -/
abbrev SliceSheaves (P : C) := Sheaf ((J).over P) AddCommGrpCat.{1}

/-- Mathlib's sheafification instance on a small site, restated at universe `1` for this file
only: synthesising it on the small model inside `Sheaf.isGrothendieckAbelian_of_essentiallySmall`
otherwise leaves the small model's universe as a stuck metavariable. -/
local instance abelianSheafifySmall {B : Type 1} [SmallCategory B]
    (K : GrothendieckTopology B) : HasSheafify K AddCommGrpCat.{1} := by
  infer_instance

instance sliceGrothendieck (P : C) :
    IsGrothendieckAbelian.{1} (SliceSheaves J P) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{1, 1, 0, 2, 1}
    ((J).over P) AddCommGrpCat.{1}

/-- The actual slice inverse image; every coefficient and object map is restriction. -/
abbrev slicePullback {P Q : C} (f : P ⟶ Q) :
    SliceSheaves J Q ⥤ SliceSheaves J P :=
  (J).overMapPullback AddCommGrpCat.{1} f

instance slicePullback_additive {P Q : C} (f : P ⟶ Q) :
    (slicePullback J f).Additive where
  map_add := by
    intro X Y a b
    apply Sheaf.hom_ext
    ext U x
    rfl

instance slicePullback_limits {P Q : C} (f : P ⟶ Q) :
    PreservesFiniteLimits (slicePullback J f) := by
  infer_instance

instance slicePullback_colimits {P Q : C} (f : P ⟶ Q) :
    PreservesFiniteColimits (slicePullback J f) := by
  letI : (slicePullback J f).IsLeftAdjoint :=
    (Functor.sheafAdjunctionCocontinuous (Over.map f) AddCommGrpCat.{1}
      ((J).over P) ((J).over Q)).isLeftAdjoint
  infer_instance

variable (F : Sheaf J AddCommGrpCat.{1})

/-- Actual local degree-n Ext of the original group and additive structure sheaves. -/
abbrev LocalExt (P : C) (n : ℕ) :=
  Ext.{1} (F.over P) ((SheafLocalExtScalars.additiveRingSheaf J O).over P) n

/-- The local coefficient module is fixed by original target multiplication. -/
instance localExtModule (P : C) (n : ℕ) :
    Module ((O).obj.obj (op P)) (LocalExt J O F P n) :=
  targetModule ((O).obj.obj (op P))
    (scalarEndRingHom (J) (O) P) n

/-- Original coefficient action as an explicit native Ext composition. -/
theorem local_smul (P : C) (n : ℕ)
    (r : (O).obj.obj (op P)) (e : LocalExt J O F P n) :
    r • e = e.comp (Ext.mk₀ (scalarEnd (J)
      (O) P r).asHom) (Nat.add_zero n) := rfl

/-- Slice restriction acts through the original exact functor on actual derived Ext. -/
def restriction {P Q : C} (f : P ⟶ Q) (n : ℕ) :
    LocalExt J O F Q n →+ LocalExt J O F P n :=
  (slicePullback J f).mapExtAddHom (F.over Q)
    ((SheafLocalExtScalars.additiveRingSheaf J O).over Q) n

/-- The actual Ext restriction is semilinear for the original ring restriction. -/
theorem restriction_smul {P Q : C} (f : P ⟶ Q) (n : ℕ)
    (r : (O).obj.obj (op Q)) (e : LocalExt J O F Q n) :
    restriction J O F f n (r • e) =
      ((O).obj.map f.op).hom r • restriction J O F f n e := by
  change (e.comp (Ext.mk₀ (scalarMap (J)
    (O) Q r)) (Nat.add_zero n)).mapExactFunctor
      (slicePullback J f) =
    (e.mapExactFunctor (slicePullback J f)).comp
      (Ext.mk₀ (scalarMap (J) (O) P
        (((O).obj.map f.op).hom r))) (Nat.add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [scalarMap_restrict]

/-- The native slice unit acts as the identity on sheaves pulled from the original PD site. -/
theorem slice_unit_on_source (P : C) (B : Sheaf J AddCommGrpCat.{1}) :
    ((J).overMapPullbackId AddCommGrpCat.{1} P).hom.app (B.over P) =
      𝟙 (B.over P) := by
  apply Sheaf.hom_ext
  ext U x
  change B.obj.obj (op U.unop.left) at x
  change (B.obj.map (𝟙 U.unop.left).op).hom x = x
  rw [op_id, _root_.CategoryTheory.Functor.map_id]
  rfl

/-- The native slice compositor has the same original coefficient normalization. -/
theorem slice_composition_on_source {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R)
    (B : Sheaf J AddCommGrpCat.{1}) :
    ((J).overMapPullbackComp AddCommGrpCat.{1} f g).hom.app (B.over R) =
      𝟙 (B.over P) := by
  apply Sheaf.hom_ext
  ext U x
  change B.obj.obj (op U.unop.left) at x
  change (B.obj.map (𝟙 U.unop.left).op).hom x = x
  rw [op_id, _root_.CategoryTheory.Functor.map_id]
  rfl

/-- The fixed native Ext restriction preserves the original identity. -/
theorem restriction_id (P : C) (n : ℕ) (e : LocalExt J O F P n) :
    restriction J O F (𝟙 P) n e = e := by
  change e.mapExactFunctor (slicePullback J (𝟙 P)) = e
  have h := Ext.mapExactFunctor_comp_mk₀_natTransApp.{1, 1, 1, 2, 1, 2} e
    (((J).overMapPullbackId AddCommGrpCat.{1} P).hom)
  rw [slice_unit_on_source, slice_unit_on_source] at h
  erw [Ext.comp_mk₀_id, Ext.mk₀_id_comp] at h
  simpa only [Ext.id_mapExactFunctor] using h

/-- Composition uses the actual native slice-pullback compositor. -/
theorem restriction_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R)
    (n : ℕ) (e : LocalExt J O F R n) :
    restriction J O F (f ≫ g) n e =
      restriction J O F f n (restriction J O F g n e) := by
  change e.mapExactFunctor (slicePullback J (f ≫ g)) =
    (e.mapExactFunctor (slicePullback J g)).mapExactFunctor (slicePullback J f)
  have h := Ext.mapExactFunctor_comp_mk₀_natTransApp.{1, 1, 1, 2, 1, 2} e
    (((J).overMapPullbackComp AddCommGrpCat.{1} f g).hom)
  rw [slice_composition_on_source, slice_composition_on_source] at h
  erw [Ext.comp_mk₀_id, Ext.mk₀_id_comp] at h
  exact h.symm.trans (Ext.comp_mapExactFunctor.{1, 1, 1} e
    (slicePullback J g) (slicePullback J f))

/-- Every original local Ext value and semilinear restriction is retained in this coefficient
presheaf. -/
def localExtModulePresheaf (n : ℕ) : PresheafOfModules.{1}
    ((O).obj ⋙ forget₂ CommRingCat.{1} RingCat.{1}) where
  obj P := by
    letI := localExtModule J O F P.unop n
    exact ModuleCat.of ((O).obj.obj P) (LocalExt J O F P.unop n)
  map {P Q} f := by
    letI := localExtModule J O F P.unop n
    letI := localExtModule J O F Q.unop n
    exact ModuleCat.ofHom
      (X := ModuleCat.of ((O).obj.obj P) (LocalExt J O F P.unop n))
      (Y := (ModuleCat.restrictScalars
        (((O).obj ⋙ forget₂ CommRingCat.{1} RingCat.{1}).map f).hom).obj
          (ModuleCat.of ((O).obj.obj Q) (LocalExt J O F Q.unop n))) {
      toFun := restriction J O F f.unop n
      map_add' := (restriction J O F f.unop n).map_add
      map_smul' := by
        intro r e
        exact restriction_smul J O F f.unop n r e }
  map_id P := by
    letI := localExtModule J O F P.unop n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro e
    exact restriction_id J O F P.unop n e
  map_comp {P Q R} f g := by
    letI := localExtModule J O F P.unop n
    letI := localExtModule J O F Q.unop n
    letI := localExtModule J O F R.unop n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro e
    exact restriction_comp J O F g.unop f.unop n e

end MathlibExt.CategoryTheory.RingedSliceExtModules
