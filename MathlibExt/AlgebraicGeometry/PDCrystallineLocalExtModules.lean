/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves
public import MathlibExt.CategoryTheory.SheafLocalExtScalars
public import MathlibExt.CategoryTheory.ExtTargetScalarModules
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Original PD-slice Ext modules and their coefficient maps

The value at a PD test is the native degree-one Ext group on its actual
slice site. Coefficients act by the original local structure-sheaf
multiplication endomorphism. Restrictions use the native exact slice
pullback and its action on Ext, rather than an independent Ext map.

For covariance the source coefficient sheaf is the actual Cartier dual
p-divisible group. Sheafification and comparison with the global internal
Ext are separate source operations, with this scalar action already fixed.

References: Berthelot--Breen--Messing, Theorie de Dieudonne cristalline II;
Scholze--Weinstein, arXiv:1211.6357v2, Sections3.2 and4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDCrystallineLocalExtModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.AlgebraicGeometry Opposite
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves
open MathlibExt.CategoryTheory.SheafLocalExtScalars
open MathlibExt.CategoryTheory.ExtTargetScalarModules

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

/-- The original slice coefficient category at a genuine nilpotent PD test. -/
abbrev SliceSheaves (P : Obj p A S) := Sheaf ((topology p A S).over P) AddCommGrpCat.{1}

instance sliceGrothendieck (P : Obj p A S) :
    IsGrothendieckAbelian.{1} (SliceSheaves p A S P) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{1, 1, 0, 2, 1}
    ((topology p A S).over P) AddCommGrpCat.{1}

/-- The actual slice inverse image; every coefficient and object map is restriction. -/
abbrev slicePullback {P Q : Obj p A S} (f : P ⟶ Q) :
    SliceSheaves p A S Q ⥤ SliceSheaves p A S P :=
  (topology p A S).overMapPullback AddCommGrpCat.{1} f

instance slicePullback_additive {P Q : Obj p A S} (f : P ⟶ Q) :
    (slicePullback p A S f).Additive where
  map_add := by
    intro X Y a b
    apply Sheaf.hom_ext
    ext U x
    rfl

instance slicePullback_limits {P Q : Obj p A S} (f : P ⟶ Q) :
    PreservesFiniteLimits (slicePullback p A S f) := by
  infer_instance

instance slicePullback_colimits {P Q : Obj p A S} (f : P ⟶ Q) :
    PreservesFiniteColimits (slicePullback p A S f) := by
  letI : (slicePullback p A S f).IsLeftAdjoint :=
    (Functor.sheafAdjunctionCocontinuous (Over.map f) AddCommGrpCat.{1}
      ((topology p A S).over P) ((topology p A S).over Q)).isLeftAdjoint
  infer_instance

variable (F : CoefficientSheaves p A S)

/-- Actual local degree-n Ext of the original group and additive structure sheaves. -/
abbrev LocalExt (P : Obj p A S) (n : ℕ) :=
  Ext.{1} (F.over P) ((structureSheaf p A S).over P) n

/-- The local coefficient module is fixed by original target multiplication. -/
instance localExtModule (P : Obj p A S) (n : ℕ) :
    Module ((structureRingSheaf p A S).obj.obj (op P)) (LocalExt p A S F P n) :=
  targetModule ((structureRingSheaf p A S).obj.obj (op P))
    (scalarEndRingHom (topology p A S) (structureRingSheaf p A S) P) n

omit [Fact p.Prime] in
/-- Original coefficient action as an explicit native Ext composition. -/
theorem local_smul (P : Obj p A S) (n : ℕ)
    (r : (structureRingSheaf p A S).obj.obj (op P)) (e : LocalExt p A S F P n) :
    r • e = e.comp (Ext.mk₀ (scalarEnd (topology p A S)
      (structureRingSheaf p A S) P r).asHom) (Nat.add_zero n) := rfl

/-- Slice restriction acts through the original exact functor on actual derived Ext. -/
def restriction {P Q : Obj p A S} (f : P ⟶ Q) (n : ℕ) :
    LocalExt p A S F Q n →+ LocalExt p A S F P n :=
  (slicePullback p A S f).mapExtAddHom (F.over Q) ((structureSheaf p A S).over Q) n

/-- The actual Ext restriction is semilinear for the original ring restriction. -/
theorem restriction_smul {P Q : Obj p A S} (f : P ⟶ Q) (n : ℕ)
    (r : (structureRingSheaf p A S).obj.obj (op Q)) (e : LocalExt p A S F Q n) :
    restriction p A S F f n (r • e) =
      ((structureRingSheaf p A S).obj.map f.op).hom r • restriction p A S F f n e := by
  change (e.comp (Ext.mk₀ (scalarMap (topology p A S)
    (structureRingSheaf p A S) Q r)) (Nat.add_zero n)).mapExactFunctor
      (slicePullback p A S f) =
    (e.mapExactFunctor (slicePullback p A S f)).comp
      (Ext.mk₀ (scalarMap (topology p A S) (structureRingSheaf p A S) P
        (((structureRingSheaf p A S).obj.map f.op).hom r))) (Nat.add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [scalarMap_restrict]

/-- The native slice unit acts as the identity on sheaves pulled from the original PD site. -/
theorem slice_unit_on_source (P : Obj p A S) (B : CoefficientSheaves p A S) :
    ((topology p A S).overMapPullbackId AddCommGrpCat.{1} P).hom.app (B.over P) =
      𝟙 (B.over P) := by
  apply Sheaf.hom_ext
  ext U x
  change B.obj.obj (op U.unop.left) at x
  change (B.obj.map (𝟙 U.unop.left).op).hom x = x
  rw [op_id, _root_.CategoryTheory.Functor.map_id]
  rfl

/-- The native slice compositor has the same original coefficient normalization. -/
theorem slice_composition_on_source {P Q R : Obj p A S} (f : P ⟶ Q) (g : Q ⟶ R)
    (B : CoefficientSheaves p A S) :
    ((topology p A S).overMapPullbackComp AddCommGrpCat.{1} f g).hom.app (B.over R) =
      𝟙 (B.over P) := by
  apply Sheaf.hom_ext
  ext U x
  change B.obj.obj (op U.unop.left) at x
  change (B.obj.map (𝟙 U.unop.left).op).hom x = x
  rw [op_id, _root_.CategoryTheory.Functor.map_id]
  rfl

/-- The fixed native Ext restriction preserves the original identity. -/
theorem restriction_id (P : Obj p A S) (n : ℕ) (e : LocalExt p A S F P n) :
    restriction p A S F (𝟙 P) n e = e := by
  change e.mapExactFunctor (slicePullback p A S (𝟙 P)) = e
  have h := Ext.mapExactFunctor_comp_mk₀_natTransApp.{1, 1, 1, 2, 1, 2} e
    (((topology p A S).overMapPullbackId AddCommGrpCat.{1} P).hom)
  rw [slice_unit_on_source, slice_unit_on_source] at h
  erw [Ext.comp_mk₀_id, Ext.mk₀_id_comp] at h
  simpa only [Ext.id_mapExactFunctor] using h

/-- Composition uses the actual native slice-pullback compositor. -/
theorem restriction_comp {P Q R : Obj p A S} (f : P ⟶ Q) (g : Q ⟶ R)
    (n : ℕ) (e : LocalExt p A S F R n) :
    restriction p A S F (f ≫ g) n e =
      restriction p A S F f n (restriction p A S F g n e) := by
  change e.mapExactFunctor (slicePullback p A S (f ≫ g)) =
    (e.mapExactFunctor (slicePullback p A S g)).mapExactFunctor (slicePullback p A S f)
  have h := Ext.mapExactFunctor_comp_mk₀_natTransApp.{1, 1, 1, 2, 1, 2} e
    (((topology p A S).overMapPullbackComp AddCommGrpCat.{1} f g).hom)
  rw [slice_composition_on_source, slice_composition_on_source] at h
  erw [Ext.comp_mk₀_id, Ext.mk₀_id_comp] at h
  exact h.symm.trans (Ext.comp_mapExactFunctor.{1, 1, 1} e
    (slicePullback p A S g) (slicePullback p A S f))

/-- Every original local Ext value and semilinear restriction is retained in this coefficient
presheaf. -/
def localExtModulePresheaf (n : ℕ) : PresheafOfModules.{1}
    ((structureRingSheaf p A S).obj ⋙ forget₂ CommRingCat.{1} RingCat.{1}) where
  obj P := by
    letI := localExtModule p A S F P.unop n
    exact ModuleCat.of ((structureRingSheaf p A S).obj.obj P) (LocalExt p A S F P.unop n)
  map {P Q} f := by
    letI := localExtModule p A S F P.unop n
    letI := localExtModule p A S F Q.unop n
    exact ModuleCat.ofHom
      (X := ModuleCat.of ((structureRingSheaf p A S).obj.obj P) (LocalExt p A S F P.unop n))
      (Y := (ModuleCat.restrictScalars
        (((structureRingSheaf p A S).obj ⋙ forget₂ CommRingCat.{1} RingCat.{1}).map f).hom).obj
          (ModuleCat.of ((structureRingSheaf p A S).obj.obj Q) (LocalExt p A S F Q.unop n))) {
      toFun := restriction p A S F f.unop n
      map_add' := (restriction p A S F f.unop n).map_add
      map_smul' := by
        intro r e
        exact restriction_smul p A S F f.unop n r e }
  map_id P := by
    letI := localExtModule p A S F P.unop n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro e
    exact restriction_id p A S F P.unop n e
  map_comp {P Q R} f g := by
    letI := localExtModule p A S F P.unop n
    letI := localExtModule p A S F Q.unop n
    letI := localExtModule p A S F R.unop n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro e
    exact restriction_comp p A S F g.unop f.unop n e

end MathlibExt.AlgebraicGeometry.PDCrystallineLocalExtModules
