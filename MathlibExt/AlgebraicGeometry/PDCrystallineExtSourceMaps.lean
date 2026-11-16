/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDCrystallineExtSheafification

/-!
# Source maps of the actual crystalline Ext module

Precompose each native slice Ext class by the original sheaf map.
It is linear for the original target-multiplication action, and its
restriction naturality is the native exact functor action on Ext.
Sheafification then produces the actual coefficient-module map.
This is the covariant map after the original Cartier-dual group map.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDCrystallineExtSourceMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.AlgebraicGeometry Opposite
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves
open PDCrystallineLocalExtModules PDCrystallineExtSheafification

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)
  {F G : CoefficientSheaves p A S} (f : F ⟶ G)

/-- The original source sheaf map, restricted to this actual PD slice. -/
def localSource (P : Obj p A S) : F.over P ⟶ G.over P :=
  ((topology p A S).overPullback AddCommGrpCat.{1} P).map f

/-- The fixed coefficient module acts by original target multiplication, so source
precomposition is linear. -/
def localExtMap (P : Obj p A S) (n : ℕ) :
    LocalExt p A S G P n →ₗ[(structureRingSheaf p A S).obj.obj (op P)] LocalExt p A S F P n := by
  letI := localExtModule p A S F P n
  letI := localExtModule p A S G P n
  exact {
    toFun := (Ext.mk₀ (localSource p A S f P)).precomp ((structureSheaf p A S).over P)
      (Nat.zero_add n)
    map_add' := ((Ext.mk₀ (localSource p A S f P)).precomp
      ((structureSheaf p A S).over P) (Nat.zero_add n)).map_add
    map_smul' := by
      intro r e
      change (Ext.mk₀ (localSource p A S f P)).comp
        (e.comp (Ext.mk₀ (MathlibExt.CategoryTheory.SheafLocalExtScalars.scalarMap
          (topology p A S) (structureRingSheaf p A S) P r)) (Nat.add_zero n))
        (Nat.zero_add n) =
      ((Ext.mk₀ (localSource p A S f P)).comp e (Nat.zero_add n)).comp
        (Ext.mk₀ (MathlibExt.CategoryTheory.SheafLocalExtScalars.scalarMap
          (topology p A S) (structureRingSheaf p A S) P r)) (Nat.add_zero n)
      exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (Nat.zero_add n)).symm }

/-- Restriction of the original source map uses the same literal sheaf restriction. -/
theorem localSource_restriction {P Q : Obj p A S} (u : P ⟶ Q) :
    (slicePullback p A S u).map (localSource p A S f Q) = localSource p A S f P := rfl

/-- Native Ext pullback commutes with precomposition by the original restricted source map. -/
theorem localExtMap_restriction {P Q : Obj p A S} (u : P ⟶ Q) (n : ℕ)
    (e : LocalExt p A S G Q n) :
    restriction p A S F u n (localExtMap p A S f Q n e) =
      localExtMap p A S f P n (restriction p A S G u n e) := by
  change ((Ext.mk₀ (localSource p A S f Q)).comp e (Nat.zero_add n)).mapExactFunctor
      (slicePullback p A S u) =
    (Ext.mk₀ (localSource p A S f P)).comp
      (e.mapExactFunctor (slicePullback p A S u)) (Nat.zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, localSource_restriction]
  rfl

/-- The complete module-presheaf map fixes every local class and original restriction. -/
def sourcePresheafMap (n : ℕ) : localExtModulePresheaf p A S G n ⟶
    localExtModulePresheaf p A S F n where
  app P := by
    letI := localExtModule p A S F P.unop n
    letI := localExtModule p A S G P.unop n
    exact ModuleCat.ofHom (localExtMap p A S f P.unop n)
  naturality {P Q} u := by
    letI := localExtModule p A S F P.unop n
    letI := localExtModule p A S G P.unop n
    letI := localExtModule p A S F Q.unop n
    letI := localExtModule p A S G Q.unop n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro e
    change localExtMap p A S f Q.unop n (restriction p A S G u.unop n e) =
      restriction p A S F u.unop n (localExtMap p A S f P.unop n e)
    exact (localExtMap_restriction p A S f u.unop n e).symm

/-- Actual module-sheafification of this fixed source coefficient map. -/
def sourceSheafMap (n : ℕ) : moduleSheaf p A S G n ⟶ moduleSheaf p A S F n :=
  (PresheafOfModules.sheafification (𝟙 (coefficientRing p A S).obj)).map
    (sourcePresheafMap p A S f n)

end MathlibExt.AlgebraicGeometry.PDCrystallineExtSourceMaps
