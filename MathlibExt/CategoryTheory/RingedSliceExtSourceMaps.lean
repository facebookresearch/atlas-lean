/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.RingedSliceExtModules

/-!
# Source maps of the fixed local Ext module

The maps precompose actual derived Ext classes by the original source
sheaf map. Their linearity follows from associativity with target
multiplication. Restrictions use the native exact slice inverse image.
This construction applies to either crystalline basis and other actual
ringed sites, without choosing a coefficient-module map independently.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.RingedSliceExtSourceMaps

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite
open RingedSliceExtModules

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)
  (O : Sheaf J CommRingCat.{1}) {F G : Sheaf J AddCommGrpCat.{1}} (f : F ⟶ G)

/-- Restrict the actual source sheaf map to this slice. -/
def localSource (P : C) : F.over P ⟶ G.over P :=
  (J.overPullback AddCommGrpCat.{1} P).map f

/-- Source precomposition is linear for the original target-multiplication action. -/
def localExtMap (P : C) (n : ℕ) :
    LocalExt J O G P n →ₗ[O.obj.obj (op P)] LocalExt J O F P n := by
  letI := localExtModule J O F P n
  letI := localExtModule J O G P n
  exact {
    toFun := (Ext.mk₀ (localSource J f P)).precomp
      ((SheafLocalExtScalars.additiveRingSheaf J O).over P) (Nat.zero_add n)
    map_add' := ((Ext.mk₀ (localSource J f P)).precomp
      ((SheafLocalExtScalars.additiveRingSheaf J O).over P) (Nat.zero_add n)).map_add
    map_smul' := by
      intro r e
      change (Ext.mk₀ (localSource J f P)).comp
        (e.comp (Ext.mk₀ (SheafLocalExtScalars.scalarMap J O P r))
          (Nat.add_zero n)) (Nat.zero_add n) =
        ((Ext.mk₀ (localSource J f P)).comp e (Nat.zero_add n)).comp
          (Ext.mk₀ (SheafLocalExtScalars.scalarMap J O P r)) (Nat.add_zero n)
      exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (Nat.zero_add n)).symm }

/-- Source restriction is the same literal restriction of the sheaf map. -/
theorem localSource_restriction {P Q : C} (u : P ⟶ Q) :
    (slicePullback J u).map (localSource J f Q) = localSource J f P := rfl

/-- Native Ext restriction commutes with the original source precomposition. -/
theorem localExtMap_restriction {P Q : C} (u : P ⟶ Q) (n : ℕ)
    (e : LocalExt J O G Q n) :
    restriction J O F u n (localExtMap J O f Q n e) =
      localExtMap J O f P n (restriction J O G u n e) := by
  change ((Ext.mk₀ (localSource J f Q)).comp e (Nat.zero_add n)).mapExactFunctor
      (slicePullback J u) =
    (Ext.mk₀ (localSource J f P)).comp
      (e.mapExactFunctor (slicePullback J u)) (Nat.zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, localSource_restriction]
  rfl

/-- The whole module-presheaf map retains every local class and restriction. -/
def sourcePresheafMap (n : ℕ) : localExtModulePresheaf J O G n ⟶
    localExtModulePresheaf J O F n where
  app P := by
    letI := localExtModule J O F P.unop n
    letI := localExtModule J O G P.unop n
    exact ModuleCat.ofHom (localExtMap J O f P.unop n)
  naturality {P Q} u := by
    letI := localExtModule J O F P.unop n
    letI := localExtModule J O G P.unop n
    letI := localExtModule J O F Q.unop n
    letI := localExtModule J O G Q.unop n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro e
    change localExtMap J O f Q.unop n (restriction J O G u.unop n e) =
      restriction J O F u.unop n (localExtMap J O f P.unop n e)
    exact (localExtMap_restriction J O f u.unop n e).symm

end MathlibExt.CategoryTheory.RingedSliceExtSourceMaps
