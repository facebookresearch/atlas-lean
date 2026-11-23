/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageTranspose
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Batteries.Tactic.Lint

noncomputable section
set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial ZeroObject

universe u v uA vA uB vB

namespace CategoryTheory.Waldhausen.SConstruction.IteratedStageTransposeTests

private theorem functor_map_heq
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {F G : A ⥤ B} (h : F = G) {X Y : A} (f : X ⟶ Y) :
    HEq (F.map f) (G.map f) := by
  cases h
  rfl

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

local instance (n : ℕ) : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
local instance (n : ℕ) : WaldhausenCategory (Stage C n) := generalStageWaldhausenCategory C n
local instance (ns : List ℕ) (n : ℕ) : HasZeroObject (Stage (IteratedStage C ns) n) :=
  generalStageHasZeroObject (IteratedStage C ns) n
local instance (ns : List ℕ) (n : ℕ) : WaldhausenCategory (Stage (IteratedStage C ns) n) :=
  generalStageWaldhausenCategory (IteratedStage C ns) n

-- Zero arrows are the canonical arrows induced by the original chosen zero objects.
local instance (ns : List ℕ) (n : ℕ) : HasZeroMorphisms (IteratedStage (Stage C n) ns) :=
  HasZeroObject.zeroMorphismsOfZeroObject
local instance (ns : List ℕ) (n : ℕ) : HasZeroMorphisms (Stage (IteratedStage C ns) n) :=
  HasZeroObject.zeroMorphismsOfZeroObject

-- The object and Hom worlds remain independent throughout the public interface.
example (ns : List ℕ) (n : ℕ) :
    IteratedStage (Stage C n) ns ≌ Stage (IteratedStage C ns) n :=
  iteratedStageTransposeEquivalence C ns n

-- Both degeneracies retain their original carriers and named Stage structures.
example (n : ℕ) :
    (iteratedStageTransposeEquivalence C [] n).functor =
      (iteratedStageNilEquivalence (Stage C n)).functor ⋙
        (iteratedStageNilEquivalence_exact C).2.mapStage n :=
  iteratedStageTransposeEquivalence_nil_functor C n

example (ns : List ℕ) :
    IteratedStage (Stage C 0) ns ≌ Stage (IteratedStage C ns) 0 :=
  iteratedStageTransposeEquivalence C ns 0

example : IteratedStage (Stage C 0) [] ≌ Stage (IteratedStage C []) 0 :=
  iteratedStageTransposeEquivalence C [] 0

-- These use arbitrary original objects and arrows rather than a replacement carrier.
example (ns : List ℕ) (n : ℕ) (x : Ar n) (X : IteratedStage (Stage C n) ns) :
    ((iteratedStageTransposeEquivalence C ns n).functor.obj X).obj.obj x =
      (mapIteratedStage (evalIsGeneralStageWaldhausenExact C n x) ns).obj X :=
  congrArg (fun F => F.obj X) (iteratedStageTransposeEquivalence_eval C ns n x)

example (ns : List ℕ) (n : ℕ) (x : Ar n)
    {X Y : IteratedStage (Stage C n) ns} (f : X ⟶ Y) :
    HEq (((iteratedStageTransposeEquivalence C ns n).functor.map f).hom.app x)
      ((mapIteratedStage (evalIsGeneralStageWaldhausenExact C n x) ns).map f) :=
  functor_map_heq (iteratedStageTransposeEquivalence_eval C ns n x) f

example {a b : SimplexCategory} (α : a ⟶ b) (ns : List ℕ) :
    mapIteratedStage (reindexStage_general_isWaldhausenExact C α) ns ⋙
        (iteratedStageTransposeEquivalence C ns a.len).functor =
      (iteratedStageTransposeEquivalence C ns b.len).functor ⋙
        reindexStage (C := IteratedStage C ns) α :=
  iteratedStageTransposeEquivalence_reindex C α ns

example {a b : SimplexCategory} (α : a ⟶ b) (ns : List ℕ)
    (X : IteratedStage (Stage C b.len) ns) :
    (iteratedStageTransposeEquivalence C ns a.len).functor.obj
        ((mapIteratedStage (reindexStage_general_isWaldhausenExact C α) ns).obj X) =
      (reindexStage (C := IteratedStage C ns) α).obj
        ((iteratedStageTransposeEquivalence C ns b.len).functor.obj X) :=
  congrArg (fun F => F.obj X) (iteratedStageTransposeEquivalence_reindex C α ns)

example {a b : SimplexCategory} (α : a ⟶ b) (ns : List ℕ)
    {X Y : IteratedStage (Stage C b.len) ns} (f : X ⟶ Y) :
    HEq ((iteratedStageTransposeEquivalence C ns a.len).functor.map
        ((mapIteratedStage (reindexStage_general_isWaldhausenExact C α) ns).map f))
      ((reindexStage (C := IteratedStage C ns) α).map
        ((iteratedStageTransposeEquivalence C ns b.len).functor.map f)) :=
  functor_map_heq (iteratedStageTransposeEquivalence_reindex C α ns) f

example {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) (n : ℕ) :
    reindexIteratedStage (Stage C n) α ⋙
        (iteratedStageTransposeEquivalence C (stageTupleDegrees b) n).functor =
      (iteratedStageTransposeEquivalence C (stageTupleDegrees a) n).functor ⋙
        (reindexIteratedStage_isWaldhausenExact C α).mapStage n :=
  iteratedStageTransposeEquivalence_reindexTuple C α n

example {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) (n : ℕ)
    (X : StageAtTuple (Stage C n) a) :
    (iteratedStageTransposeEquivalence C (stageTupleDegrees b) n).functor.obj
        ((reindexIteratedStage (Stage C n) α).obj X) =
      ((reindexIteratedStage_isWaldhausenExact C α).mapStage n).obj
        ((iteratedStageTransposeEquivalence C (stageTupleDegrees a) n).functor.obj X) :=
  congrArg (fun F => F.obj X) (iteratedStageTransposeEquivalence_reindexTuple C α n)

example {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) (n : ℕ)
    {X Y : StageAtTuple (Stage C n) a} (f : X ⟶ Y) :
    HEq ((iteratedStageTransposeEquivalence C (stageTupleDegrees b) n).functor.map
        ((reindexIteratedStage (Stage C n) α).map f))
      (((reindexIteratedStage_isWaldhausenExact C α).mapStage n).map
        ((iteratedStageTransposeEquivalence C (stageTupleDegrees a) n).functor.map f)) :=
  functor_map_heq (iteratedStageTransposeEquivalence_reindexTuple C α n) f

-- The quotient is the original zeroth-face functor, including its original arrows.
example (ns : List ℕ) (n : ℕ) :
    (iteratedStageTransposeEquivalence C ns (n + 1)).functor ⋙
        StageFirstQuotient.quotient (IteratedStage C ns) n =
      mapIteratedStage (StageFirstQuotient.quotient_isWaldhausenExact C n) ns ⋙
        (iteratedStageTransposeEquivalence C ns n).functor :=
  iteratedStageTransposeEquivalence_quotient C ns n

example (ns : List ℕ) (n : ℕ) (X : IteratedStage (Stage C (n + 1)) ns) :
    (StageFirstQuotient.quotient (IteratedStage C ns) n).obj
        ((iteratedStageTransposeEquivalence C ns (n + 1)).functor.obj X) =
      (iteratedStageTransposeEquivalence C ns n).functor.obj
        ((mapIteratedStage (StageFirstQuotient.quotient_isWaldhausenExact C n) ns).obj X) :=
  congrArg (fun F => F.obj X) (iteratedStageTransposeEquivalence_quotient C ns n)

example (ns : List ℕ) (n : ℕ)
    {X Y : IteratedStage (Stage C (n + 1)) ns} (f : X ⟶ Y) :
    HEq ((StageFirstQuotient.quotient (IteratedStage C ns) n).map
        ((iteratedStageTransposeEquivalence C ns (n + 1)).functor.map f))
      ((iteratedStageTransposeEquivalence C ns n).functor.map
        ((mapIteratedStage (StageFirstQuotient.quotient_isWaldhausenExact C n) ns).map f)) :=
  functor_map_heq (iteratedStageTransposeEquivalence_quotient C ns n) f

example :
    (iteratedStageTransposeEquivalence C [] 1).functor ⋙
        StageFirstQuotient.quotient (IteratedStage C []) 0 =
      mapIteratedStage (StageFirstQuotient.quotient_isWaldhausenExact C 0) [] ⋙
        (iteratedStageTransposeEquivalence C [] 0).functor :=
  iteratedStageTransposeEquivalence_quotient C [] 0

-- Exactness is earned for both actual directions and their selected zero objects.
example (ns : List ℕ) (n : ℕ) :
    IsZero ((iteratedStageTransposeEquivalence C ns n).functor.obj
      (0 : IteratedStage (Stage C n) ns)) :=
  (iteratedStageTransposeEquivalence_exact C ns n).1.map_isZero (isZero_zero _)

example (ns : List ℕ) (n : ℕ) :
    IsZero ((iteratedStageTransposeEquivalence C ns n).inverse.obj
      (0 : Stage (IteratedStage C ns) n)) :=
  (iteratedStageTransposeEquivalence_exact C ns n).2.map_isZero (isZero_zero _)

example (ns : List ℕ) (n : ℕ) (X Y : IteratedStage (Stage C n) ns) :
    (iteratedStageTransposeEquivalence C ns n).functor.map (0 : X ⟶ Y) = 0 :=
  Functor.map_zero _ X Y

example (ns : List ℕ) (n : ℕ) (X Y : Stage (IteratedStage C ns) n) :
    (iteratedStageTransposeEquivalence C ns n).inverse.map (0 : X ⟶ Y) = 0 :=
  Functor.map_zero _ X Y

example (ns : List ℕ) (n : ℕ) {X Y : IteratedStage (Stage C n) ns}
    (f : X ⟶ Y) (hf : IsCofibration f) :
    IsCofibration ((iteratedStageTransposeEquivalence C ns n).functor.map f) :=
  (iteratedStageTransposeEquivalence_exact C ns n).1.map_cofibration f hf

example (ns : List ℕ) (n : ℕ) {X Y : Stage (IteratedStage C ns) n}
    (f : X ⟶ Y) (hf : IsCofibration f) :
    IsCofibration ((iteratedStageTransposeEquivalence C ns n).inverse.map f) :=
  (iteratedStageTransposeEquivalence_exact C ns n).2.map_cofibration f hf

example (ns : List ℕ) (n : ℕ) {X Y : IteratedStage (Stage C n) ns}
    (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    IsWeakEquivalence ((iteratedStageTransposeEquivalence C ns n).functor.map f) :=
  (iteratedStageTransposeEquivalence_exact C ns n).1.map_weakEquivalence f hf

example (ns : List ℕ) (n : ℕ) {X Y : Stage (IteratedStage C ns) n}
    (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    IsWeakEquivalence ((iteratedStageTransposeEquivalence C ns n).inverse.map f) :=
  (iteratedStageTransposeEquivalence_exact C ns n).2.map_weakEquivalence f hf

#print axioms iteratedStageTransposeEquivalence
#print axioms iteratedStageTransposeEquivalence_exact
#print axioms iteratedStageTransposeEquivalence_nil_functor
#print axioms iteratedStageTransposeEquivalence_cons_functor
#print axioms iteratedStageTransposeEquivalence_eval
#print axioms iteratedStageTransposeEquivalence_reindex
#print axioms iteratedStageTransposeEquivalence_quotient
#print axioms iteratedStageTransposeEquivalence_reindexTuple

#lint only unusedArguments in
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageTranspose

end CategoryTheory.Waldhausen.SConstruction.IteratedStageTransposeTests
