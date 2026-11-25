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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageProduct

/-!
# Finite-stage product functor consumer tests

Smallest consumer checks for the finite-stage projection and pairing functors:
projected stage objects compute to the component, paired stage objects compute
to the paired components, and paired diagonals stay zero at low degree.
Uses the explicitly scoped product structure `prodWaldhausen`; proves no
equivalence, weak-stage comparison, simplicial, realization, additivity, or
K/G-theory claim.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u
universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageProductTests

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [HasZeroObject C] [HasZeroObject D]
  [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] (n : ℕ)

local instance prodWaldhausenIndependent
    {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {D : Type u₂} [Category.{v₂} D] [Limits.HasZeroObject D] [WaldhausenCategoryWithoutGluing D] :
    WaldhausenCategoryWithoutGluing (C × D) := prodWaldhausen

/-- Projected stage object to `C` computes to the first component. -/
example (X : Stage (C × D) n) (a : Ar n) :
    ((stageProjectFst C D n).obj X).obj.obj a = (X.obj.obj a).1 :=
  stageProjectFst_obj_obj C D n X a

/-- Paired stage object computes to the paired components. -/
example (p : Stage C n × Stage D n) (a : Ar n) :
    ((stagePair C D n).obj p).obj.obj a = (p.1.obj.obj a, p.2.obj.obj a) :=
  stagePair_obj_obj C D n p a

/-- Paired stage diagonal is zero at low degree. -/
example (p : Stage C n × Stage D n) (i : Fin (n + 1)) :
    IsZero (((stagePair C D n).obj p).obj.obj (diag i)) :=
  ((stagePair C D n).obj p).property.diag_isZero i

/-- Projected stage object to `D` computes to the second component,
with independent universes. -/
example (C : Type u₁) [Category.{v₁} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    (D : Type u₂) [Category.{v₂} D] [Limits.HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    (n : ℕ) (X : Stage (C × D) n) (a : Ar n) :
    ((stageProjectSnd C D n).obj X).obj.obj a = (X.obj.obj a).2 :=
    stageProjectSnd_obj_obj C D n X a

/-- Projected stage map to `C` computes to the first component. -/
example (X Y : Stage (C × D) n) (f : X ⟶ Y) (a : Ar n) :
    ((stageProjectFst C D n).map f).hom.app a = (f.hom.app a).1 :=
  stageProjectFst_map_app C D n f a

/-- Projected stage map to `D` computes to the second component. -/
example (X Y : Stage (C × D) n) (f : X ⟶ Y) (a : Ar n) :
    ((stageProjectSnd C D n).map f).hom.app a = (f.hom.app a).2 :=
  stageProjectSnd_map_app C D n f a

/-- Paired stage map first component computes componentwise. -/
example (p q : Stage C n × Stage D n) (f : p ⟶ q) (a : Ar n) :
    (((stagePair C D n).map f).hom.app a).1 = f.1.hom.app a :=
  stagePair_map_app_fst C D n f a

/-- Paired stage map second component computes componentwise. -/
example (p q : Stage C n × Stage D n) (f : p ⟶ q) (a : Ar n) :
    (((stagePair C D n).map f).hom.app a).2 = f.2.hom.app a :=
  stagePair_map_app_snd C D n f a

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageProductTests
