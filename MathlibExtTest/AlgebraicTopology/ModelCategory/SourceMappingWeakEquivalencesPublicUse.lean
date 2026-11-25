/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.SourceMappingWeakEquivalences

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SourceMappingWeakEquivalencesNeutralPublicUse
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {J : Type w} [HasProductsOfShape J D] (F : Cᵒᵖ ⥤ D)
  [PreservesLimitsOfSize.{w, w} F]

/-- The original caller cofans and their actual source map need no spectrum structure. -/
example {X Y : J → C}
    [∀ j, IsFibrant (F.obj (Opposite.op (X j)))]
    [∀ j, IsFibrant (F.obj (Opposite.op (Y j)))]
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j)
    (hf : ∀ j, WeakEquivalence (F.map (f j).op)) : WeakEquivalence (F.map p.op) :=
  OriginalCoproductSourceMapping.originalCallerMap_weak F c hc d hd f p hp hf

/-- Any actual colimiting cofan retains the same cofibrant point and its original legs. -/
example {X : J → D} (c : Cofan X) (hc : IsColimit c) [∀ j, IsCofibrant (X j)] :
    IsCofibrant c.pt := originalCofanPoint_cofibrant c hc
end SourceMappingWeakEquivalencesNeutralPublicUse
