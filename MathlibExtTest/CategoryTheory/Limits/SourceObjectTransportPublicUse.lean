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

public import MathlibExt.CategoryTheory.Limits.SourceObjectTransport

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.OriginalSourceObjectTransport

namespace SourceObjectTransportNeutralPublicUse
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : Type w} (F : Cᵒᵖ ⥤ D) (O : C → D)
  (hO : O = fun X => F.obj (Opposite.op X))

/-- Exact whole object-family transport retains the same original source map. -/
example {X Y : C} (f : X ⟶ Y) : HEq (pre F O hO f) (F.map f.op) :=
  pre_heq F O hO f

/-- The same actual fan, chosen colimit and endpoint function give all projections. -/
example [PreservesLimitsOfSize.{w, w} F] {X : J → C}
    (c : Cofan X) (hc : IsColimit c) [HasProduct (fun j => O (X j))] (j : J) :
    (productIso F O hO c hc).hom ≫ Pi.π (fun j => O (X j)) j =
      pre F O hO (c.inj j) := productIso_hom_projection F O hO c hc j

/-- A caller's exact dependent pre-map family receives the original whole equality. -/
example (P : ∀ {X Y : C}, (X ⟶ Y) → (O Y ⟶ O X))
    (hP : HEq (fun (X Y : C) (f : X ⟶ Y) => @P X Y f)
      (fun (X Y : C) (f : X ⟶ Y) => F.map f.op))
    {X Y : C} (f : X ⟶ Y) : pre F O hO f = P f := pre_eq F O hO P hP f

/-- A source-independent inverse leg follows from its actual forward leg. -/
example {X Y Z : C} (e : X ≅ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
    (h : e.hom ≫ p = q) : e.inv ≫ q = p := originalIso_inv_projection e p q h
end SourceObjectTransportNeutralPublicUse
