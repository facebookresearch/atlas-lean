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

public import MathlibExt.CategoryTheory.Limits.DiscreteSourceMapping

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.OriginalDiscreteSourceMapping

namespace DiscreteSourceMappingNeutralPublicUse
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : Type w} (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w} F]
  {X Y : J → C} (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
  [HasProduct (fun j => F.obj (Opposite.op (X j)))]
  [HasProduct (fun j => F.obj (Opposite.op (Y j)))]

/-- Arbitrary source and target categories keep the actual caller cofan. -/
example : IsLimit (fan F c) := fanIsLimit F c hc

/-- Both inverse directions retain the original, unmodified source injection. -/
example (j : J) :
    (productIso F c hc).hom ≫ Pi.π (fun j => F.obj (Opposite.op (X j))) j =
      F.map (c.inj j).op := productIso_hom_projection F c hc j

example (j : J) :
    (productIso F c hc).inv ≫ F.map (c.inj j).op =
      Pi.π (fun j => F.obj (Opposite.op (X j))) j := productIso_inv_projection F c hc j

/-- The original family map and caller coproduct map commute in the full comparison. -/
example (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) :
    F.map p.op ≫ (productIso F c hc).hom =
      (productIso F d hd).hom ≫ Limits.Pi.map (fun j => F.map (f j).op) :=
  productIso_naturality F c hc d hd f p hp
end DiscreteSourceMappingNeutralPublicUse
