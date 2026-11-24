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

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Discrete source coproducts retain all original mapping-product projections

The complete generic declarations are retained from the original native
Omega weak-class source. Original universes, chosen fans/cofans, maps,
hypotheses and proof bodies are unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w uC vC uD vD uV vV uI uT
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OriginalDiscreteSourceMapping

variable {D : Type uD} [Category.{vD} D] {J : Type w}

/-- Both complete original product maps are chosen only by the actual limiting fan. -/
def isoOfFan {X : J → D} (c : Fan X) (hc : IsLimit c) [HasProduct X] : c.pt ≅ ∏ᶜ X :=
  hc.conePointUniqueUpToIso (productIsProduct X)

/-- The full forward product map retains every original projection. -/
theorem isoOfFan_hom_projection {X : J → D} (c : Fan X) (hc : IsLimit c)
    [HasProduct X] (j : J) : (isoOfFan c hc).hom ≫ Pi.π X j = c.proj j :=
  IsLimit.conePointUniqueUpToIso_hom_comp hc (productIsProduct X) (Discrete.mk j)

/-- The full inverse product map retains every original projection. -/
theorem isoOfFan_inv_projection {X : J → D} (c : Fan X) (hc : IsLimit c)
    [HasProduct X] (j : J) : (isoOfFan c hc).inv ≫ c.proj j = Pi.π X j :=
  IsLimit.conePointUniqueUpToIso_inv_comp hc (productIsProduct X) (Discrete.mk j)

end CategoryTheory.OriginalDiscreteSourceMapping

namespace CategoryTheory.OriginalDiscreteSourceMapping

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : Type w} (F : Cᵒᵖ ⥤ D)

/-- Actual source mapping along the discrete opposite equivalence retains each original object. -/
def diagramIso (X : J → C) :
    (Discrete.opposite J).inverse ⋙ (Discrete.functor X).op ⋙ F ≅
      Discrete.functor (fun j => F.obj (Opposite.op (X j))) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro ⟨j⟩ ⟨k⟩ f
    obtain rfl := Discrete.eq_of_hom f
    have hf : f = 𝟙 (Discrete.mk j) := Subsingleton.elim _ _
    subst f
    simp only [Functor.map_id, Category.comp_id, Category.id_comp])

/-- The original caller cofan maps through its actual source limit and full diagram isomorphism. -/
def mappedCone {X : J → C} (c : Cofan X) :
    Cone (Discrete.functor (fun j => F.obj (Opposite.op (X j)))) :=
  (Cone.postcompose (diagramIso F X).hom).obj
    ((F.mapCone (Cocone.op c)).whisker (Discrete.opposite J).inverse)

/-- The complete original mapped cone is limiting by actual preservation and equivalence. -/
def mappedConeIsLimit [PreservesLimitsOfSize.{w, w} F]
    {X : J → C} (c : Cofan X) (hc : IsColimit c) : IsLimit (mappedCone F c) :=
  (IsLimit.postcomposeHomEquiv (diagramIso F X)
    ((F.mapCone (Cocone.op c)).whisker (Discrete.opposite J).inverse)).symm
      ((isLimitOfPreserves F hc.op).whiskerEquivalence (Discrete.opposite J).symm)

/-- Every original coproduct injection becomes the actual complete mapping projection. -/
theorem mappedCone_projection {X : J → C} (c : Cofan X) (j : J) :
    (mappedCone F c).π.app (Discrete.mk j) = F.map (c.inj j).op := by
  change F.map (c.inj j).op ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The actual original source mapping fan uses those same complete projection maps. -/
def fan {X : J → C} (c : Cofan X) : Fan (fun j => F.obj (Opposite.op (X j))) :=
  Fan.mk (F.obj (Opposite.op c.pt)) (fun j => F.map (c.inj j).op)

/-- Every original mapped cone projection agrees with the corresponding literal fan projection. -/
def fanIso {X : J → C} (c : Cofan X) : mappedCone F c ≅ fan F c :=
  Cone.ext (Iso.refl _) (fun j => by
    change (mappedCone F c).π.app j = 𝟙 (F.obj (Opposite.op c.pt)) ≫ F.map (c.inj j.as).op
    exact (mappedCone_projection F c j.as).trans (Category.id_comp _).symm)

/-- All caller source coproducts give genuine mapping products with every original map retained. -/
def fanIsLimit [PreservesLimitsOfSize.{w, w} F]
    {X : J → C} (c : Cofan X) (hc : IsColimit c) : IsLimit (fan F c) :=
  IsLimit.ofIsoLimit (mappedConeIsLimit F c hc) (fanIso F c)

end CategoryTheory.OriginalDiscreteSourceMapping

namespace CategoryTheory.OriginalDiscreteSourceMapping

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : Type w} (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w} F]

/-- The full original source mapping fan uses its actual product comparison. -/
def productIso {X : J → C} (c : Cofan X) (hc : IsColimit c)
    [HasProduct (fun j => F.obj (Opposite.op (X j)))] :
    F.obj (Opposite.op c.pt) ≅ ∏ᶜ (fun j => F.obj (Opposite.op (X j))) :=
  (fanIsLimit F c hc).conePointUniqueUpToIso (productIsProduct _)

/-- The forward original comparison retains every literal mapping projection. -/
theorem productIso_hom_projection {X : J → C} (c : Cofan X) (hc : IsColimit c)
    [HasProduct (fun j => F.obj (Opposite.op (X j)))] (j : J) :
    (productIso F c hc).hom ≫ Pi.π (fun j => F.obj (Opposite.op (X j))) j =
      F.map (c.inj j).op :=
  IsLimit.conePointUniqueUpToIso_hom_comp (fanIsLimit F c hc) (productIsProduct _) (Discrete.mk j)

/-- The inverse original comparison retains every literal mapping projection. -/
theorem productIso_inv_projection {X : J → C} (c : Cofan X) (hc : IsColimit c)
    [HasProduct (fun j => F.obj (Opposite.op (X j)))] (j : J) :
    (productIso F c hc).inv ≫ F.map (c.inj j).op = Pi.π (fun j => F.obj (Opposite.op (X j))) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp (fanIsLimit F c hc) (productIsProduct _) (Discrete.mk j)

/-- Every actual source family/caller coproduct map retains the whole product Iso square. -/
theorem productIso_naturality {X Y : J → C} (c : Cofan X) (hc : IsColimit c)
    (d : Cofan Y) (hd : IsColimit d)
    [HasProduct (fun j => F.obj (Opposite.op (X j)))]
    [HasProduct (fun j => F.obj (Opposite.op (Y j)))]
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) :
    F.map p.op ≫ (productIso F c hc).hom =
      (productIso F d hd).hom ≫ Limits.Pi.map (fun j => F.map (f j).op) := by
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, productIso_hom_projection, Category.assoc, Pi.map_π,
    ← Category.assoc, productIso_hom_projection]
  have h : p.op ≫ (c.inj j).op = (d.inj j).op ≫ (f j).op :=
    congrArg Quiver.Hom.op (hp j)
  exact (F.map_comp _ _).symm.trans ((F.congr_map h).trans (F.map_comp _ _))

end CategoryTheory.OriginalDiscreteSourceMapping
