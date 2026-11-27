/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialHomCongrFullMaps

/-!
# Genuine original full enriched object transport through supplied unit isomorphisms

The original source functor and all its full Hom maps are retained.
Each supplied actual unit-category isomorphism gives the canonical
complete enriched Hom isomorphism. Composing those SAME maps transports
only the original target objects. The full original identity and every
composition map are preserved at independent source, target and scalar
universes; no functor or weak-outcome certificate is an input.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [EnrichedCategory SSet.{u} D]
  (F : EnrichedFunctor SSet.{u} C D) (b : C → D)
  (e : ∀ x, ForgetEnrichment.of SSet.{u} (F.obj x) ≅ ForgetEnrichment.of SSet.{u} (b x))

/-- Retain the SAME whole original Hom map followed by the canonical supplied full
target-object isomorphisms. -/
def transportedHom (x y : C) : (x ⟶[SSet.{u}] y) ⟶ (b x ⟶[SSet.{u}] b y) :=
  F.map x y ≫ (Iso.eHomCongr SSet.{u} (e x) (e y)).hom

/-- The SAME actual original source identity is mapped to the supplied original target identity. -/
theorem transportedHom_identity (x : C) : eId SSet.{u} x ≫ transportedHom F b e x x =
  eId SSet.{u} (b x) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ (Iso.eHomCongr SSet.{u} (e x) (e x)).hom) (F.map_id x)).trans
      (homCongr_identity D (e x)))

/-- Every complete original composable Hom pair keeps the SAME full enriched composition
equation. -/
theorem transportedHom_composition (x y z : C) :
    eComp SSet.{u} x y z ≫ transportedHom F b e x z =
      (transportedHom F b e x y ⊗ₘ transportedHom F b e y z) ≫
        eComp SSet.{u} (b x) (b y) (b z) := by
  let Txy : (F.obj x ⟶[SSet.{u}] F.obj y) ⟶ (b x ⟶[SSet.{u}] b y) :=
    (Iso.eHomCongr SSet.{u} (e x) (e y)).hom
  let Tyz : (F.obj y ⟶[SSet.{u}] F.obj z) ⟶ (b y ⟶[SSet.{u}] b z) :=
    (Iso.eHomCongr SSet.{u} (e y) (e z)).hom
  let Txz : (F.obj x ⟶[SSet.{u}] F.obj z) ⟶ (b x ⟶[SSet.{u}] b z) :=
    (Iso.eHomCongr SSet.{u} (e x) (e z)).hom
  have hT : eComp SSet.{u} (F.obj x) (F.obj y) (F.obj z) ≫ Txz =
      (Txy ⊗ₘ Tyz) ≫ eComp SSet.{u} (b x) (b y) (b z) :=
    homCongr_composition D (e x) (e y) (e z)
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  have hF := congrArg (fun h : ((x ⟶[SSet.{u}] y) ⊗ (y ⟶[SSet.{u}] z)) ⟶
      (F.obj x ⟶[SSet.{u}] F.obj z) => h.app q p) (F.map_comp x y z)
  have hC := congrArg (fun h : ((F.obj x ⟶[SSet.{u}] F.obj y) ⊗
      (F.obj y ⟶[SSet.{u}] F.obj z)) ⟶ (b x ⟶[SSet.{u}] b z) =>
    h.app q ((F.map x y).app q p.1, (F.map y z).app q p.2)) hT
  exact (congrArg (fun h => Txz.app q h) hF).trans hC

/-- The SAME supplied original functor transported through those actual target-object unit
isomorphisms. -/
def transportObjects : EnrichedFunctor SSet.{u} C D where
  obj := b
  map := transportedHom F b e
  map_id := transportedHom_identity F b e
  map_comp := transportedHom_composition F b e

/-- The actual whole transported Hom map retains the SAME original map and both canonical
target isomorphisms. -/
theorem transportObjects_hom (x y : C) :
    (transportObjects F b e).map x y = F.map x y ≫ (Iso.eHomCongr SSet.{u} (e x) (e y)).hom := rfl

/-- Every original scalar coefficient retains its complete canonical original
object-conjugation formula. -/
theorem transportObjects_scalar (q : SimplexCategoryᵒᵖ) (x y : C) (h : (x ⟶[SSet.{u}] y).obj q) :
    ((transportObjects F b e).map x y).app q h =
      (unitScalarFunctor D q).map (e x).inv ≫ (F.map x y).app q h ≫
        (unitScalarFunctor D q).map (e y).hom :=
  homCongr_scalar D q (e x) (e y) ((F.map x y).app q h)

end SSet
