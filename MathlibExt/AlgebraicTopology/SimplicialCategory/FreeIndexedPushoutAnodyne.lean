/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeCoproducts
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiverPushoutAnodyne

/-!
# Entire indexed free-quiver attachments are Hom anodyne

The actual indexed free coproduct universal property compares every
supplied enriched coproduct cocone with the literal indexed generating
quiver. The original pushout square transports across those whole
isomorphisms. The proved word filtration then applies to the same old
pushout map on every original Hom, for arbitrary small indexed families.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeIndexedPushout

variable {O I : Type u} {Q R : I → SimplicialQuiver.Data O}

/-- The same original free sum map is isomorphic to the actual map of the two supplied coproducts. -/
def sumMapArrowIso (m : ∀ i x y, (Q i).Hom x y ⟶ (R i).Hom x y)
    (c₁ : Cofan (fun i => FreeQuiver.object (Q i))) (c₂ : Cofan (fun i => FreeQuiver.object (R i)))
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ i, c₁.inj i ≫ φ = FreeQuiver.map (m i) ≫ c₂.inj i) :
    Arrow.mk (FreeQuiver.sumMap m) ≅ Arrow.mk φ := by
  let e₁ := IsColimit.coconePointUniqueUpToIso (FreeQuiver.sumIsColimit Q) h₁
  let e₂ := IsColimit.coconePointUniqueUpToIso (FreeQuiver.sumIsColimit R) h₂
  have he₁ (i : I) : FreeQuiver.sumInclusion Q i ≫ e₁.hom = c₁.inj i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (FreeQuiver.sumIsColimit Q) h₁ (Discrete.mk i)
  have he₂ (i : I) : FreeQuiver.sumInclusion R i ≫ e₂.hom = c₂.inj i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (FreeQuiver.sumIsColimit R) h₂ (Discrete.mk i)
  refine Arrow.isoMk' _ _ e₁ e₂ ?_
  symm
  apply (FreeQuiver.sumIsColimit Q).hom_ext
  rintro ⟨i⟩
  change FreeQuiver.sumInclusion Q i ≫ (FreeQuiver.sumMap m ≫ e₂.hom) =
    FreeQuiver.sumInclusion Q i ≫ (e₁.hom ≫ φ)
  calc
    _ = FreeQuiver.map (m i) ≫ FreeQuiver.sumInclusion R i ≫ e₂.hom :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ e₂.hom) (FreeQuiver.sumInclusion_sumMap m i)).trans (Category.assoc _ _ _))
    _ = FreeQuiver.map (m i) ≫ c₂.inj i := congrArg (fun t => FreeQuiver.map (m i) ≫ t) (he₂ i)
    _ = c₁.inj i ≫ φ := (hφ i).symm
    _ = _ := (congrArg (fun t => t ≫ φ) (he₁ i).symm).trans (Category.assoc _ _ _)

/-- The same whole original indexed free attachment is anodyne on each actual old Hom map. -/
theorem hom_anodyne_of_isPushout (m : ∀ i x y, (Q i).Hom x y ⟶ (R i).Hom x y)
    (hm : ∀ i x y, SSet.anodyneExtensions (m i x y))
    (c₁ : Cofan (fun i => FreeQuiver.object (Q i))) (c₂ : Cofan (fun i => FreeQuiver.object (R i)))
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ i, c₁.inj i ≫ φ = FreeQuiver.map (m i) ≫ c₂.inj i)
    {C D : FixedObjects O} (s : c₁.pt ⟶ C) (j : C ⟶ D) (k : c₂.pt ⟶ D)
    (hp : IsPushout s φ j k) (x y : O) : SSet.anodyneExtensions (homMap j x y) := by
  let e := sumMapArrowIso m c₁ c₂ h₁ h₂ φ hφ
  let e₁ := Arrow.leftFunc.mapIso e
  let e₂ := Arrow.rightFunc.mapIso e
  let ms : ∀ a b : O, (FreeQuiver.sumQuiver Q).Hom a b ⟶ (FreeQuiver.sumQuiver R).Hom a b :=
    fun a b => SSet.IndexedSums.map (fun i => (Q i).Hom a b) (fun i => m i a b)
  have hms : ∀ a b, SSet.anodyneExtensions (ms a b) := fun a b =>
    SSet.IndexedSums.map_property (fun i => (Q i).Hom a b) SSet.anodyneExtensions
      (fun i => m i a b) (fun i => hm i a b)
  have hn : IsPushout (e₁.hom ≫ s) (FreeQuiver.map ms) j (e₂.hom ≫ k) :=
    hp.of_iso' e₁ (Iso.refl _) e₂ (Iso.refl _)
      (by simp) (e.hom.w) (by simp) (by simp)
  exact FreeQuiverPushout.hom_anodyne_of_isPushout
    (Q := FreeQuiver.sumQuiver Q) (R := FreeQuiver.sumQuiver R) (C := C) (D := D)
    ms hms (e₁.hom ≫ s) j (e₂.hom ≫ k) hn x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeIndexedPushout
