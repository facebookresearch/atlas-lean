/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiverMonoPushoutScalarPresentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeIndexedPushoutAnodyne
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
# Full scalar free presentations of entire indexed monic attachments

Every supplied original free coproduct cocone is compared with the
literal indexed generating quiver. Its actual original pushout square
then gives the constructed scalar free presentation with all original
cell labels and full old Hom maps retained. Empty indexing families and
loop endpoint pairs use these same original maps.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeIndexedMonoPushout
open RelativeWords

variable {O I : Type u} {Q R : I → SimplicialQuiver.Data O}
  (m : ∀ i x y, (Q i).Hom x y ⟶ (R i).Hom x y)
  (hm : ∀ i x y, Mono (m i x y))

/-- The full original indexed generator inclusion at the same endpoint pair. -/
def sumHom (x y : O) : (FreeQuiver.sumQuiver Q).Hom x y ⟶ (FreeQuiver.sumQuiver R).Hom x y :=
  SSet.IndexedSums.map (fun i => (Q i).Hom x y) (fun i => m i x y)

include hm in
/-- The entire indexed inclusion is genuinely monic from the original component maps. -/
theorem sumHom_mono (x y : O) : Mono (sumHom m x y) := by
  have hq (q : SimplexCategoryᵒᵖ) : Mono ((sumHom m x y).app q) := by
    apply (mono_iff_injective _).mpr
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.mk (β := fun i => ((R i).Hom x y).obj q) i ((m i x y).app q a) =
      Sigma.mk (β := fun i => ((R i).Hom x y).obj q) j ((m j x y).app q b) at h
    obtain ⟨rfl, hab⟩ := Sigma.mk.inj_iff.mp h
    let _ := hm i x y
    have ha := injective_of_mono ((m i x y).app q) (eq_of_heq hab)
    exact congrArg (Sigma.mk (β := fun i => ((Q i).Hom x y).obj q) i) ha
  let _ : ∀ q, Mono ((sumHom m x y).app q) := hq
  exact NatTrans.mono_of_mono_app _

variable (c₁ : Cofan (fun i => FreeQuiver.object (Q i)))
  (c₂ : Cofan (fun i => FreeQuiver.object (R i)))
  (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt)
  (hφ : ∀ i, c₁.inj i ≫ φ = FreeQuiver.map (m i) ≫ c₂.inj i)
  {C D : FixedObjects O} (s : c₁.pt ⟶ C) (j : C ⟶ D) (k : c₂.pt ⟶ D)
  (hp : IsPushout s φ j k)

/-- The actual free-domain attachment read under the complete original coproduct comparison. -/
def attaching : FreeQuiver.object (FreeQuiver.sumQuiver Q) ⟶ C :=
  (Arrow.leftFunc.mapIso (FreeIndexedPushout.sumMapArrowIso m c₁ c₂ h₁ h₂ φ hφ)).hom ≫ s

/-- The actual target map retains the complete original second coproduct comparison. -/
def target : FreeQuiver.object (FreeQuiver.sumQuiver R) ⟶ D :=
  (Arrow.rightFunc.mapIso (FreeIndexedPushout.sumMapArrowIso m c₁ c₂ h₁ h₂ φ hφ)).hom ≫ k

include hp in
/-- The actual whole original indexed pushout square becomes the same full free-quiver square. -/
theorem isPushout : IsPushout (attaching m c₁ c₂ h₁ h₂ φ hφ s)
    (FreeQuiver.map (sumHom m)) j (target m c₁ c₂ h₁ h₂ φ hφ k) := by
  let e := FreeIndexedPushout.sumMapArrowIso m c₁ c₂ h₁ h₂ φ hφ
  exact hp.of_iso' (Arrow.leftFunc.mapIso e) (Iso.refl _)
    (Arrow.rightFunc.mapIso e) (Iso.refl _)
    (by simp [attaching, e]) e.hom.w (by simp) (by simp [target, e])

/-- Construct the entire original scalar free presentation of this actual indexed attachment. -/
def scalarPresentation (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    FreePresentation.{u,u,u} (scalarCategory D q) :=
  FreeQuiverMonoPushout.scalarPresentation (sumHom m) (sumHom_mono m hm)
    (attaching m c₁ c₂ h₁ h₂ φ hφ s) j (target m c₁ c₂ h₁ h₂ φ hφ k)
    (isPushout m c₁ c₂ h₁ h₂ φ hφ s j k hp) q P

include hm hp in
/-- Every old complete path retains the SAME supplied original indexed pushout Hom map. -/
theorem scalarPresentation_oldPath (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) {x y : O}
    (p : @Quiver.Path O P.quiver x y) :
    (scalarPresentation m hm c₁ c₂ h₁ h₂ φ hφ s j k hp q P).map
        (RelativeWords.FreePaths.oldPath P.quiver
          (RelativeAttachment.newAt
            (FreeQuiverMonoPushout.data (sumHom m) (sumHom_mono m hm)
              (attaching m c₁ c₂ h₁ h₂ φ hφ s)) q) p) =
      (homMap j x y).app q (P.map p) :=
  FreeQuiverMonoPushout.scalarPresentation_oldPath (sumHom m) (sumHom_mono m hm)
    (attaching m c₁ c₂ h₁ h₂ φ hφ s) j (target m c₁ c₂ h₁ h₂ φ hφ k)
    (isPushout m c₁ c₂ h₁ h₂ φ hφ s j k hp) q P p

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeIndexedMonoPushout
