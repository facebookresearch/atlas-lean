/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiverMonoSourcePushoutWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeIndexedMonoPushoutScalarPresentation

/-!
# Original weak source gluing for entire indexed mono-quiver attachments

The actual indexed generator coproducts retain every original index and
endpoint pair, including the empty family. Their canonical comparison
identifies the SAME whole mono-quiver attachment. The original old Hom
maps are monic, and any actual subsequent cobase change preserves its
supplied genuinely Homwise weak source map.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeIndexedMonoPushout
variable {O I : Type u} {Q R : I → SimplicialQuiver.Data O}
  (m : ∀ i x y, (Q i).Hom x y ⟶ (R i).Hom x y)
  (hm : ∀ i x y, Mono (m i x y))
  (c₁ : Cofan (fun i => FreeQuiver.object (Q i)))
  (c₂ : Cofan (fun i => FreeQuiver.object (R i)))
  (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt)
  (hφ : ∀ i, c₁.inj i ≫ φ = FreeQuiver.map (m i) ≫ c₂.inj i)
  {C P D E : FixedObjects O} (s : c₁.pt ⟶ C) (j : C ⟶ P) (k : c₂.pt ⟶ P)
  (hp : IsPushout s φ j k)

include hm h₁ h₂ hφ hp in
/-- Every SAME old full Hom map in the entire original indexed attachment is monic. -/
theorem leftHom_mono (a b : O) : Mono (homMap j a b) :=
  FreeQuiverMonoPushout.leftHom_mono (sumHom m) (sumHom_mono m hm)
    (attaching m c₁ c₂ h₁ h₂ φ hφ s) j (target m c₁ c₂ h₁ h₂ φ hφ k)
    (isPushout m c₁ c₂ h₁ h₂ φ hφ s j k hp) a b

include hm h₁ h₂ hφ hp in
/-- The SAME actual weak source map survives cobase change along every full indexed original attachment. -/
theorem sourcePushout_weak (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences O F)
    (d : P ⟶ E) (c : D ⟶ E) (sq : IsPushout j F d c) :
    FixedObjectModel.weakEquivalences O d :=
  FreeQuiverMonoPushout.sourcePushout_weak (sumHom m) (sumHom_mono m hm)
    (attaching m c₁ c₂ h₁ h₂ φ hφ s) j (target m c₁ c₂ h₁ h₂ φ hφ k)
    (isPushout m c₁ c₂ h₁ h₂ φ hφ s j k hp) F hF d c sq

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeIndexedMonoPushout
