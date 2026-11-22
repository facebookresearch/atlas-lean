/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentEquivalenceCoreEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.ComponentUnionPiZero

/-!
# Actual groupoid of components of the full original equivalence core

The full original core inclusion injects every actual original Hom
component and its image is exactly the original invertible classes.
Each actual source component arrow has its genuine original inverse
class lifted into the SAME selected Hom. Faithfulness reflects both
whole inverse equations, proving the actual core component category
is a groupoid. No scalar weak or strict-inverse premise is assumed.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore

variable (C : Carrier.{u})

/-- The SAME full original core inclusion is faithful on its entire original component Homs. -/
instance componentInclusion_faithful : (ComponentCategory.mapFunctor (inclusion C)).Faithful where
  map_injective {x y} := SSet.componentUnion_piZero_injective (equivalentClass C x y)

/-- Every SAME actual original core component arrow has an invertible original inclusion image. -/
theorem componentInclusion_isIso {x y : ComponentCategory.objects.{u} (object C)} (a : x ⟶ y) :
    IsIso ((ComponentCategory.mapFunctor (inclusion C)).map a) :=
  SSet.componentUnion_piZero_selected (equivalentClass C x y) a

/-- Every full original invertible component arrow lifts to the SAME selected original core Hom class. -/
theorem componentInclusion_preimage {x y : object C}
    (a : ComponentCategory.objectOf.{u} C x ⟶ ComponentCategory.objectOf.{u} C y) (ha : IsIso a) :
    ∃ b : ComponentCategory.objectOf.{u} (object C) x ⟶ ComponentCategory.objectOf.{u} (object C) y,
      (ComponentCategory.mapFunctor (inclusion C)).map b = a :=
  SSet.componentUnion_piZero_surjective_on (equivalentClass C x y) a ha

/-- The SAME full original component-equivalence core genuinely has a groupoid component category. -/
instance component_isGroupoid : IsGroupoid (ComponentCategory.objects.{u} (object C)) where
  all_isIso {x y} a := by
    let F := ComponentCategory.mapFunctor (inclusion C)
    have ha : IsIso (F.map a) := componentInclusion_isIso C a
    let e := @asIso _ _ _ _ (F.map a) ha
    obtain ⟨b, hb⟩ := componentInclusion_preimage C e.inv e.isIso_inv
    refine ⟨⟨b, ?_, ?_⟩⟩
    · apply F.map_injective
      exact (F.map_comp a b).trans
        ((congrArg (fun c => F.map a ≫ c) hb).trans
          (e.hom_inv_id.trans (F.map_id x).symm))
    · apply F.map_injective
      exact (F.map_comp b a).trans
        ((congrArg (fun c => c ≫ F.map a) hb).trans
          (e.inv_hom_id.trans (F.map_id y).symm))

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
