/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCountableHoms
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSmallColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual countable initial objects, coproducts and pushouts on original labels

The genuine fixed-label presentation colimits retain their actual
countable Hom simplices. This includes the same original initial
enrichment and every countable coproduct/pushout used by the actual
boundary small-object construction.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} [Countable O]

/-- The SAME original fixed-label initial enrichment has countable full Homs. -/
instance initial_countableHoms : CountableHoms (⊥_ (FixedObjects O)) := by
  have (j : Discrete PEmpty) : CountableHoms ((Functor.empty (FixedObjects O)).obj j) :=
    PEmpty.elim j.as
  exact colimit_countable (Functor.empty (FixedObjects O))

/-- Every actual countable original coproduct retains countable entire Homs on its SAME labels. -/
instance coproduct_countableHoms {I : Type v} [Countable I] (C : I → FixedObjects O)
    [∀ i, CountableHoms (C i)] : CountableHoms (∐ C) := by
  have : Countable (Discrete I) :=
    Countable.of_equiv I ⟨Discrete.mk, Discrete.as, fun _ => rfl, fun _ => rfl⟩
  have (j : Discrete I) : CountableHoms ((Discrete.functor C).obj j) := by
    change CountableHoms (C j.as)
    infer_instance
  exact colimit_countable (Discrete.functor C)

/-- The genuine original fixed-label pushout of actual countable Hom enrichments has countable full Homs. -/
instance pushout_countableHoms {C A B : FixedObjects O}
    [CountableHoms C] [CountableHoms A] [CountableHoms B]
    (f : C ⟶ A) (g : C ⟶ B) : CountableHoms (pushout f g) := by
  have (j : WalkingSpan) : CountableHoms ((span f g).obj j) := by
    rcases j with _ | (_ | _)
    · change CountableHoms C
      infer_instance
    · change CountableHoms A
      infer_instance
    · change CountableHoms B
      infer_instance
  exact colimit_countable (span f g)

end CategoryTheory.SimplicialEnrichment.FixedObjects
