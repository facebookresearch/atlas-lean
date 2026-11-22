/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.TailPullbackColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono

/-!
# Monomorphisms in fixed-base pullback tail diagrams

Actual Mono transitions of the SAME fixed-base tail pullback diagram.

The first projection and original X transition, together with the fixed
second projection, prove Mono. Original Y transitions need not be mono.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace SSet.RezkTailPullbackColimit

/-- Every actual tail pullback transition is mono from the original X
transition and the unchanged second projection; no Mono Y is required. -/
theorem tailPullbackDiagram_map_mono
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (hmX : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (X.map f))
    {i j : ℕ} (f : i ⟶ j) : Mono ((tailPullbackDiagram p n).map f) := by
  let : Mono (X.map ((natTail n).map f)) := hmX ((natTail n).map f)
  have legs := tailPullbackDiagram_map_legs p n f
  constructor
  intro T a b hab
  apply pullback.hom_ext
  · apply (cancel_mono (X.map ((natTail n).map f))).mp
    calc
      (a ≫ pullback.fst _ _) ≫ X.map ((natTail n).map f) =
          a ≫ ((tailPullbackDiagram p n).map f ≫ pullback.fst _ _) := by
        rw [Category.assoc, legs.1]
      _ = (a ≫ (tailPullbackDiagram p n).map f) ≫ pullback.fst _ _ :=
        (Category.assoc _ _ _).symm
      _ = (b ≫ (tailPullbackDiagram p n).map f) ≫ pullback.fst _ _ :=
        congrArg (fun z => z ≫ pullback.fst _ _) hab
      _ = b ≫ ((tailPullbackDiagram p n).map f ≫ pullback.fst _ _) :=
        Category.assoc _ _ _
      _ = (b ≫ pullback.fst _ _) ≫ X.map ((natTail n).map f) := by
        rw [legs.1, Category.assoc]
  · calc
      a ≫ pullback.snd _ _ =
          a ≫ ((tailPullbackDiagram p n).map f ≫ pullback.snd _ _) := by rw [legs.2]
      _ = (a ≫ (tailPullbackDiagram p n).map f) ≫ pullback.snd _ _ :=
        (Category.assoc _ _ _).symm
      _ = (b ≫ (tailPullbackDiagram p n).map f) ≫ pullback.snd _ _ :=
        congrArg (fun z => z ≫ pullback.snd _ _) hab
      _ = b ≫ ((tailPullbackDiagram p n).map f ≫ pullback.snd _ _) :=
        Category.assoc _ _ _
      _ = b ≫ pullback.snd _ _ := by rw [legs.2]

end SSet.RezkTailPullbackColimit
