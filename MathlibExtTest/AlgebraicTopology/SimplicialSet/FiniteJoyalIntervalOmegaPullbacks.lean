/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaPullbacks

/-!
# Actual pullback comparison and its two projections for the omega functor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits SSet.joyalInterval

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaPullbacks

/-- Arbitrary span maps have the actual comparison isomorphism and both prescribed projections. -/
theorem comparison {X Y V : SSet.{u}} (f : X ⟶ Y) (g : V ⟶ Y) :
    ∃ e : auxiliaryOmegaFreeFiller.obj (pullback f g) ≅
        pullback (auxiliaryOmegaFreeFiller.map f) (auxiliaryOmegaFreeFiller.map g),
      e.hom = pullbackComparison auxiliaryOmegaFreeFiller f g ∧
        e.hom ≫ pullback.fst _ _ = auxiliaryOmegaFreeFiller.map (pullback.fst f g) ∧
        e.hom ≫ pullback.snd _ _ = auxiliaryOmegaFreeFiller.map (pullback.snd f g) := by
  refine ⟨PreservesPullback.iso auxiliaryOmegaFreeFiller f g, ?_, ?_, ?_⟩
  · exact PreservesPullback.iso_hom auxiliaryOmegaFreeFiller f g
  · exact PreservesPullback.iso_hom_fst auxiliaryOmegaFreeFiller f g
  · exact PreservesPullback.iso_hom_snd auxiliaryOmegaFreeFiller f g

/-- The original monic-span intersection comparison retains its actual two projections. -/
theorem monic_span {X Y V : SSet.{u}} (f : X ⟶ Y) (g : V ⟶ Y) [Mono f] [Mono g] :
    IsIso (pullbackComparison auxiliaryOmegaFreeFiller f g) ∧
      pullbackComparison auxiliaryOmegaFreeFiller f g ≫ pullback.fst _ _ =
        auxiliaryOmegaFreeFiller.map (pullback.fst f g) ∧
      pullbackComparison auxiliaryOmegaFreeFiller f g ≫ pullback.snd _ _ =
        auxiliaryOmegaFreeFiller.map (pullback.snd f g) := by
  obtain ⟨e, he, hf, hg⟩ := comparison f g
  refine ⟨?_, ?_, ?_⟩
  · rw [← he]; infer_instance
  · simpa only [← he] using hf
  · simpa only [← he] using hg

/-- Native pullback preservation supplies map monicity, with no new production instance. -/
theorem map_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Mono (auxiliaryOmegaFreeFiller.map i) := by
  infer_instance

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaPullbacks
