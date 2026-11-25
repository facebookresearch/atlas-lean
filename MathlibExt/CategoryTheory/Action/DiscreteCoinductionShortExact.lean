/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Action.DiscreteAbelianShortExact
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoinductionExactness

/-! # Actual continuous coinduction of original short-exact coefficient sequences -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The existing coinduction functor preserves actual original Hom addition. -/
instance coind_additive : (coind.{g, w} (G := G)).Additive where
  map_add := by
    intro A B f h
    apply (forget G).map_injective
    ext c
    rfl

/-- Actual continuous coinduction retains the real underlying short-exact sequence. -/
theorem coind_forget_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) :
    ((S.map coind.{g, w}).map (forget.{g, max g w} G)).ShortExact := by
  let T := S.map (forget.{g, max g w} G)
  let U := (S.map coind.{g, w}).map (forget.{g, max g w} G)
  have hf : Function.Injective (homToAdd S.f) := (AddCommGrpCat.mono_iff_injective T.f).mp hS.mono_f
  have hq : Function.Surjective (homToAdd S.g) := (AddCommGrpCat.epi_iff_surjective T.g).mp hS.epi_g
  have hex : ∀ y : underlying S.X₂, homToAdd S.g y = 0 → ∃ x : underlying S.X₁,
      homToAdd S.f x = y :=
    T.ab_exact_iff.mp hS.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply U.ab_exact_iff.mpr
    intro c hc
    exact ContinuousCohomology.coindOneMap_lift_kernel.{0, g, w}
      (toTopRep.map S.f) (toTopRep.map S.g) hex c hc
  · apply (AddCommGrpCat.mono_iff_injective U.f).mpr
    exact ContinuousCohomology.coindOneMap_injective.{0, g, w} (toTopRep.map S.f) hf
  · apply (AddCommGrpCat.epi_iff_surjective U.g).mpr
    exact ContinuousCohomology.coindOneMap_surjective.{0, g, w} (toTopRep.map S.g) hq

/-- The coinduced original sequence is genuinely short exact in discrete continuous actions. -/
theorem coind_shortExact_of_forget
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) : (S.map coind.{g, w}).ShortExact :=
  shortExact_of_forget_shortExact.{g, max g w} (G := G) (S.map coind.{g, w})
    (coind_forget_shortExact.{g, w} (G := G) S hS)

end CategoryTheory.DiscreteAbelianAction
