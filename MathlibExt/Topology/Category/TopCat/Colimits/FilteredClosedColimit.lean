/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Filtered closed-embedding colimit legs in `TopCat`

For a filtered diagram `F : J ⥤ TopCat` whose every transition map is a
closed embedding, every colimit cocone leg is a closed embedding.

The proof reuses the filtered common-target API (`IsFiltered.max`,
`IsFiltered.leftToMax`, `IsFiltered.rightToMax`), the filtered-colimit
equality API (`Types.FilteredColimit.isColimit_eq_iff'`), the
underlying-`Type` colimit (`isColimitOfPreserves (forget TopCat) hc`),
and the colimit topology (`isClosed_iff_of_isColimit`).

Injectivity of each leg is equalization after a filtered common target.
The key closed-map step identifies, for closed `S` in the source leg and
any other leg `j`, the preimage of the image with one continuous
preimage after the common target `k = max j₀ j`: the legwise preimage
is closed as a preimage of a closed image. Inducing follows from
injectivity via `S = ι⁻¹' (ι '' S)`; the closed range is the image of
`univ`.

No presentability, compact-generation, arbitrary-colimit-preservation,
or model-category claim is made.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits Topology

namespace TopCat

section FilteredClosedColimit

variable {J : Type v} [Category.{w} J] [IsFiltered J]
variable {F : J ⥤ TopCat.{u}} (c : Cocone F)

omit [IsFiltered J] in
/-- Cocone naturality at the function level, through the underlying
`Type` naturality: pushing forward along a transition map and then taking
the leg equals taking the source leg. -/
private lemma leg_map_apply {i j : J} (f : i ⟶ j) (x : F.obj i) :
    (c.ι.app j).hom ((F.map f).hom x) = (c.ι.app i).hom x :=
  ConcreteCategory.congr_hom ((forget TopCat).congr_map (c.w f)) x

/-- Each colimit leg is injective when every transition map is injective:
equal points in one leg are equalized after a filtered common target
(`isColimit_eq_iff'`), where transition injectivity closes the goal. -/
private lemma injective_ι_of_isColimit (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Injective (F.map f).hom)
    (j₀ : J) : Function.Injective (c.ι.app j₀).hom := by
  intro x y hxy
  obtain ⟨k, f, hfk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget TopCat) hc) _ _).1 hxy
  exact hF f hfk

/-- Preimage identification after the filtered common target: the
preimage in leg `j` of the image of `S` along leg `j₀` is the continuous
preimage of the pushed-forward image. Forward moves a colimit
identification into the common target by leg injectivity; backward is
cocone naturality. -/
private lemma preimage_image_eq
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom) (j₀ j : J)
    (S : Set (F.obj j₀)) :
    (c.ι.app j).hom ⁻¹' ((c.ι.app j₀).hom '' S) =
      (F.map (IsFiltered.rightToMax j₀ j)).hom ⁻¹'
        ((F.map (IsFiltered.leftToMax j₀ j)).hom '' S) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have ha := leg_map_apply c (IsFiltered.leftToMax j₀ j) x
    have hb := leg_map_apply c (IsFiltered.rightToMax j₀ j) y
    refine ⟨x, hx, hinj _ ?_⟩
    rw [ha, hb, hxy]
  · rintro ⟨x, hx, hxy⟩
    have ha := leg_map_apply c (IsFiltered.leftToMax j₀ j) x
    have hb := leg_map_apply c (IsFiltered.rightToMax j₀ j) y
    refine ⟨x, hx, ?_⟩
    rw [← ha, ← hb, hxy]

/-- Each leg is a closed map: the image of a closed set is closed,
tested legwise through `isClosed_iff_of_isColimit` and the preimage
identification above. -/
private lemma isClosedMap_ι_of_isColimit (hc : IsColimit c)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (j₀ : J) : IsClosedMap (c.ι.app j₀).hom := by
  intro S hS
  rw [isClosed_iff_of_isColimit c hc]
  intro j
  rw [preimage_image_eq c hinj j₀ j S]
  exact ((hF (IsFiltered.leftToMax j₀ j)).isClosedMap _ hS).preimage
    (hF (IsFiltered.rightToMax j₀ j)).continuous

/-- Main statement: for `J` filtered, a `TopCat` diagram whose every
transition map is a closed embedding has every colimit cocone leg a
closed embedding. Accepts any colimit cocone; no global `HasColimit`
or stronger order/finite hypotheses. -/
theorem isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (j₀ : J) : IsClosedEmbedding (c.ι.app j₀).hom := by
  have hinj : ∀ j, Function.Injective (c.ι.app j).hom := fun j =>
    injective_ι_of_isColimit c hc (fun _ _ f => (hF f).injective) j
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (c.ι.app j₀).hom.continuous (hinj j₀)
    (isClosedMap_ι_of_isColimit c hc hinj hF j₀)

end FilteredClosedColimit

end TopCat
