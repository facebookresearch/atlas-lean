/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Evaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective

/-!
# Literal native sequential generating families

Free images are indexed by the actual base-family arrows and natural levels.
The label type is retained, and its Small witness proves smallness at an
independent size universe. The native boundary and horn families use the
explicit pointed CGWH cofibrant-generation data.
-/

set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

namespace PointedCGWH.SequentialSpectrum

/-- The literal free images of an actual pointed morphism family at all
natural levels, for any suspension coordinate. -/
noncomputable def liftedGenerators (K : PointedCGWH.{u, v})
    (P : MorphismProperty PointedCGWH.{u, v}) :
    MorphismProperty (CategoryTheory.Spectra.Sequential.Spectrum (C := PointedCGWH.{u, v}) K) :=
  MorphismProperty.ofHoms
    (fun p : ℕ × P.toSet => (freeAt K p.1).map p.2.1.hom)

/-- Membership retains the correlated level and actual source/target arrow. -/
theorem liftedGenerators_iff (K : PointedCGWH.{u, v})
    (P : MorphismProperty PointedCGWH.{u, v})
    {X Y : CategoryTheory.Spectra.Sequential.Spectrum (C := PointedCGWH.{u, v}) K} (g : X ⟶ Y) :
    liftedGenerators K P g ↔
      ∃ p : ℕ × P.toSet, Arrow.mk g = Arrow.mk ((freeAt K p.1).map p.2.1.hom) :=
  MorphismProperty.ofHoms_iff _ g

/-- Every actual free image belongs to the displayed lifted family. -/
theorem freeAt_map_mem_liftedGenerators (K : PointedCGWH.{u, v})
    (P : MorphismProperty PointedCGWH.{u, v})
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B) (hf : P f) (n : ℕ) :
    liftedGenerators K P ((freeAt K n).map f) := by
  let q : P.toSet := ⟨Arrow.mk f, hf⟩
  exact MorphismProperty.ofHoms.mk (n, q)

/-- Literal lifting preserves smallness at an independent size universe. -/
theorem liftedGenerators_isSmall (K : PointedCGWH.{u, v})
    (P : MorphismProperty PointedCGWH.{u, v}) [P.IsSmall.{w}] :
    (liftedGenerators K P).IsSmall.{w} := by
  let _ : Small.{w} P.toSet := inferInstance
  let _ : Small.{w} ℕ := inferInstance
  let _ : Small.{w} (ℕ × P.toSet) := inferInstance
  exact MorphismProperty.isSmall_ofHoms
    (fun p : ℕ × P.toSet => (freeAt K p.1).map p.2.1.hom)

/-- The native boundary family uses the actual explicit pointed generators. -/
noncomputable def boundaryGenerators :
    MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  liftedGenerators PointedCGWH.sphereOne.{u, v}
    PointedCGWH.cofibrantGenerationData.{u, v}.I

/-- The native horn family uses the actual explicit pointed generators. -/
noncomputable def hornGenerators :
    MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  liftedGenerators PointedCGWH.sphereOne.{u, v}
    PointedCGWH.cofibrantGenerationData.{u, v}.J

theorem boundaryGenerators_isSmall : boundaryGenerators.{u, v}.IsSmall.{v} := by
  let _ : PointedCGWH.cofibrantGenerationData.{u, v}.I.IsSmall.{v} :=
    PointedCGWH.cofibrantGenerationData.{u, v}.I_smallObject.isSmall
  exact liftedGenerators_isSmall PointedCGWH.sphereOne
    PointedCGWH.cofibrantGenerationData.{u, v}.I

theorem hornGenerators_isSmall : hornGenerators.{u, v}.IsSmall.{v} := by
  let _ : PointedCGWH.cofibrantGenerationData.{u, v}.J.IsSmall.{v} :=
    PointedCGWH.cofibrantGenerationData.{u, v}.J_smallObject.isSmall
  exact liftedGenerators_isSmall PointedCGWH.sphereOne
    PointedCGWH.cofibrantGenerationData.{u, v}.J

/-- The natural-level free family is exactly the actual enriched-index family. -/
theorem liftedGenerators_eq_enrichedGenerators (K : PointedCGWH.{u, v})
    (P : MorphismProperty PointedCGWH.{u, v}) :
    liftedGenerators K P = HomotopicalAlgebra.EnrichedProjective.generators
      (A := CategoryTheory.Spectra.Sequential.Index K) P := by
  ext X Y f
  let L : CategoryTheory.Spectra.Sequential.Index K →
      PointedCGWH.{u, v} ⥤ CategoryTheory.Spectra.Sequential.Spectrum
        (C := PointedCGWH.{u, v}) K :=
    fun a => EnrichedFunctorCat.Free.functor a
  change liftedGenerators K P f ↔ MorphismProperty.adjointFamilyGenerators L P f
  constructor
  · intro hf
    obtain ⟨⟨n, q⟩, hq⟩ := (liftedGenerators_iff K P f).mp hf
    exact (MorphismProperty.adjointFamilyGenerators_iff L P f).mpr
      ⟨⟨CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n, q⟩, hq⟩
  · intro hf
    obtain ⟨⟨a, q⟩, hq⟩ :=
      (MorphismProperty.adjointFamilyGenerators_iff L P f).mp hf
    rcases a with ⟨n⟩
    exact (liftedGenerators_iff K P f).mpr ⟨⟨n, q⟩, hq⟩

end PointedCGWH.SequentialSpectrum
