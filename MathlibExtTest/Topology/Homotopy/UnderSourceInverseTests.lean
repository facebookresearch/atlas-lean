/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.UnderSourceInverse
public import MathlibExt.Topology.CWComplex.BasedWhitehead

/-!
# Whole source-image and based inverse clients

The one source-under factory fixes the entire common source image in both
inverse families. The based theorem specializes the same machinery to the
one-point source and retains both original singleton-relative families.
-/

public section

noncomputable section

open CategoryTheory HomotopicalAlgebra Topology
open scoped TopCat.modelCategory

universe u

namespace UnderSourceInverseTests

/-- Every original source point is fixed at independent left/right times. -/
theorem allSourcePoints {S Y Z : TopCat.{u}} (i : S ⟶ Y) (j : S ⟶ Z)
    [Cofibration i] [Cofibration j] (f : Y ⟶ Z)
    (hSource : i ≫ f = j) (hWeak : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Z ⟶ Y, j ≫ g = i ∧
      ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 Y : Y ⟶ Y).hom (Set.range i),
      ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Z : Z ⟶ Z).hom (Set.range j),
        ∀ s : S, ∀ t v : unitInterval, HL (t, i s) = i s ∧ HR (v, j s) = j s := by
  let R := TopCat.sourceRelativeInverseOfWeak i j f hSource hWeak
  refine ⟨R.inverse, R.inverse_source, R.leftHomotopy, R.rightHomotopy, ?_⟩
  intro s t v
  exact ⟨R.leftHomotopy.eq_snd t ⟨s, rfl⟩, R.rightHomotopy.eq_snd v ⟨s, rfl⟩⟩

/-- A two-point source tests simultaneous image fixation, rather than one marked point. -/
theorem twoSourcePoints {Y Z : TopCat.{u}}
    (i : TopCat.of (ULift.{u} Bool) ⟶ Y) (j : TopCat.of (ULift.{u} Bool) ⟶ Z)
    [Cofibration i] [Cofibration j] (f : Y ⟶ Z)
    (hSource : i ≫ f = j) (hWeak : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Z ⟶ Y, j ≫ g = i ∧
      ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 Y : Y ⟶ Y).hom (Set.range i),
      ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Z : Z ⟶ Z).hom (Set.range j),
        ∀ b : Bool, ∀ t v : unitInterval,
          HL (t, i (ULift.up b)) = i (ULift.up b) ∧
          HR (v, j (ULift.up b)) = j (ULift.up b) := by
  obtain ⟨g, hg, HL, HR, h⟩ := allSourcePoints i j f hSource hWeak
  exact ⟨g, hg, HL, HR, fun b t v => h (ULift.up b) t v⟩

/-- The public PUnit specialization retains both whole point-relative families. -/
theorem basedSpecialization (X Y : TopCat.{u}) (x : X) (y : Y)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const y : TopCat.of PUnit.{u + 1} ⟶ Y)]
    (f : X ⟶ Y) (hxy : f x = y) (hWeak : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x},
      ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y},
        ∀ t v : unitInterval, HL (t, x) = x ∧ HR (v, y) = y := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ :=
    TopCat.exists_based_inverse_of_weak_of_cofibrant_points X Y x y f hxy hWeak
  exact ⟨g, hg, HL, HR, fun t v =>
    ⟨HL.eq_snd t (Set.mem_singleton x), HR.eq_snd v (Set.mem_singleton y)⟩⟩

end UnderSourceInverseTests

end
