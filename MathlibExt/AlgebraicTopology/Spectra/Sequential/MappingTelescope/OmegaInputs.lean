/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.CompactFactorization
import MathlibExt.Topology.Category.CGWH.Colimits.ClosedWeakNatCocone

/-!
# The actual native telescope on original Omega inputs

All original stages, projections, transitions and units remain. Genuine
native weak closed-cocone closure makes the telescope unit level weak on
Omega inputs, and the original unit naturalities preserve Omega inputs
and their level weak maps. Arbitrary-input Omega remains separate.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The SAME original caller-B level weak class is the actual complete original component class. -/
theorem levelWeak_iff_components {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f ↔
      ∀ m : ℕ, CGWH.weakHomotopyEquivalences
        (PointedCGWH.SequentialSpectrum.levelMap f m).right := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  rw [EvaluationTransfer.evaluationProperty_iff]
  have hp {A C : PointedCGWH.{u, v}} (g : A ⟶ C) :
      weakEquivalences PointedCGWH.{u, v} g ↔ CGWH.weakHomotopyEquivalences g.right :=
    (HomotopicalAlgebra.weakEquivalence_iff g).symm.trans
      ((PointedCGWH.weakEquivalence_iff g).trans (CGWH.modelCategory.weakEquivalence_iff g.right))
  constructor
  · intro h m
    exact (hp _).mp
      (h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m))
  · intro h a
    rcases a with ⟨m⟩
    exact (hp _).mpr (h m)

/-- Every SAME original full stage functor preserves the original native level weak class. -/
theorem stageFunctor_map_levelWeak (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((stage n).functor.map f) := by
  let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
  have hpx : W ((projection n).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence n X)
  have hpy : W ((projection n).app Y) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence n Y)
  have hr : W ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n).map f) :=
    PointedCGWH.SequentialSpectrum.OrderedLoop.iterate_map_levelWeak n f hf
  have hnat : (stage n).functor.map f ≫ (projection n).app Y =
      (projection n).app X ≫ (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n).map f :=
    (projection n).naturality f
  have hn : W ((stage n).functor.map f ≫ (projection n).app Y) :=
    (congrArg (fun g : (stage n).functor.obj X ⟶
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n).obj Y => W g) hnat).mpr
        (W.comp_mem _ _ hpx hr)
  exact W.of_postcomp _ _ hpy hn

/-- Every SAME original target section is level weak on arbitrary original inputs. -/
theorem stageSection_levelWeak (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((stageSection n).app X) := by
  let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
  have hp : W ((projection (n + 1)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence (n + 1) X)
  have h : (stageSection n).app X ≫ (projection (n + 1)).app X =
      𝟙 ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X) :=
    congr_app (stageSection_projection n) X
  have hcomp : W ((stageSection n).app X ≫ (projection (n + 1)).app X) :=
    (congrArg (fun g : (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X ⟶
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X => W g) h).mpr
        (W.id_mem _)
  exact W.of_postcomp _ _ hp hcomp

/-- All SAME original transitions on actual Omega inputs are level weak. -/
theorem transition_levelWeak_of_isOmega (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((transition n).app X) := by
  let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
  have hp : W ((projection n).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence n X)
  have hp' : W ((projection (n + 1)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence (n + 1) X)
  have hu : W ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X) :=
    PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit_levelWeak n X hX
  have hnat : (transition n).app X ≫ (projection (n + 1)).app X =
      (projection n).app X ≫ (PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X :=
    congr_app (transition_projection n) X
  have hcomp : W ((transition n).app X ≫ (projection (n + 1)).app X) :=
    (congrArg (fun g : (stage n).functor.obj X ⟶
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X => W g) hnat).mpr
        (W.comp_mem _ _ hp hu)
  exact W.of_postcomp _ _ hp' hcomp

/-- Every SAME original finite stage map is level weak on actual original Omega inputs. -/
theorem diagram_map_levelWeak_of_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) {i j : ℕ} (φ : i ⟶ j) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((diagram X).map φ) := by
  let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
  let F := diagram X
  have hStep (n : ℕ) : W (F.map (homOfLE (Nat.le_succ n))) := by
    rw [show F = diagram X from rfl, diagram_map_succ]
    exact transition_levelWeak_of_isOmega n X hX
  have hMaps (j : ℕ) (hij : i ≤ j) : W (F.map (homOfLE hij)) := by
    induction j, hij using Nat.le_induction with
    | base => simpa only [homOfLE_refl, F.map_id] using W.id_mem (F.obj i)
    | succ j hij ih =>
        rw [← homOfLE_comp hij (Nat.le_succ j), F.map_comp]
        exact W.comp_mem _ _ ih (hStep j)
  rw [← homOfLE_leOfHom φ]
  exact hMaps j (leOfHom φ)

/-- Native closed-chain closure proves weakness of every SAME original telescope-unit level. -/
theorem unit_component_weak_of_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (m : ℕ) : CGWH.weakHomotopyEquivalences
      (PointedCGWH.SequentialSpectrum.levelMap (unit.app X) m).right := by
  let F := levelDiagram X m ⋙ pointedToCGWH
  let c := pointedToCGWH.mapCocone (levelCocone X m)
  have hStep (n : ℕ) : CGWH.weakHomotopyEquivalences
      (F.map (homOfLE (Nat.le_succ n))) ∧
      IsClosedEmbedding (ConcreteCategory.hom (F.map (homOfLE (Nat.le_succ n)))) := by
    have hw := (levelWeak_iff_components ((transition n).app X)).mp
      (transition_levelWeak_of_isOmega n X hX) m
    have hc := transition_level_isClosedEmbedding n X m
    change CGWH.weakHomotopyEquivalences
      ((levelDiagram X m).map (homOfLE (Nat.le_succ n))).right ∧
      IsClosedEmbedding (ConcreteCategory.hom
        ((levelDiagram X m).map (homOfLE (Nat.le_succ n))).right)
    rw [levelDiagram_map_succ]
    exact ⟨hw, hc⟩
  exact CGWH.ClosedWeakNatCocone.endpoint_weak c (levelCoconeCGWHIsColimit X m) hStep

/-- The SAME original chosen telescope unit is level weak on every original Omega input. -/
theorem unit_levelWeak_of_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) (hX : X.IsOmega) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (unit.app X) :=
  (levelWeak_iff_components _).mpr (unit_component_weak_of_isOmega X hX)

/-- The SAME original telescope preserves actual original Omega inputs, through original R maps. -/
theorem telescope_isOmega_of_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) : (telescope X).IsOmega := by
  let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
  have ht : W (unit.app X) := unit_levelWeak_of_isOmega X hX
  have hr : W (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X) :=
    (PointedCGWH.SequentialSpectrum.OrderedLoop.unit_levelWeak_iff X).mpr hX
  have hmap : W (PointedCGWH.SequentialSpectrum.OrderedLoop.functor.map (unit.app X)) :=
    PointedCGWH.SequentialSpectrum.OrderedLoop.functor_map_levelWeak _ ht
  have hnat : unit.app X ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X) =
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X ≫
        PointedCGWH.SequentialSpectrum.OrderedLoop.functor.map (unit.app X) :=
    PointedCGWH.SequentialSpectrum.OrderedLoop.unit.naturality (unit.app X)
  have hcomp : W (unit.app X ≫
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X)) :=
    (congrArg (fun g : X ⟶ PointedCGWH.SequentialSpectrum.OrderedLoop.functor.obj (telescope X) =>
      W g) hnat).mpr (W.comp_mem _ _ hr hmap)
  exact (PointedCGWH.SequentialSpectrum.OrderedLoop.unit_levelWeak_iff _).mp
    (W.of_precomp _ _ ht hcomp)

/-- Whole SAME original telescope maps preserve level weakness between actual Omega inputs. -/
theorem telescope_map_levelWeak_of_isOmega
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (hX : X.IsOmega) (hY : Y.IsOmega)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (telescopeFunctor.map f) := by
  let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
  have hx : W (unit.app X) := unit_levelWeak_of_isOmega X hX
  have hy : W (unit.app Y) := unit_levelWeak_of_isOmega Y hY
  have hnat : f ≫ unit.app Y = unit.app X ≫ telescopeFunctor.map f := unit.naturality f
  have hcomp : W (unit.app X ≫ telescopeFunctor.map f) :=
    (congrArg (fun g : X ⟶ telescope Y => W g) hnat).mp (W.comp_mem _ _ hf hy)
  exact W.of_precomp _ _ hx hcomp

end PointedCGWH.SequentialSpectrum.MappingTelescope
