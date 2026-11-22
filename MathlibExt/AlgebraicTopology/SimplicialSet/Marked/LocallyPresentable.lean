/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.StrongGenerator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellSourcePresentability
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# Original-universe local presentability of marked simplicial sets

The actual minimally marked simplices and the fully marked interval form
a small strong generator. Each is presentable at the original regular
cell-source rank: minimal markings preserve presheaf presentability, and
the interval has only finitely many original marked edges. The native
strong-generator theorem therefore proves local presentability of the
whole marked carrier, rather than merely smallness of the generator labels.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

local instance : Fact CellSmallness.cardinal.{u}.IsRegular := CellSmallness.cardinal_regular

/-- Marking every original interval edge is the same marked object up to the identity map. -/
def fullyMarkedIntervalIso :
    withEdges (Δ[1] : SSet.{u}) Set.univ ≅ max (Δ[1] : SSet.{u}) :=
  isoMk (Iso.refl _) (fun _ => ⟨fun _ => Set.mem_univ _, fun h => Or.inr h⟩)

/-- All original degree-one interval simplices form a finite set, at every value universe. -/
theorem interval_edges_finite : (Set.univ : Set ((Δ[1] : SSet.{u}) _⦋1⦌)).Finite := by
  have h : Set.range (SSet.stdSimplex.objMk₁.{u} (n := 1)) = Set.univ :=
    Set.range_eq_univ.mpr SSet.stdSimplex.objMk₁_surjective
  rw [← h]
  exact Set.finite_range _

/-- The original fully marked interval is genuinely presentable at the native source rank. -/
theorem max_interval_isCardinalPresentable :
    IsCardinalPresentable (max (Δ[1] : SSet.{u})) CellSmallness.cardinal.{u} := by
  let _ : Fact CellSmallness.cardinal.{u}.IsRegular := CellSmallness.cardinal_regular
  let _ : IsCardinalPresentable (Δ[1] : SSet.{u}) CellSmallness.cardinal.{u} :=
    CellSmallness.finite_source_presentable _
  let _ : IsCardinalPresentable (withEdges (Δ[1] : SSet.{u}) Set.univ)
      CellSmallness.cardinal.{u} :=
    withEdges_isCardinalPresentable _ _ interval_edges_finite _
  exact isCardinalPresentable_of_iso fullyMarkedIntervalIso _

/-- Every actual object of the small strong generator has this original-universe presentability rank. -/
theorem strongGenerator_presentable :
    strongGenerator.{u} ≤ isCardinalPresentable Marked.{u} CellSmallness.cardinal.{u} := by
  let _ : Fact CellSmallness.cardinal.{u}.IsRegular := CellSmallness.cardinal_regular
  intro X hX
  change ObjectProperty.ofObj strongGeneratorObj X at hX
  rcases hX with ⟨i⟩
  cases i with
  | none => exact max_interval_isCardinalPresentable
  | some n =>
      change IsCardinalPresentable (min (Δ[n] : SSet.{u})) CellSmallness.cardinal.{u}
      let _ : IsCardinalPresentable (Δ[n] : SSet.{u}) CellSmallness.cardinal.{u} :=
        CellSmallness.finite_source_presentable _
      exact min_isCardinalPresentable _ _

/-- The whole original marked carrier is locally presentable at the proven regular source rank. -/
theorem isCardinalLocallyPresentable :
    IsCardinalLocallyPresentable Marked.{u} CellSmallness.cardinal.{u} := by
  let _ : Fact CellSmallness.cardinal.{u}.IsRegular := CellSmallness.cardinal_regular
  let _ : ObjectProperty.Small.{u} strongGenerator.{u} := strongGenerator_small
  exact (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator _ _).mpr
    ⟨strongGenerator, inferInstance, strongGenerator_isStrongGenerator, strongGenerator_presentable⟩

/-- Native marked simplicial sets are locally presentable without raising the working universe. -/
theorem isLocallyPresentable : IsLocallyPresentable.{u} Marked.{u} where
  exists_cardinal := ⟨CellSmallness.cardinal, CellSmallness.cardinal_regular,
    isCardinalLocallyPresentable⟩

end SSet.Marked
