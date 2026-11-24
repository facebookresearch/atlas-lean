/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLiftingIsofibration

/-!
# Public clients for the strict isofibration comparison

The forward client retains the chosen source, target-vertex equality and
equality of the actual typed image edge. The reverse client retains the native
ordinary object equality and its exact transported isomorphism equation.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.EquivalenceLiftingIsofibrationTest

/-- Ordinary isofibrancy gives the actual prescribed base edge, with the
lifted target vertex equality retained. -/
theorem exists_strict_edge_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.InnerFibration p] [SSet.Quasicategory Y]
    (hF : (SSet.hoFunctor.map p).toFunctor.IsIsofibration)
    {x₀ : X _⦋0⦌} {y₁ : Y _⦋0⦌}
    (g : SSet.Edge (p.app (op ⦋0⦌) x₀) y₁) (hg : g.IsEquivalence) :
    ∃ (x₁ : X _⦋0⦌) (hx₁ : p.app (op ⦋0⦌) x₁ = y₁) (f : SSet.Edge x₀ x₁),
      f.IsEquivalence ∧ (f.map p).ofEq rfl hx₁ = g := by
  obtain ⟨x₁, hx₁, f, hf, hmap⟩ := (SSet.hasStrictEquivalenceLifting_iff p).mp
    ((SSet.isIsofibration_hoFunctor_map_iff_hasStrictEquivalenceLifting p).mp hF) g hg
  exact ⟨x₁, hx₁, f, hf, SSet.Edge.ext hmap⟩

/-- Strict equivalence-edge lifting gives the native ordinary lift for
arbitrary homotopy-category objects and retains both exact equations. -/
theorem exists_iso_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.InnerFibration p] [SSet.Quasicategory Y]
    (hStrict : SSet.HasStrictEquivalenceLifting p)
    {a₀ : X.HomotopyCategory} {a₁ : Y.HomotopyCategory}
    (g : (SSet.hoFunctor.map p).toFunctor.obj a₀ ≅ a₁) :
    ∃ (b : X.HomotopyCategory) (f : a₀ ≅ b)
      (hobj : (SSet.hoFunctor.map p).toFunctor.obj b = a₁),
      (SSet.hoFunctor.map p).toFunctor.mapIso f ≪≫ eqToIso hobj = g := by
  have := (SSet.isIsofibration_hoFunctor_map_iff_hasStrictEquivalenceLifting p).mpr hStrict
  exact (SSet.hoFunctor.map p).toFunctor.exists_iso_lift g

end MathlibExtTest.AlgebraicTopology.Quasicategory.EquivalenceLiftingIsofibrationTest
