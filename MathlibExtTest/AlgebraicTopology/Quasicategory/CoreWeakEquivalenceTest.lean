/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.Quasicategory.CoreWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Core Weak Equivalence Test
-/

set_option autoImplicit false

universe u

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- The core weak-preservation result supplies a weak equivalence in the
actual native Kan model. -/
example {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : categoricalEquivalences f) :
    WeakEquivalence (core.map f) := by
  have hc := core_map_mem_W_of_categoricalEquivalence hf
  let _ : KanComplex (core X : SSet.{u}) := hc.kanComplex_source
  let _ : KanComplex (core Y : SSet.{u}) := hc.kanComplex_target
  rw [weakEquivalence_iff]
  change realizationWeakEquivalences (core.map f)
  exact (KanComplex.W_iff_realizationWeakEquivalence (core.map f)).mp hc

/-- Structural weak preservation includes equivalence of fundamental groupoids. -/
example {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : categoricalEquivalences f) :
    (mapFundamentalGroupoid (core.map f)).IsEquivalence :=
  (core_map_mem_W_of_categoricalEquivalence hf).isEquivalence_mapFundamentalGroupoid

/-- Every pointed homotopy-group map is bijective. -/
example {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : categoricalEquivalences f)
    (n : ℕ) (x : (core X : SSet.{u}) _⦋0⦌) :
    Function.Bijective (KanComplex.π.map (core.map f) rfl (n := n) (x := x)) :=
  (core_map_mem_W_of_categoricalEquivalence hf).bijective_piMap n x

end SSet
