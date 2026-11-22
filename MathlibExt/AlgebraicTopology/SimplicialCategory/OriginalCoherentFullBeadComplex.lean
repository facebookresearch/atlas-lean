/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFullBeadRepresentation
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Types.Epimorphisms

/-!
# The full original bead complex and its actual evaluation

All complete original input beads form a simplicial set under the
original inner coefficient operators. Its evaluation is the same raw
coherent Hom map and is epi for a quasicategory. The original outer
degree descends to components; outer simplex relations remain necessary
for a weak comparison.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.Complex

private theorem coefficient_id (H : SSet.{u}) (q : SimplexCategoryᵒᵖ) (p : H.obj q) :
    H.map (𝟙 q) p = p :=
  ConcreteCategory.congr_hom (H.map_id q) p

private theorem coefficient_comp (H : SSet.{u}) {q r t : SimplexCategoryᵒᵖ}
    (f : q ⟶ r) (g : r ⟶ t) (p : H.obj q) :
    H.map (f ≫ g) p = H.map g (H.map f p) :=
  ConcreteCategory.congr_hom (H.map_comp f g) p

/-- The complete original beads with all original scalar coefficient operators. -/
def object (K : SSet.{u}) (x y : K _⦋0⦌) : SSet.{u} where
  obj q := Bead K x y q
  map f := ↾fun b => b.map f
  map_id q := by
    ext b
    cases b with
    | mk n σ hx hy p =>
      exact congrArg (fun r => (Bead.mk n σ hx hy r : Bead K x y q))
        (coefficient_id ((initial n) ⟶[SSet.{u}] (terminal n)) q p)
  map_comp f g := by
    ext b
    cases b with
    | mk n σ hx hy p =>
      exact congrArg (fun r => (Bead.mk n σ hx hy r : Bead K x y _))
        (coefficient_comp ((initial n) ⟶[SSet.{u}] (terminal n)) f g p)

/-- Evaluation retains the actual original raw Hom map of every complete bead. -/
def evaluation (K : SSet.{u}) (x y : K _⦋0⦌) : object K x y ⟶ hom K x y where
  app q := ↾fun b => b.evaluation
  naturality q r f := by
    ext b
    exact (Bead.evaluation_map f b).symm

/-- Every original bead is read by the same original full insertion. -/
theorem evaluation_app (K : SSet.{u}) (x y : K _⦋0⦌)
    (q : SimplexCategoryᵒᵖ) (b : Bead K x y q) :
    (evaluation K x y).app q b = b.evaluation := rfl

/-- Evaluation is onto every original raw Hom coefficient for a quasicategory. -/
theorem evaluation_surjective (K : SSet.{u}) [SSet.Quasicategory K]
    (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((evaluation K x y).app q) :=
  fun a => original_hom_represented a

/-- The actual original full bead evaluation is epi, at every universe. -/
theorem evaluation_epi (K : SSet.{u}) [SSet.Quasicategory K]
    (x y : K _⦋0⦌) : Epi (evaluation K x y) := by
  apply (NatTrans.epi_iff_epi_app (evaluation K x y)).2
  intro q
  exact (epi_iff_surjective _).2 (evaluation_surjective K x y q)

private theorem edge_dimension {K : SSet.{u}} {x y : K _⦋0⦌}
    {a b : (object K x y) _⦋0⦌} (e : (object K x y).Edge a b) :
    a.dimension = b.dimension := by
  have hs : e.edge.dimension = a.dimension := congrArg Bead.dimension e.src_eq
  have ht : e.edge.dimension = b.dimension := congrArg Bead.dimension e.tgt_eq
  exact hs.symm.trans ht

/-- The same original outer degree descends to components of the full bead complex. -/
def componentDimension (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.π₀ (object K x y) → ℕ :=
  SSet.π₀.lift (fun b => b.dimension)
    (fun {_ _} e => edge_dimension (K := K) (x := x) (y := y) e)

/-- Components retain the exact original outer degree of every full bead. -/
theorem componentDimension_mk (K : SSet.{u}) (x y : K _⦋0⦌)
    (b : (object K x y) _⦋0⦌) :
    componentDimension K x y (SSet.π₀.mk b) = b.dimension := rfl

end CategoryTheory.CoherentRealization.OriginalBead.Complex
