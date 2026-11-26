/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentUnit

/-!
# Full coherent beads

Each bead retains its input simplex, both 
endpoint equations, and its scalar coherent Hom coefficient.
The evaluation is the same generator in coherent realization.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open SimplicialEnrichment SimplicialQuiver

/-- The initial coherent object of a standard bead. -/
def initial (n : ℕ) : coherentSimplex.{u} ⦋n⦌ :=
  SimplicialThickening.mk (ULift.up (0 : Fin (n + 1)))

/-- The terminal coherent object of a standard bead. -/
def terminal (n : ℕ) : coherentSimplex.{u} ⦋n⦌ :=
  SimplicialThickening.mk (ULift.up (Fin.last n))

/-- A complete bead and its scalar coefficient. -/
structure Bead (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) where
  /-- Input dimension. -/
  dimension : ℕ
  /-- The input simplex. -/
  simplex : K _⦋dimension⦌
  /-- The source equation. -/
  source_eq : vertex K simplex (initial dimension) = x
  /-- The target equation. -/
  target_eq : vertex K simplex (terminal dimension) = y
  /-- The coherent Hom coefficient. -/
  coefficient : ((initial dimension) ⟶[SSet.{u}] (terminal dimension)).obj q

namespace Bead

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- The full bead is a coherent generator. -/
def toArrow (b : Bead K x y q) : Arrow K x y q :=
  ⟨⦋b.dimension⦌, b.simplex, initial b.dimension, terminal b.dimension,
    b.source_eq, b.target_eq, b.coefficient⟩

/-- The same generating Hom simplex in the realization. -/
def evaluation (b : Bead K x y q) : (hom K x y).obj q :=
  (simplexHom K b.simplex (initial b.dimension) (terminal b.dimension)
    b.source_eq b.target_eq).app q b.coefficient

/-- Every scalar operator acts on the coefficient. -/
def map (f : q ⟶ r) (b : Bead K x y q) : Bead K x y r :=
  ⟨b.dimension, b.simplex, b.source_eq, b.target_eq,
    ((initial b.dimension) ⟶[SSet.{u}] (terminal b.dimension)).map f b.coefficient⟩

/-- Scalar operators retain the generator. -/
theorem toArrow_map (f : q ⟶ r) (b : Bead K x y q) :
    (b.map f).toArrow = b.toArrow.map f := rfl

/-- Evaluation follows every scalar operator. -/
theorem evaluation_map (f : q ⟶ r) (b : Bead K x y q) :
    (hom K x y).map f b.evaluation = (b.map f).evaluation :=
  ConcreteCategory.congr_hom
    ((simplexHom K b.simplex (initial b.dimension) (terminal b.dimension)
      b.source_eq b.target_eq).naturality f).symm b.coefficient

end Bead

/-- The outer-operator equation at the same endpoint labels. -/
theorem simplexHom_operator {K : SSet.{u}} {n m : SimplexCategory}
    (f : n ⟶ m) (σ : K.obj (op m)) (i j : coherentSimplex.{u} n)
    {x y : K _⦋0⦌} (hx : vertex K (K.map f.op σ) i = x)
    (hy : vertex K (K.map f.op σ) j = y) :
    simplexHom K (K.map f.op σ) i j hx hy =
      (coherentSimplexMap f).map i j ≫
        simplexHom K σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j)
          ((vertex_operator K f σ i).symm.trans hx)
          ((vertex_operator K f σ j).symm.trans hy) := by
  ext q a
  exact _root_.Quotient.sound
    (Closure.relation (Equations.operator q f σ i j hx hy a))

/-- The source-object equalities transport the same full generator map. -/
theorem simplexHom_source_transport {K : SSet.{u}} {n : SimplexCategory}
    (σ : K.obj (op n)) {i j i' j' : coherentSimplex.{u} n}
    (hi : i = i') (hj : j = j') {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y)
    (hx' : vertex K σ i' = x) (hy' : vertex K σ j' = y) :
    eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} n => a ⟶[SSet.{u}] b) hi hj) ≫
      simplexHom K σ i' j' hx' hy' = simplexHom K σ i j hx hy := by
  cases hi
  cases hj
  exact Category.id_comp _

end CategoryTheory.CoherentRealization.OriginalBead
