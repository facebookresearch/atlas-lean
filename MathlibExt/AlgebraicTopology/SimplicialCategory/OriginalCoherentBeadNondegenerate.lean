/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentEpiBeadOperators
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

/-!
# The native nondegenerate simplex of an original coherent bead

The same original supplied simplex has the native unique nondegenerate
factor and epimorphism. Its complete original coefficient is pushed
through that same original epimorphism; both actual endpoints are kept.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.Nondegenerate

open SimplicialEnrichment
open TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The entire same original coefficient with its literal path-nerve type. -/
def originalCoefficient (b : Bead K x y q) :
    (coefficientObject.{u} b.dimension).obj q := b.coefficient

/-- The same original supplied input simplex with its actual native dimension. -/
def originalSimplex (b : Bead K x y q) : K.S := SSet.S.mk b.simplex

/-- The native unique nondegenerate input simplex of the same original bead. -/
def simplex (b : Bead K x y q) : K.N := (originalSimplex b).toN

/-- The same native original epi factor of the whole supplied input simplex. -/
def operator (b : Bead K x y q) : ⦋b.dimension⦌ ⟶ ⦋(simplex b).dim⦌ :=
  (originalSimplex b).toNπ

/-- The actual original factor is a native epimorphism. -/
instance (b : Bead K x y q) : Epi (operator b) :=
  inferInstanceAs (Epi (originalSimplex b).toNπ)

/-- The entire same original simplex has its exact native epi readback. -/
theorem simplex_factor (b : Bead K x y q) :
    K.map (operator b).op (simplex b).simplex = b.simplex :=
  SSet.S.map_toNπ_op_apply (originalSimplex b)

/-- The same actual original nondegenerate source object. -/
theorem source_object (b : Bead K x y q) :
    (coherentSimplexMap.{u} (operator b)).obj (initial.{u} b.dimension) =
      initial.{u} (simplex b).dim :=
  congrArg SimplicialThickening.mk
    (OuterOperator.lifted_zero (operator b) (OuterOperator.zero_of_epi (operator b)))

/-- The same actual original nondegenerate target object. -/
theorem target_object (b : Bead K x y q) :
    (coherentSimplexMap.{u} (operator b)).obj (terminal.{u} b.dimension) =
      terminal.{u} (simplex b).dim :=
  congrArg SimplicialThickening.mk
    (OuterOperator.lifted_last (operator b) (OuterOperator.last_of_epi (operator b)))

/-- The whole same original coefficient image map under the native epi. -/
def coefficientMap (b : Bead K x y q) :
    coefficientObject.{u} b.dimension ⟶ coefficientObject.{u} (simplex b).dim :=
  OuterOperator.map (operator b) (OuterOperator.zero_of_epi (operator b))
    (OuterOperator.last_of_epi (operator b))

/-- The actual original nondegenerate bead, with its complete original coefficient image. -/
def normalize (b : Bead K x y q) : Bead K x y q where
  dimension := (simplex b).dim
  simplex := (simplex b).simplex
  source_eq :=
    ((congrArg (vertex K (simplex b).simplex) (source_object b)).symm.trans
      ((vertex_operator K (operator b) (simplex b).simplex (initial.{u} b.dimension)).symm.trans
        (congrArg (fun σ => vertex K σ (initial.{u} b.dimension)) (simplex_factor b)))).trans
      b.source_eq
  target_eq :=
    ((congrArg (vertex K (simplex b).simplex) (target_object b)).symm.trans
      ((vertex_operator K (operator b) (simplex b).simplex (terminal.{u} b.dimension)).symm.trans
        (congrArg (fun σ => vertex K σ (terminal.{u} b.dimension)) (simplex_factor b)))).trans
      b.target_eq
  coefficient := (coefficientMap b).app q b.coefficient

/-- The resulting entire original input simplex is genuinely nondegenerate. -/
theorem normalize_nondegenerate (b : Bead K x y q) :
    (normalize b).simplex ∈ K.nonDegenerate (normalize b).dimension :=
  (simplex b).nonDegenerate

/-- Every whole original coefficient flag retains its same native epi image. -/
theorem normalize_flags (b : Bead K x y q) (t : Fin (q.unop.len + 1)) :
    (((coefficientMap b).app q b.coefficient).obj t).I =
      (operator b).toOrderHom.uliftMap '' ((originalCoefficient b).obj t).I :=
  OuterOperator.map_flags (operator b) (OuterOperator.zero_of_epi (operator b))
    (OuterOperator.last_of_epi (operator b)) b.coefficient t

/-- The actual original nondegenerate factor does not increase the native input dimension. -/
theorem normalize_dimension_le (b : Bead K x y q) :
    (normalize b).dimension ≤ b.dimension :=
  SSet.S.dim_toN_le (originalSimplex b)

end CategoryTheory.CoherentRealization.OriginalBead.Nondegenerate
