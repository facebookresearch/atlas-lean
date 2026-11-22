/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadCompositionLaws
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadCoefficientGluing

/-!
# Genuine original two-bead flattenings

A flattening is a whole original input simplex with its two literal
original restrictions. It exists for a quasicategory by the genuine
full-bead inner-anodyne extension theorem. The three endpoint equations
are read from those same original restrictions.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open SimplicialEnrichment
open SSet.OriginalTwoBead.OrdinalCharts

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {s : SimplexCategoryᵒᵖ}

/-- The full original simplex and its two original complete bead restrictions. -/
structure Flattening (b : Bead K x y s) (c : Bead K y z s) where
  /-- The entire original input simplex, retaining the total original ordinal. -/
  simplex : K _⦋b.dimension + c.dimension⦌
  /-- Its literal original full first-bead restriction. -/
  left : K.map (prefixOperator b.dimension c.dimension).op simplex = b.simplex
  /-- Its literal original full second-bead restriction. -/
  right : K.map (suffixOperator b.dimension c.dimension).op simplex = c.simplex

namespace Flattening

variable {b : Bead K x y s} {c : Bead K y z s} (f : Flattening b c)

/-- The first original interval operator retains the total original initial object. -/
theorem prefix_initial :
    (coherentSimplexMap (prefixOperator b.dimension c.dimension)).obj (initial b.dimension) =
      initial (b.dimension + c.dimension) :=
  congrArg SimplicialThickening.mk
    (CoefficientGluing.prefix_first b.dimension c.dimension)

/-- The last object of the first original interval is the original shared pivot. -/
theorem prefix_terminal :
    (coherentSimplexMap (prefixOperator b.dimension c.dimension)).obj (terminal b.dimension) =
      CoefficientGluing.middle b.dimension c.dimension :=
  congrArg SimplicialThickening.mk
    (CoefficientGluing.prefix_final b.dimension c.dimension)

/-- The first object of the second original interval is the same original pivot. -/
theorem suffix_initial :
    (coherentSimplexMap (suffixOperator b.dimension c.dimension)).obj (initial c.dimension) =
      CoefficientGluing.middle b.dimension c.dimension :=
  congrArg SimplicialThickening.mk
    (CoefficientGluing.suffix_first b.dimension c.dimension)

/-- The last object of the second original interval retains the total original last object. -/
theorem suffix_terminal :
    (coherentSimplexMap (suffixOperator b.dimension c.dimension)).obj (terminal c.dimension) =
      terminal (b.dimension + c.dimension) :=
  congrArg SimplicialThickening.mk
    (CoefficientGluing.suffix_final b.dimension c.dimension)

/-- The full flattening retains the original source vertex. -/
theorem source_eq :
    vertex K f.simplex (initial (b.dimension + c.dimension)) = x :=
  (congrArg (vertex K f.simplex) (prefix_initial (b := b) (c := c)).symm).trans
    ((vertex_operator K (prefixOperator b.dimension c.dimension) f.simplex
      (initial b.dimension)).symm.trans
        ((congrArg (fun σ => vertex K σ (initial b.dimension)) f.left).trans b.source_eq))

/-- The full flattening retains the original shared intermediate vertex. -/
theorem middle_eq :
    vertex K f.simplex (CoefficientGluing.middle b.dimension c.dimension) = y :=
  (congrArg (vertex K f.simplex) (prefix_terminal (b := b) (c := c)).symm).trans
    ((vertex_operator K (prefixOperator b.dimension c.dimension) f.simplex
      (terminal b.dimension)).symm.trans
        ((congrArg (fun σ => vertex K σ (terminal b.dimension)) f.left).trans b.target_eq))

/-- The full flattening retains the original target vertex. -/
theorem target_eq :
    vertex K f.simplex (terminal (b.dimension + c.dimension)) = z :=
  (congrArg (vertex K f.simplex) (suffix_terminal (b := b) (c := c)).symm).trans
    ((vertex_operator K (suffixOperator b.dimension c.dimension) f.simplex
      (terminal c.dimension)).symm.trans
        ((congrArg (fun σ => vertex K σ (terminal c.dimension)) f.right).trans c.target_eq))

/-- The actual full flattened bead uses the entire original coefficient union. -/
def bead : Bead K x z s :=
  ⟨b.dimension + c.dimension, f.simplex, f.source_eq, f.target_eq,
    (CoefficientGluing.map b.dimension c.dimension).app s (b.coefficient, c.coefficient)⟩

end Flattening

/-- Both full original beads have a genuine original simplex flattening in a quasicategory. -/
theorem exists_flattening [SSet.Quasicategory K]
    (b : Bead K x y s) (c : Bead K y z s) : Nonempty (Flattening b c) := by
  have h : lastVertex b.dimension ≫ SSet.yonedaEquiv.symm b.simplex =
      firstVertex c.dimension ≫ SSet.yonedaEquiv.symm c.simplex :=
    b.last_map.trans c.first_map.symm
  obtain ⟨τ, hl, hr⟩ := exists_standard_extension b.dimension c.dimension
    (SSet.yonedaEquiv.symm b.simplex) (SSet.yonedaEquiv.symm c.simplex) h
  refine ⟨⟨SSet.yonedaEquiv τ, ?_, ?_⟩⟩
  · exact (SSet.yonedaEquiv_naturality (prefixOperator b.dimension c.dimension) τ).trans
      ((congrArg SSet.yonedaEquiv hl).trans (Equiv.apply_symm_apply _ _))
  · exact (SSet.yonedaEquiv_naturality (suffixOperator b.dimension c.dimension) τ).trans
      ((congrArg SSet.yonedaEquiv hr).trans (Equiv.apply_symm_apply _ _))

end CategoryTheory.CoherentRealization.OriginalBead
