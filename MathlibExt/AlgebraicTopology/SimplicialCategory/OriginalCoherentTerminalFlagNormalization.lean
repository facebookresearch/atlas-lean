/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagCoefficient

/-!
# Original terminal-supported bead normalization

The computed terminal support restricts the same original input simplex.
Its complete coefficient is the native supported-face preimage. Evaluation
agrees through the original outer-operator and endpoint relations.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag

open SimplicialEnrichment

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The same whole original bead coefficient with its literal path-nerve type. -/
def originalCoefficient (b : Bead K x y q) :
    (coefficientObject.{u} b.dimension).obj q := b.coefficient

/-- The selected original ordinal operator starts at the same original source. -/
theorem source_object (b : Bead K x y q) :
    (coherentSimplexMap.{u} (operator b.coefficient)).obj
      (initial.{u} (dimension b.coefficient)) = initial.{u} b.dimension :=
  congrArg SimplicialThickening.mk (lifted_zero b.coefficient)

/-- The selected original ordinal operator ends at the same original target. -/
theorem target_object (b : Bead K x y q) :
    (coherentSimplexMap.{u} (operator b.coefficient)).obj
      (terminal.{u} (dimension b.coefficient)) = terminal.{u} b.dimension :=
  congrArg SimplicialThickening.mk (lifted_last b.coefficient)

/-- The same original bead restricted to all vertices in its actual terminal flag. -/
def normalize (b : Bead K x y q) : Bead K x y q where
  dimension := dimension b.coefficient
  simplex := K.map (operator b.coefficient).op b.simplex
  source_eq := (vertex_operator K (operator b.coefficient) b.simplex
    (initial.{u} (dimension b.coefficient))).trans
      ((congrArg (vertex K b.simplex) (source_object b)).trans b.source_eq)
  target_eq := (vertex_operator K (operator b.coefficient) b.simplex
    (terminal.{u} (dimension b.coefficient))).trans
      ((congrArg (vertex K b.simplex) (target_object b)).trans b.target_eq)
  coefficient := coefficient b.coefficient

/-- The actual normalized terminal flag is the entire selected vertex set. -/
theorem normalize_last_full (b : Bead K x y q) :
    ((originalCoefficient (normalize b)).obj (Fin.last q.unop.len)).I = Set.univ :=
  coefficient_last_full b.coefficient

/-- Every actual normalized flag retains its whole original selected preimage. -/
theorem normalize_flags (b : Bead K x y q) (t : Fin (q.unop.len + 1)) :
    ((originalCoefficient (normalize b)).obj t).I =
      (liftedEmbedding b.coefficient) ⁻¹' ((originalCoefficient b).obj t).I :=
  coefficient_flags b.coefficient t

/-- The complete original coefficient image map retains the original enriched endpoints. -/
theorem imageMap_bead_operator (b : Bead K x y q) :
    imageMap b.coefficient =
      (coherentSimplexMap.{u} (operator b.coefficient)).map
        (initial.{u} (dimension b.coefficient)) (terminal.{u} (dimension b.coefficient)) ≫
      eqToHom (congrArg₂
        (fun i j : coherentSimplex.{u} ⦋b.dimension⦌ => i ⟶[SSet.{u}] j)
        (source_object b) (target_object b)) :=
  imageMap_operator b.coefficient

/-- The original normalized generating map factors through the same complete face map. -/
theorem evaluation_factor (b : Bead K x y q) :
    simplexHom K (normalize b).simplex
      (initial.{u} (dimension b.coefficient)) (terminal.{u} (dimension b.coefficient))
      (normalize b).source_eq (normalize b).target_eq =
    imageMap b.coefficient ≫
      simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension)
        b.source_eq b.target_eq := by
  have ho := simplexHom_operator (operator b.coefficient) b.simplex
    (initial.{u} (dimension b.coefficient)) (terminal.{u} (dimension b.coefficient))
    (normalize b).source_eq (normalize b).target_eq
  have hs := simplexHom_source_transport b.simplex (source_object b) (target_object b)
    ((vertex_operator K (operator b.coefficient) b.simplex
      (initial.{u} (dimension b.coefficient))).symm.trans (normalize b).source_eq)
    ((vertex_operator K (operator b.coefficient) b.simplex
      (terminal.{u} (dimension b.coefficient))).symm.trans (normalize b).target_eq)
    b.source_eq b.target_eq
  exact ho.trans ((congrArg
    (fun g => (coherentSimplexMap.{u} (operator b.coefficient)).map
      (initial.{u} (dimension b.coefficient)) (terminal.{u} (dimension b.coefficient)) ≫ g)
      hs.symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫
        simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension)
          b.source_eq b.target_eq) (imageMap_bead_operator b).symm)))

/-- Terminal-support normalization preserves the same original raw Hom value. -/
theorem evaluation_normalize (b : Bead K x y q) :
    (normalize b).evaluation = b.evaluation := by
  have h := ConcreteCategory.congr_hom (congr_app (evaluation_factor b) q)
    (coefficient b.coefficient)
  change _ =
    (simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension)
      b.source_eq b.target_eq).app q
        ((imageMap b.coefficient).app q (coefficient b.coefficient)) at h
  exact h.trans (congrArg
    ((simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension)
      b.source_eq b.target_eq).app q) (image_coefficient b.coefficient))

/-- Each original full bead has an actual terminal-full bead with the same raw value. -/
theorem exists_terminal_full (b : Bead K x y q) :
    ∃ c : Bead K x y q,
      ((originalCoefficient c).obj (Fin.last q.unop.len)).I = Set.univ ∧
        c.evaluation = b.evaluation :=
  ⟨normalize b, normalize_last_full b, evaluation_normalize b⟩

end CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag
