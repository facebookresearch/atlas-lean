/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadNondegenerate

/-!
# The same original nondegenerate bead evaluation

The native epi factor evaluates through the original whole outer
operator relation. The same normalized bead has precisely the original
raw Hom value, with every coefficient flag and endpoint retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.Nondegenerate

open SimplicialEnrichment
open TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

private theorem simplexHom_eq_of_simplex_eq {n : SimplexCategory}
    (σ τ : K.obj (op n)) (h : σ = τ) (i j : coherentSimplex.{u} n)
    (hx : vertex K σ i = x) (hy : vertex K σ j = y)
    (hx' : vertex K τ i = x) (hy' : vertex K τ j = y) :
    simplexHom K σ i j hx hy = simplexHom K τ i j hx' hy' := by
  cases h
  rfl

/-- The same complete native coefficient map is the original enriched operator with its endpoint equations. -/
theorem coefficientMap_coherent (b : Bead K x y q) :
    coefficientMap b =
      (coherentSimplexMap.{u} (operator b)).map (initial.{u} b.dimension) (terminal.{u} b.dimension) ≫
      eqToHom (congrArg₂
        (fun i j : coherentSimplex.{u} ⦋(simplex b).dim⦌ => i ⟶[SSet.{u}] j)
        (source_object b) (target_object b)) :=
  OuterOperator.map_coherent (operator b) (OuterOperator.zero_of_epi (operator b))
    (OuterOperator.last_of_epi (operator b))

/-- The entire original generator factors through the same native nondegenerate simplex and coefficient map. -/
theorem evaluation_factor (b : Bead K x y q) :
    simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension)
      b.source_eq b.target_eq =
      coefficientMap b ≫
        simplexHom K (normalize b).simplex
          (initial.{u} (normalize b).dimension) (terminal.{u} (normalize b).dimension)
          (normalize b).source_eq (normalize b).target_eq := by
  let hx : vertex K (K.map (operator b).op (simplex b).simplex)
      (initial.{u} b.dimension) = x :=
    (congrArg (fun σ => vertex K σ (initial.{u} b.dimension)) (simplex_factor b)).trans
      b.source_eq
  let hy : vertex K (K.map (operator b).op (simplex b).simplex)
      (terminal.{u} b.dimension) = y :=
    (congrArg (fun σ => vertex K σ (terminal.{u} b.dimension)) (simplex_factor b)).trans
      b.target_eq
  have hσ := simplexHom_eq_of_simplex_eq b.simplex
    (K.map (operator b).op (simplex b).simplex) (simplex_factor b).symm
    (initial.{u} b.dimension) (terminal.{u} b.dimension) b.source_eq b.target_eq hx hy
  have ho := simplexHom_operator (operator b) (simplex b).simplex
    (initial.{u} b.dimension) (terminal.{u} b.dimension) hx hy
  have hs := simplexHom_source_transport (simplex b).simplex (source_object b) (target_object b)
    ((vertex_operator K (operator b) (simplex b).simplex (initial.{u} b.dimension)).symm.trans hx)
    ((vertex_operator K (operator b) (simplex b).simplex (terminal.{u} b.dimension)).symm.trans hy)
    (normalize b).source_eq (normalize b).target_eq
  exact hσ.trans (ho.trans ((congrArg
    (fun g => (coherentSimplexMap.{u} (operator b)).map
      (initial.{u} b.dimension) (terminal.{u} b.dimension) ≫ g) hs.symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫
        simplexHom K (normalize b).simplex (initial.{u} (normalize b).dimension)
          (terminal.{u} (normalize b).dimension) (normalize b).source_eq (normalize b).target_eq)
        (coefficientMap_coherent b).symm))))

/-- The same original nondegenerate bead retains the exact original raw Hom value. -/
theorem evaluation_normalize (b : Bead K x y q) :
    (normalize b).evaluation = b.evaluation :=
  (ConcreteCategory.congr_hom (congr_app (evaluation_factor b) q) b.coefficient).symm

/-- The entire normalized original coefficient with its literal native path-nerve type. -/
def normalizedCoefficient (b : Bead K x y q) :
    (coefficientObject.{u} (normalize b).dimension).obj q :=
  (coefficientMap b).app q b.coefficient

/-- A full original terminal flag remains full through the same actual native epi. -/
theorem normalize_last_full (b : Bead K x y q)
    (h : ((originalCoefficient b).obj (Fin.last q.unop.len)).I = Set.univ) :
    ((normalizedCoefficient b).obj (Fin.last q.unop.len)).I = Set.univ :=
  OuterOperator.map_last_full (operator b) (originalCoefficient b) h

/-- An endpoint-only original first flag remains exactly the two original endpoint images. -/
theorem normalize_first_endpoints (b : Bead K x y q)
    (h : ((originalCoefficient b).obj 0).I =
      {ULift.up.{u} (0 : Fin (b.dimension + 1)), ULift.up.{u} (Fin.last b.dimension)}) :
    ((normalizedCoefficient b).obj 0).I =
      {ULift.up.{u} (0 : Fin ((normalize b).dimension + 1)),
        ULift.up.{u} (Fin.last (normalize b).dimension)} :=
  OuterOperator.map_first_endpoints (operator b) (originalCoefficient b) h

end CategoryTheory.CoherentRealization.OriginalBead.Nondegenerate
