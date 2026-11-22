/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadNondegenerateEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFullBeadComplex

/-!
# Native nondegenerate uniqueness and all scalar readbacks

The native epi is the unique original epi with its actual simplex
readback. The same whole bead normalization retains every scalar
operator and its exact evaluation map. No weakness of the disjoint
bead complex is asserted.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.Nondegenerate

open TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- The actual original epi is unique for the same canonical native nondegenerate simplex. -/
theorem operator_unique (b : Bead K x y q)
    (g : ⦋b.dimension⦌ ⟶ ⦋(simplex b).dim⦌) [Epi g]
    (hg : K.map g.op (simplex b).simplex = b.simplex) : g = operator b := by
  exact SSet.unique_nonDegenerate_map K b.simplex g
    ⟨(simplex b).simplex, (simplex b).nonDegenerate⟩ hg.symm (operator b)
    ⟨(simplex b).simplex, (simplex b).nonDegenerate⟩ (simplex_factor b).symm

/-- Any actual native nondegenerate epi factor has the same original target dimension. -/
theorem factor_dimension_unique (b : Bead K x y q) {m : ℕ}
    (g : ⦋b.dimension⦌ ⟶ ⦋m⦌) [Epi g] (σ : K.nonDegenerate m)
    (hσ : K.map g.op σ = b.simplex) : m = (simplex b).dim :=
  SSet.unique_nonDegenerate_dim K b.simplex g σ hσ.symm (operator b)
    ⟨(simplex b).simplex, (simplex b).nonDegenerate⟩ (simplex_factor b).symm

private theorem bead_coefficient_congr {K : SSet.{u}} {x y : K _⦋0⦌}
    {q : SimplexCategoryᵒᵖ} (n : ℕ) (σ : K _⦋n⦌)
    (hx : vertex K σ (initial.{u} n) = x) (hy : vertex K σ (terminal.{u} n) = y)
    (p r : (coefficientObject.{u} n).obj q) (h : p = r) :
    (Bead.mk n σ hx hy p : Bead K x y q) = Bead.mk n σ hx hy r := by
  cases h
  rfl

/-- The entire original nondegenerate bead retains every original scalar operator. -/
theorem normalize_inner (b : Bead K x y q) (θ : q ⟶ r) :
    normalize (b.map θ) = (normalize b).map θ :=
  bead_coefficient_congr (simplex b).dim (simplex b).simplex
    (normalize b).source_eq (normalize b).target_eq _ _
      (ConcreteCategory.congr_hom ((coefficientMap b).naturality θ) b.coefficient)

/-- The same whole original nondegenerate normalization on the complete disjoint bead complex. -/
def normalizationMap (K : SSet.{u}) (x y : K _⦋0⦌) :
    Complex.object K x y ⟶ Complex.object K x y where
  app q := ↾fun b => normalize b
  naturality _q _r θ := by
    ext b
    exact normalize_inner b θ

/-- The complete original normalization retains its same original raw evaluation map. -/
theorem normalizationMap_evaluation (K : SSet.{u}) (x y : K _⦋0⦌) :
    normalizationMap K x y ≫ Complex.evaluation K x y = Complex.evaluation K x y := by
  ext q b
  exact evaluation_normalize b

/-- The complete original normalization component is the same native nondegenerate bead. -/
theorem normalizationMap_app (b : Bead K x y q) :
    (normalizationMap K x y).app q b = normalize b := rfl

end CategoryTheory.CoherentRealization.OriginalBead.Nondegenerate
