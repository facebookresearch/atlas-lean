/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence

/-!
# Bicomplex naturality of the bottom-relative-to-total comparison

The bottom-relative homology comparison at the finite upper abutment stage
is natural with respect to bicomplex maps.  The proof combines naturality at
that complete-filtration stage with compatibility of stage maps and the map
of total complexes.

This file does not pass to image quotients or stable associated-graded terms.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The bottom-relative-to-total comparison is natural under bicomplex
morphisms. -/
theorem horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (p + q) := by
  have hstage :=
    horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
      f (horizontalAbutmentUpperIndex p q) (p + q)
  have hbottom :
      horizontalBottomToStageMap
          (horizontalAbutmentUpperIndex p q) =
        horizontalCanonicalAbutmentTotalMap p q :=
    Subsingleton.elim _ _
  rw [hbottom] at hstage
  push_cast at hstage
  have htotal := congrArg
    (fun k => HomologicalComplex.homologyMap k (p + q))
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal
      f (horizontalAbutmentUpperIndex p q))
  simp only [HomologicalComplex.homologyMap_comp] at htotal
  dsimp [horizontalBottomRelativeHomologyToTotalIso,
    horizontalAbutmentUpperHomologyToTotalIso]
  rw [horizontalCompleteHomologyToTotal_eq L (p + q)
      (horizontalAbutmentUpperIndex p q),
    horizontalCompleteHomologyToTotal_eq K (p + q)
      (horizontalAbutmentUpperIndex p q)]
  rw [reassoc_of% hstage, htotal]
  simp only [Category.assoc]

end HomologicalComplex₂

end
