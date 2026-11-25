/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedComparison

/-!
# Positive total-homology filtration step comparisons

For a positive filtration index, the complete-filtration step intertwines
the complete-to-finite comparisons at its predecessor and current index.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The positive complete-filtration step followed by the upper comparison
is the lower comparison followed by the corresponding finite step. -/
theorem horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)).hom.app p =
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (p + q) p hp).hom ≫
        (horizontalFiniteTotalHomologyFiltration K (p + q)).diagram.map
          (homOfLE (Nat.sub_le p 1)) := by
  let a : (p - 1 : ℕ) ⟶ p := homOfLE (Nat.sub_le p 1)
  have htransport :
      horizontalTotalHomologyFiltrationStepMap K p q =
        eqToHom (congrArg
          (fun i : EInt =>
            (horizontalTotalHomologyFiltration K (p + q)).obj i)
          (horizontalTotalHomologyPrevNatIndexEq p hp)) ≫
          (horizontalTotalHomologyFiltration K (p + q)).diagram.map
            (horizontalFiltrationNatToEIntFunctor.map a) := by
    change
      (horizontalTotalHomologyFiltration K (p + q)).diagram.map
          (homOfLE (horizontalTotalHomologyPrevIndex_le p)) = _
    rw [← eqToHom_map
        (horizontalTotalHomologyFiltration K (p + q)).diagram
        (horizontalTotalHomologyPrevNatIndexEq p hp),
      ← Functor.map_comp]
    apply (horizontalTotalHomologyFiltration K (p + q)).diagram.congr_map
    apply Subsingleton.elim
  have hnat :
      (horizontalTotalHomologyFiltration K (p + q)).diagram.map
            (horizontalFiltrationNatToEIntFunctor.map a) ≫
          (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
            (p + q)).hom.app p =
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
            (p + q)).hom.app (p - 1) ≫
          (horizontalFiniteTotalHomologyFiltration K
            (p + q)).diagram.map a := by
    simpa only [Functor.comp_map] using
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
        (p + q)).hom.naturality a
  calc
    horizontalTotalHomologyFiltrationStepMap K p q ≫
          (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
            (p + q)).hom.app p =
        (eqToHom (congrArg
            (fun i : EInt =>
              (horizontalTotalHomologyFiltration K (p + q)).obj i)
            (horizontalTotalHomologyPrevNatIndexEq p hp)) ≫
          (horizontalTotalHomologyFiltration K (p + q)).diagram.map
            (horizontalFiltrationNatToEIntFunctor.map a)) ≫
          (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
            (p + q)).hom.app p := by rw [htransport]
    _ = eqToHom (congrArg
            (fun i : EInt =>
              (horizontalTotalHomologyFiltration K (p + q)).obj i)
            (horizontalTotalHomologyPrevNatIndexEq p hp)) ≫
          ((horizontalTotalHomologyFiltration K (p + q)).diagram.map
              (horizontalFiltrationNatToEIntFunctor.map a) ≫
            (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
              (p + q)).hom.app p) :=
      Category.assoc _ _ _
    _ = eqToHom (congrArg
            (fun i : EInt =>
              (horizontalTotalHomologyFiltration K (p + q)).obj i)
            (horizontalTotalHomologyPrevNatIndexEq p hp)) ≫
          ((horizontalCompleteFiniteHomologyFiltrationDiagramIso K
              (p + q)).hom.app (p - 1) ≫
            (horizontalFiniteTotalHomologyFiltration K
              (p + q)).diagram.map a) := by rw [hnat]
    _ = (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
            K (p + q) p hp).hom ≫
          (horizontalFiniteTotalHomologyFiltration K
            (p + q)).diagram.map a := by
      rw [horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_hom]
      exact (Category.assoc _ _ _).symm
    _ = _ := by rfl

/-- Inverse orientation of the positive step comparison. -/
theorem horizontalFiniteTotalHomologyFiltrationStepMap_comp_positiveComparison_inv
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    (horizontalFiniteTotalHomologyFiltration K (p + q)).diagram.map
          (homOfLE (Nat.sub_le p 1)) ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).inv.app p =
        (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (p + q) p hp).inv ≫
        horizontalTotalHomologyFiltrationStepMap K p q := by
  let ePrev := horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
    K (p + q) p hp
  let eCurr :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)).app p
  change _ ≫ eCurr.inv = ePrev.inv ≫ _
  symm
  rw [ePrev.inv_comp_eq]
  rw [← Category.assoc, eCurr.eq_comp_inv]
  exact horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
    K p q hp

end HomologicalComplex₂

end
