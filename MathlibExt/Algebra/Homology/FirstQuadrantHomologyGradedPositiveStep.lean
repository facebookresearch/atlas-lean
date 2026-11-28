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
# Comparing positive consecutive homology-filtration steps

Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), p>0, and n=p+q. Let
e_prev compare the complete stage at (p:ℤ)−1 with finite stage p−1, and e_p compare the
complete and finite stages at p.

For the consecutive inclusions s_complete and s_finite, one has s_complete ≫ e_p.hom =
e_prev.hom ≫ s_finite. The inverse-oriented equality is s_finite ≫ e_p.inv = e_prev.inv ≫
s_complete.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), p,q ∈ ℕ, and hp : 0 < p.
In degree n=p+q, let s_c : F_{(p:ℤ)−1}^complete → F_p^complete and s_f : F_{p−1}^finite →
F_p^finite be the consecutive inclusions. Let e_prev and e_p be the predecessor and current
complete-to-finite stage isomorphisms. Then s_c ≫ e_p.hom = e_prev.hom ≫ s_f. The finite arrow
s_f is the diagram map of the inequality p−1 ≤ p in ℕ. -/
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

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), p,q ∈ ℕ, and hp : 0 < p.
In total degree p+q, let s_f be the finite image-filtration inclusion at natural indices p−1 ≤
p, s_c the complete inclusion at integer indices p−1 ≤ p, and e_prev,e_p the
complete-to-finite stage isomorphisms. Then s_f ≫ e_p.inv = e_prev.inv ≫ s_c. This specifies
the orientation from the finite predecessor stage to the complete current stage. -/
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
