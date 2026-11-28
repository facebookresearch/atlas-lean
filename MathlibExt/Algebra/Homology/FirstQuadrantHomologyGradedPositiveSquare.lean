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

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPositiveStep

/-!
# The positive-column homology-filtration square

Let C be an abelian category, f : K → L a first-quadrant bicomplex map, and n=p+q. The current
complete image-stage map at p is the finite image-stage map conjugated by the
complete-to-finite comparisons. For p>0 the same construction at the natural predecessor p−1
gives the preceding complete-stage map.

These two maps commute with the consecutive complete-filtration inclusion F_{p−1}H_n(Tot) →
F_pH_n(Tot). The current map itself is defined for all p ∈ ℕ.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), p,q ∈ ℕ, and
hp : 0 < p. Put n=p+q, and let e_K and e_L identify the complete image stages at (p:ℤ)−1 with
the finite stages at p−1. If b(f) is the finite predecessor-stage map induced by f, define the
complete predecessor map to be e_K.hom ≫ b(f) ≫ e_L.inv. Its source and target are
F_{(p:ℤ)−1}H_n(Tot(K)) and F_{(p:ℤ)−1}H_n(Tot(L)). -/
noncomputable def horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) :=
  (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
      K (p + q) p hp).hom ≫
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor (p + q)).map f).natTrans.app
      (p - 1) ≫
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
      L (p + q) p hp).inv

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Put n=p+q, and let e_K,p and e_L,p be the complete-to-finite image comparisons at column p.
The current complete-stage map F_pH_n(Tot(K)) → F_pH_n(Tot(L)) is e_K,p.hom ≫ b_p(f) ≫
e_L,p.inv, where b_p(f) is the finite filtered-homology map at p. This definition requires no
inequality p>0. -/
noncomputable def horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (p + q)).obj
        (((p : ℤ) : EInt)) :=
  (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
      (p + q)).hom.app p ≫
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor (p + q)).map f).natTrans.app p ≫
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso L
      (p + q)).inv.app p

@[simp]
theorem horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp =
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (p + q) p hp).hom ≫
        ((horizontalFiniteTotalHomologyFilteredObjectFunctor
          (p + q)).map f).natTrans.app (p - 1) ≫
        (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          L (p + q) p hp).inv :=
  rfl

@[simp]
theorem horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq
    (f : K ⟶ L) (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        ((horizontalFiniteTotalHomologyFilteredObjectFunctor
          (p + q)).map f).natTrans.app p ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso L
          (p + q)).inv.app p :=
  rfl

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), p,q ∈ ℕ, and
hp : 0 < p. In total degree n=p+q, let s_K and s_L be the complete-stage inclusions F_{p−1} →
F_p. Let a(f) and c(f) be the predecessor and current maps obtained from the finite image
filtration through the complete-to-finite comparisons. Then s_K ≫ c(f) = a(f) ≫ s_L. The
predecessor comparison uses hp to identify its integer and natural indices. -/
theorem horizontalTotalHomologyFiltrationStepMap_naturality_of_pos
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalTotalHomologyFiltrationStepMap L p q := by
  let a : (p - 1 : ℕ) ⟶ p := homOfLE (Nat.sub_le p 1)
  let DK : ℕ ⥤ C := (horizontalFiniteTotalHomologyFiltration K (p + q)).diagram
  let DL : ℕ ⥤ C := (horizontalFiniteTotalHomologyFiltration L (p + q)).diagram
  let eKPrev : (horizontalTotalHomologyFiltration K (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅ DK.obj (p - 1) :=
    horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K (p + q) p hp
  let eLPrev : (horizontalTotalHomologyFiltration L (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅ DL.obj (p - 1) :=
    horizontalPositivePrevCompleteFiniteHomologyFiltrationIso L (p + q) p hp
  let eKCurr : (horizontalTotalHomologyFiltration K (p + q)).obj
      (((p : ℤ) : EInt)) ≅ DK.obj p :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)).app p
  let eLCurr : (horizontalTotalHomologyFiltration L (p + q)).obj
      (((p : ℤ) : EInt)) ≅ DL.obj p :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q)).app p
  let τ : DK ⟶ DL :=
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor (p + q)).map f).natTrans
  let dK : DK.obj (p - 1) ⟶ DK.obj p := DK.map a
  let dL : DL.obj (p - 1) ⟶ DL.obj p := DL.map a
  have hK :
      horizontalTotalHomologyFiltrationStepMap K p q ≫ eKCurr.hom =
        eKPrev.hom ≫ dK :=
    horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
      K p q hp
  have hL :
      dL ≫ eLCurr.inv =
        eLPrev.inv ≫ horizontalTotalHomologyFiltrationStepMap L p q :=
    horizontalFiniteTotalHomologyFiltrationStepMap_comp_positiveComparison_inv
      L p q hp
  have hm : dK ≫ τ.app p = τ.app (p - 1) ≫ dL :=
    τ.naturality a
  rw [horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq]
  change
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        (eKCurr.hom ≫ τ.app p ≫ eLCurr.inv) =
      (eKPrev.hom ≫ τ.app (p - 1) ≫ eLPrev.inv) ≫
        horizontalTotalHomologyFiltrationStepMap L p q
  calc
    horizontalTotalHomologyFiltrationStepMap K p q ≫
          (eKCurr.hom ≫ τ.app p ≫ eLCurr.inv) =
        (horizontalTotalHomologyFiltrationStepMap K p q ≫ eKCurr.hom) ≫
          τ.app p ≫ eLCurr.inv := by
      simp only [Category.assoc]
    _ = (eKPrev.hom ≫ dK) ≫ τ.app p ≫ eLCurr.inv := by
      rw [hK]
    _ = eKPrev.hom ≫ (dK ≫ τ.app p) ≫ eLCurr.inv := by
      simp only [Category.assoc]
    _ = eKPrev.hom ≫ (τ.app (p - 1) ≫ dL) ≫ eLCurr.inv := by
      rw [hm]
    _ = (eKPrev.hom ≫ τ.app (p - 1)) ≫
        (dL ≫ eLCurr.inv) := by
      simp only [Category.assoc]
    _ = (eKPrev.hom ≫ τ.app (p - 1)) ≫
        (eLPrev.inv ≫ horizontalTotalHomologyFiltrationStepMap L p q) := by
      rw [hL]
    _ = (eKPrev.hom ≫ τ.app (p - 1) ≫ eLPrev.inv) ≫
        horizontalTotalHomologyFiltrationStepMap L p q := by
      simp only [Category.assoc]

end HomologicalComplex₂

end
