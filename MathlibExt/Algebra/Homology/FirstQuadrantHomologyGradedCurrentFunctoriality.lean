/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedMap
public import Mathlib.CategoryTheory.HomCongr

/-!
# Functorial maps on current homology-filtration stages

Let C be an abelian category, p,q ∈ ℕ, and F_p(K) the complete image-filtration stage in
H_{p+q}(Tot(K)). A bicomplex map f induces F_p(K) → F_p(L) by transporting its finite
image-stage map through the complete-to-finite comparisons at p.

These maps preserve identity morphisms and composition. The current-stage construction is
defined for every p, including p=0.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. In total
degree n=p+q, let c(f) : F_p(K) → F_p(L) be the current complete image-stage map obtained by
conjugating the finite stage-p map with the complete-to-finite comparisons. Then c(𝟙_K) =
𝟙_{F_p(K)}. The formula holds for every p, including column zero. -/
@[simp 1100]
theorem
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) p q = 𝟙 _ := by
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor (C := C) (p + q)
  let eK : (horizontalTotalHomologyFiltration K (p + q)).obj (((p : ℤ) : EInt)) ≅
      ((F.obj K).filtration.diagram).obj p :=
    ((evaluation ℕ C).obj p).mapIso
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q))
  let θ : (F.obj K ⟶ F.obj K) →
      ((horizontalTotalHomologyFiltration K (p + q)).obj (((p : ℤ) : EInt)) ⟶
        (horizontalTotalHomologyFiltration K (p + q)).obj (((p : ℤ) : EInt))) :=
    fun h => eK.hom ≫ h.natTrans.app p ≫ eK.inv
  change θ (F.map (𝟙 K)) = 𝟙 _
  calc
    θ (F.map (𝟙 K)) = θ (𝟙 (F.obj K)) := congrArg θ (F.map_id K)
    _ = 𝟙 _ := by
      change eK.hom ≫ 𝟙 _ ≫ eK.inv = 𝟙 _
      calc
        eK.hom ≫ 𝟙 _ ≫ eK.inv = eK.hom ≫ eK.inv :=
          congrArg (fun h => eK.hom ≫ h) (Category.id_comp eK.inv)
        _ = 𝟙 _ := eK.hom_inv_id

/-- Let C be an abelian category and f : K → L, g : L → M composable maps of bicomplexes of shape
(down ℕ,down ℕ). For p,q ∈ ℕ and n=p+q, let c(f) : F_pH_n(Tot(K)) → F_pH_n(Tot(L)) be the
current-stage map transported from the finite image filtration. Then c(f ≫ g) = c(f) ≫ c(g).
Each intermediate complete-to-finite stage comparison is an isomorphism, and the equality uses
the same column p and total degree n throughout. -/
@[simp 1100]
theorem
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex g p q := by
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor (C := C) (p + q)
  let eK : (horizontalTotalHomologyFiltration K (p + q)).obj (((p : ℤ) : EInt)) ≅
      ((F.obj K).filtration.diagram).obj p :=
    ((evaluation ℕ C).obj p).mapIso
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q))
  let eL : (horizontalTotalHomologyFiltration L (p + q)).obj (((p : ℤ) : EInt)) ≅
      ((F.obj L).filtration.diagram).obj p :=
    ((evaluation ℕ C).obj p).mapIso
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q))
  let eM : (horizontalTotalHomologyFiltration M (p + q)).obj (((p : ℤ) : EInt)) ≅
      ((F.obj M).filtration.diagram).obj p :=
    ((evaluation ℕ C).obj p).mapIso
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso M (p + q))
  let θ : (F.obj K ⟶ F.obj M) →
      ((horizontalTotalHomologyFiltration K (p + q)).obj (((p : ℤ) : EInt)) ⟶
        (horizontalTotalHomologyFiltration M (p + q)).obj (((p : ℤ) : EInt))) :=
    fun h => eK.hom ≫ h.natTrans.app p ≫ eM.inv
  change θ (F.map (f ≫ g)) =
    (eK.hom ≫ (F.map f).natTrans.app p ≫ eL.inv) ≫
      (eL.hom ≫ (F.map g).natTrans.app p ≫ eM.inv)
  calc
    θ (F.map (f ≫ g)) = θ (F.map f ≫ F.map g) := congrArg θ (F.map_comp f g)
    _ = (eK.hom ≫ (F.map f).natTrans.app p ≫ eL.inv) ≫
        (eL.hom ≫ (F.map g).natTrans.app p ≫ eM.inv) := by
      change eK.hom ≫ ((F.map f).natTrans.app p ≫ (F.map g).natTrans.app p) ≫ eM.inv = _
      exact Iso.homCongr_comp eK.symm eL.symm eM.symm
        ((F.map f).natTrans.app p) ((F.map g).natTrans.app p)

end HomologicalComplex₂

end
