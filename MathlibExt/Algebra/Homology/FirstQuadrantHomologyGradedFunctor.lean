/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedUnifiedPrevFunctoriality

/-!
# Functorial associated graded of first-quadrant total homology

The preceding and current total-homology filtration stages form functors of
the bicomplex.  Their consecutive-stage maps form a natural transformation,
whose pointwise arrows give the filtration-step Arrow functor.  Composing
with the cokernel functor packages the associated graded pieces and their
landed maps into a functor.

Identity and composition of the associated-graded maps are inherited from
this functor; no cokernel universal property is reopened here.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The preceding complete total-homology filtration stage, functorial in
the bicomplex. -/
noncomputable def horizontalPrevTotalHomologyFiltrationFunctor
    (p q : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤ C where
  obj K := (horizontalTotalHomologyFiltration K (p + q)).obj
    ((((p : ℤ) - 1 : ℤ) : EInt))
  map f := horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q
  map_id K := horizontalPrevTotalHomologyFiltrationMapOfBicomplex_id K p q
  map_comp f g :=
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex_comp f g p q

/-- The current complete total-homology filtration stage, functorial in the
bicomplex. -/
noncomputable def horizontalCurrentTotalHomologyFiltrationFunctor
    (p q : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤ C where
  obj K := (horizontalTotalHomologyFiltration K (p + q)).obj
    (((p : ℤ) : EInt))
  map f := horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
    f p q
  map_id K :=
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_id K p q
  map_comp f g :=
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp
      f g p q

@[simp]
theorem horizontalPrevTotalHomologyFiltrationFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalPrevTotalHomologyFiltrationFunctor
      (C := C) p q).obj K =
      (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) :=
  rfl

@[simp]
theorem horizontalPrevTotalHomologyFiltrationFunctor_map
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalPrevTotalHomologyFiltrationFunctor
      (C := C) p q).map f =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

@[simp]
theorem horizontalCurrentTotalHomologyFiltrationFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalCurrentTotalHomologyFiltrationFunctor
      (C := C) p q).obj K =
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℤ) : EInt)) :=
  rfl

@[simp]
theorem horizontalCurrentTotalHomologyFiltrationFunctor_map
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalCurrentTotalHomologyFiltrationFunctor
      (C := C) p q).map f =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

/-- Consecutive complete total-homology filtration steps form a natural
transformation between the predecessor and current stage functors. -/
noncomputable def horizontalTotalHomologyFiltrationStepNatTrans
    (p q : ℕ) :
    horizontalPrevTotalHomologyFiltrationFunctor (C := C) p q ⟶
      horizontalCurrentTotalHomologyFiltrationFunctor (C := C) p q where
  app K := horizontalTotalHomologyFiltrationStepMap K p q
  naturality _ _ f :=
    (horizontalTotalHomologyFiltrationStepMap_naturality f p q).symm

@[simp]
theorem horizontalTotalHomologyFiltrationStepNatTrans_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepNatTrans
      (C := C) p q).app K =
      horizontalTotalHomologyFiltrationStepMap K p q :=
  rfl

/-- The consecutive filtration step as a functor to the arrow category. -/
noncomputable def horizontalTotalHomologyFiltrationStepArrowFunctor
    (p q : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤ Arrow C :=
  (horizontalTotalHomologyFiltrationStepNatTrans (C := C) p q).arrow

@[simp]
theorem horizontalTotalHomologyFiltrationStepArrowFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepArrowFunctor
      (C := C) p q).obj K =
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap K p q) :=
  rfl

@[simp]
theorem horizontalTotalHomologyFiltrationStepArrowFunctor_map
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepArrowFunctor
      (C := C) p q).map f =
      horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q :=
  rfl

/-- Associated graded pieces of total homology, functorial in the
first-quadrant bicomplex. -/
noncomputable def horizontalTotalHomologyGradedPieceFunctor
    (p q : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤ C :=
  horizontalTotalHomologyFiltrationStepArrowFunctor (C := C) p q ⋙
    Limits.coker C

@[simp]
theorem horizontalTotalHomologyGradedPieceFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) p q).obj K =
      horizontalTotalHomologyGradedPiece K p q :=
  rfl

@[simp]
theorem horizontalTotalHomologyGradedPieceFunctor_map
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) p q).map f =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
  rfl

/-- The associated-graded map of an identity bicomplex morphism is the
identity. -/
@[simp 1100]
theorem horizontalTotalHomologyGradedPieceMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalTotalHomologyGradedPieceMapOfBicomplex (𝟙 K) p q = 𝟙 _ := by
  simpa only [horizontalTotalHomologyGradedPieceFunctor_map,
    horizontalTotalHomologyGradedPieceFunctor_obj] using
    (horizontalTotalHomologyGradedPieceFunctor
      (C := C) p q).map_id K

/-- Associated-graded maps preserve composition of bicomplex morphisms. -/
@[simp 1100]
theorem horizontalTotalHomologyGradedPieceMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalTotalHomologyGradedPieceMapOfBicomplex (f ≫ g) p q =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f p q ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex g p q := by
  simpa only [horizontalTotalHomologyGradedPieceFunctor_map] using
    (horizontalTotalHomologyGradedPieceFunctor
      (C := C) p q).map_comp f g

end HomologicalComplex₂

end
