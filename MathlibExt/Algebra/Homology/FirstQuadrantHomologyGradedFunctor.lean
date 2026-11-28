/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedUnifiedPrevFunctoriality

/-!
# Functorial associated graded total homology

Let C be an abelian category, p,q ∈ ℕ, and n=p+q. For a bicomplex K of shape (down ℕ,down ℕ),
the complete image stages F_{p−1}H_n(Tot(K)) and F_pH_n(Tot(K)) are functorial in K. Their
inclusion defines a natural transformation and hence a functor to Arrow(C).

Composing with the cokernel functor gives K ↦ Gr_pH_n(Tot(K)) = coker(F_{p−1} → F_p). The
induced associated graded maps preserve identity morphisms and composition. The predecessor
index is in ℤ, so at p=0 its stage is F_{−1}=0.
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

/-- Let C be an abelian category and p,q ∈ ℕ. The assignment K ↦ F_{(p:ℤ)−1}H_{p+q}(Tot(K)), for
bicomplexes of shape (down ℕ,down ℕ), defines a functor to C. A bicomplex map acts by the
finite predecessor image map transported to the complete stage when p>0, and by the zero map
between the zero stages at index −1 when p=0. These maps preserve identities and composition. -/
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

/-- Let C be an abelian category and p,q ∈ ℕ. Assign to a bicomplex K of shape (down ℕ,down ℕ) the
stage F_pH_{p+q}(Tot(K)) of its complete image filtration. On a bicomplex map, use the finite
stage-p image map conjugated by the complete-to-finite stage comparisons. This gives a functor
to C for every p, including zero, with the stated current-stage identity and composition laws. -/
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

/-- Let C be an abelian category and p,q ∈ ℕ. The inclusions s_K : F_{p−1}H_{p+q}(Tot(K)) →
F_pH_{p+q}(Tot(K)) form a natural transformation from the predecessor-stage functor to the
current-stage functor on bicomplexes of shape (down ℕ,down ℕ). If f : K → L, its naturality
equation is a_prev(f) ≫ s_L = s_K ≫ a_current(f), with the predecessor index computed in ℤ. -/
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

/-- Let C be an abelian category and p,q ∈ ℕ. The consecutive-stage natural transformation defines
a functor from bicomplexes of shape (down ℕ,down ℕ) to Arrow(C). Its object at K is
F_{p−1}H_{p+q}(Tot(K)) → F_pH_{p+q}(Tot(K)), and its map on f : K → L is the commutative
square with the induced predecessor and current-stage maps as its two components. -/
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

/-- Let C be an abelian category and p,q ∈ ℕ. Define a functor on bicomplexes of shape (down
ℕ,down ℕ) by K ↦ Gr_pH_{p+q}(Tot(K)) = coker(F_{p−1}H_{p+q}(Tot(K)) → F_pH_{p+q}(Tot(K))). It
is the consecutive-stage arrow functor followed by coker : Arrow(C) → C. A bicomplex map acts
by the cokernel map of its predecessor/current filtration square. -/
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

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. The
cokernel map induced by the identity bicomplex morphism is the identity on
Gr_pH_{p+q}(Tot(K)). Here the associated graded object is the cokernel of the complete-stage
inclusion F_{p−1} → F_p, with p−1 computed in ℤ. The equality holds also at p=0. -/
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

/-- Let C be an abelian category and f : K → L, g : L → M composable morphisms of bicomplexes of
shape (down ℕ,down ℕ). For p,q ∈ ℕ, the induced associated graded maps satisfy Gr_{p,p+q}(f ≫
g) = Gr_{p,p+q}(f) ≫ Gr_{p,p+q}(g). Each map is the cokernel map of the consecutive
image-filtration square F_{p−1}H_{p+q} → F_pH_{p+q}. -/
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
