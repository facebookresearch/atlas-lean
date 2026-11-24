/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlternating
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim

/-!
# The homology bicomplex of a Bousfield--Kan bar

A simplicial-set-valued diagram has a terminal-weight weighted bar, which is
a bisimplicial set before taking its diagonal.  This file linearizes that
bisimplicial set degreewise, applies the alternating-face bicomplex, and
exposes its signed direct-sum total complex functorially in the diagram.

The construction reuses the existing strict weighted bar and generic
bisimplicial alternating complex.  It does not assert an
Alexander--Whitney comparison with the diagonal, identify a spectral-
sequence page, or prove convergence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w uJ vJ vA uA

namespace SSet

section GenericLinearization

variable (A : Type uA) [Category.{vA} A] [HasCoproducts.{w} A]

/-- Degreewise coproduct linearization of simplicial sets with coefficient
object `R`. -/
noncomputable def coproductLinearizationFunctor (R : A) :
    SSet.{w} ⥤ SimplicialObject A :=
  (SimplicialObject.whiskering (Type w) A).obj
    ((sigmaConst : A ⥤ (Type w ⥤ A)).obj R)

/-- Pointwise linearization of bisimplicial sets. -/
noncomputable def bisimplicialLinearizationFunctor (R : A) :
    SimplicialObject SSet.{w} ⥤
      SimplicialObject (SimplicialObject A) :=
  (SimplicialObject.whiskering SSet.{w}
    (SimplicialObject A)).obj (coproductLinearizationFunctor A R)

/-- In bidegree `(p,q)`, pointwise linearization is the coproduct of copies
of `R` indexed by the `(p,q)`-bisimplices. -/
@[simp]
theorem bisimplicialLinearizationFunctor_obj_obj_obj
    (R : A) (B : SimplicialObject SSet.{w}) (p q : ℕ) :
    (((bisimplicialLinearizationFunctor A R).obj B).obj
      (op ⦋p⦌)).obj (op ⦋q⦌) =
        ∐ fun _ : (B.obj (op ⦋p⦌)).obj (op ⦋q⦌) => R :=
  rfl

end GenericLinearization

section CommonIndex

variable (A : Type uA) [Category.{vA} A] [HasCoproducts.{max uJ vJ} A]
  {J : Type uJ} [Category.{vJ} J]


section

variable [Preadditive A]

/-- Functorial bisimplicial terminal-weight bar underlying the
Bousfield--Kan homotopy-colimit carrier. -/
noncomputable def bkBarBisimplicialFunctor :
    (J ⥤ SSet.{max uJ vJ}) ⥤ SimplicialObject SSet.{max uJ vJ} where
  obj D := StrictOrdinaryWeightedBar.wbarSimplicial
    (CategoryBar.replUnit J) D
  map alpha := StrictOrdinaryWeightedBar.wbarSimplicialMapF
    (CategoryBar.replUnit J) alpha
  map_id D := StrictOrdinaryWeightedBar.wbarSimplicialMapF_id
    (CategoryBar.replUnit J) D
  map_comp alpha beta :=
    StrictOrdinaryWeightedBar.wbarSimplicialMapF_comp
      (CategoryBar.replUnit J) alpha beta

/-- Bisimplicial terminal-weight bar underlying the Bousfield--Kan
homotopy-colimit carrier. -/
noncomputable abbrev bkBarBisimplicial (D : J ⥤ SSet.{max uJ vJ}) :
    SimplicialObject SSet.{max uJ vJ} :=
  (bkBarBisimplicialFunctor (J := J)).obj D

/-- Functorial alternating bicomplex of the linearized Bousfield--Kan
bar. -/
noncomputable def bkAlternatingBicomplexFunctor (R : A) :
    (J ⥤ SSet.{max uJ vJ}) ⥤ HomologicalComplex₂ A
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  bkBarBisimplicialFunctor (J := J) ⋙
    bisimplicialLinearizationFunctor A R ⋙
    AlgebraicTopology.bisimplicialAlternatingBicomplexFunctor A

/-- Alternating bicomplex of the linearized Bousfield--Kan bar. -/
noncomputable abbrev bkAlternatingBicomplex (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) : HomologicalComplex₂ A
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (bkAlternatingBicomplexFunctor A R).obj D

/-- A Bousfield--Kan bidegree is the coproduct of copies of `R` indexed by
the corresponding weighted-bar bisimplices. -/
@[simp]
theorem bkAlternatingBicomplex_X_X (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) (p q : ℕ) :
    ((bkAlternatingBicomplex A R D).X p).X q =
      ∐ fun _ : ((bkBarBisimplicial D).obj (op ⦋p⦌)).obj
        (op ⦋q⦌) => R :=
  rfl

section Total

variable [Limits.HasCountableCoproducts A]

/-- Functorial signed direct-sum total complex of the linearized
Bousfield--Kan bar. -/
noncomputable def bkAlternatingTotalComplexFunctor (R : A) :
    (J ⥤ SSet.{max uJ vJ}) ⥤ ChainComplex A ℕ :=
  bkAlternatingBicomplexFunctor A R ⋙
    HomologicalComplex₂.totalFunctor A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- Signed direct-sum total complex of the linearized Bousfield--Kan
bar. -/
noncomputable abbrev bkAlternatingTotalComplex (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) : ChainComplex A ℕ :=
  (bkAlternatingTotalComplexFunctor A R).obj D

/-- Inclusion of Bousfield--Kan bidegree `(p,q)` into total degree
`p+q`. -/
noncomputable def bkAlternatingTotalι (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) (p q : ℕ) :
    (∐ fun _ : ((bkBarBisimplicial D).obj (op ⦋p⦌)).obj
      (op ⦋q⦌) => R) ⟶
        (bkAlternatingTotalComplex A R D).X (p + q) :=
  (bkAlternatingBicomplex A R D).ιTotal
    (ComplexShape.down ℕ) p q (p + q) rfl

end Total
end
end CommonIndex
end SSet

end
