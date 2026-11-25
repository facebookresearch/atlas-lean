/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRows
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan

/-!
# Right-comma Bousfield--Kan homology bicomplex

For `F : C ⥤ D`, the strict diagram `d ↦ nerve (F / d)` gives the
cofibered orientation of the category-homology bicomplex.  A bidegree
generator is a base chain and a chain in the right comma category over its
left endpoint.  Equivalently, it consists of

```text
F(c_q) ⟶ d₀ ⟶ ⋯ ⟶ d_p,    c₀ ⟶ ⋯ ⟶ c_q.
```

The intermediate arrows `F(c_i) ⟶ d₀` are forced by the terminal anchor.
This is the categorical dual of the arrow orientation printed in Weibel,
*The K-book*, IV, Exercise 3.7, and is the orientation compatible with a
cofibered functor.

This file identifies the already-constructed weighted-bar bidegrees with
these generators and specializes the generic Bousfield--Kan bicomplex.  It
does not assert a diagonal comparison, a fiber-homology page, or
convergence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u vA uA

namespace SSet

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

/-- Corrected cofibered-orientation generators in bidegree `(p,q)`: a base
chain and a comma-category chain over its left endpoint. -/
structure RightCommaBidegreeGenerator (F : C ⥤ D) (p q : ℕ) where
  base : ComposableArrows D p
  comma : ComposableArrows (CostructuredArrow F base.left) q

namespace RightCommaBidegreeGenerator

/-- Underlying total-category chain of a corrected generator. -/
def totalChain {F : C ⥤ D} {p q : ℕ}
    (x : RightCommaBidegreeGenerator F p q) : ComposableArrows C q :=
  x.comma ⋙ CostructuredArrow.proj F x.base.left

/-- Terminal anchor `F(c_q) ⟶ d₀` of a corrected generator. -/
def terminalAnchor {F : C ⥤ D} {p q : ℕ}
    (x : RightCommaBidegreeGenerator F p q) :
    F.obj x.totalChain.right ⟶ x.base.left :=
  (x.comma.obj (Fin.last q)).hom

/-- Every earlier comma anchor is forced by the total chain and its terminal
anchor. -/
theorem map'_terminalAnchor {F : C ⥤ D} {p q : ℕ}
    (x : RightCommaBidegreeGenerator F p q) (i : Fin (q + 1)) :
    F.map (x.totalChain.map' i.val q) ≫ x.terminalAnchor =
      (x.comma.obj i).hom := by
  exact CostructuredArrow.w (x.comma.map' i.val q)

end RightCommaBidegreeGenerator

/-- The simplicial-replacement presentation is the explicit right-comma
generator type, with its contractible terminal weight removed. -/
def rightCommaReplGeneratorEquiv (F : C ⥤ D) (p q : ℕ) :
    CategoryBar.replObj D
      (wbarDegreeCoefficient (rightCommaNerveDiagram F) (op ⦋q⦌)) p ≃
        RightCommaBidegreeGenerator F p q where
  toFun x := ⟨x.1, x.2.1⟩
  invFun x := ⟨x.base, x.comma, PUnit.unit⟩
  left_inv x := by
    rcases x with ⟨base, comma, weight⟩
    rcases weight
    rfl
  right_inv x := by
    rcases x with ⟨base, comma⟩
    rfl

/-- A bidegree of the right-comma weighted bar is exactly the corrected
Weibel generator type. -/
noncomputable def rightCommaBarBidegreeEquiv (F : C ⥤ D) (p q : ℕ) :
    ((bkBarBisimplicial (rightCommaNerveDiagram F)).obj
      (op ⦋p⦌)).obj (op ⦋q⦌) ≃
        RightCommaBidegreeGenerator F p q :=
  (terminalWeightRowDegreeIso (rightCommaNerveDiagram F)
    (op ⦋q⦌) p).toEquiv.trans
      (rightCommaReplGeneratorEquiv F p q)

variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{u} A]

/-- Right-comma Bousfield--Kan homology bicomplex. -/
noncomputable abbrev rightCommaAlternatingBicomplex
    (R : A) (F : C ⥤ D) :
    HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) :=
  bkAlternatingBicomplex A R (rightCommaNerveDiagram F)

/-- Each right-comma bidegree is freely linearized on the corrected Weibel
generator type. -/
noncomputable def rightCommaAlternatingBidegreeIso
    (R : A) (F : C ⥤ D) (p q : ℕ) :
    ((rightCommaAlternatingBicomplex A R F).X p).X q ≅
      ∐ fun _ : RightCommaBidegreeGenerator F p q => R :=
  ((sigmaConst : A ⥤ (Type u ⥤ A)).obj R).mapIso
    (rightCommaBarBidegreeEquiv F p q).toIso

end SSet

end
