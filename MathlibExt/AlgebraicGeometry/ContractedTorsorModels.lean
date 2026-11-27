/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import MathlibExt.AlgebraicGeometry.QuotientLineDescentModels

/-!
# Actual contracted torsors and normalized families

Bundle objects and arrows reuse the native torsor quotient groupoid.
Tensor products (for commutative group schemes) are actual fppf quotients of
P times_X Q by the inverse diagonal action, with the actual product action and universal property.
Base changes are the actual Cartesian torsor pullbacks. Unit and
composition isomorphisms retain their actual maps to the original
torsor; maps of bundles retain their actual equivariant arrows.
References: Stacks Project Tags 04UR and0CQJ; Donagi--Gaitsgory
arXiv:math/0005132v3, Sections4--6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ContractedTorsorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GroupTorsorGeometry

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

instance terminalAction : ModObj G (𝟙_ (Over S)) where
  smul := toUnit _
  one_smul := Subsingleton.elim _ _
  mul_smul := Subsingleton.elim _ _

abbrev Bundle (X : Over S) := QuotientObject G (𝟙_ (Over S)) X

variable {G} {X : Over S}

abbrev product (P Q : Bundle G X) := pullback P.torsor.projection Q.torsor.projection

/-- The tensor product of two torsors under a commutative group scheme: the fppf quotient of
the fibre product by the inverse diagonal action. Commutativity is part of the data: for a
noncommutative group the inverse diagonal map is not an action and the quotient is not a
torsor. -/
structure TensorDiagram (P Q R : Bundle G X) where
  commutative : IsCommMonObj G
  quotient : product P Q ⟶ R.torsor.total
  projection : quotient ≫ R.torsor.projection =
    pullback.fst P.torsor.projection Q.torsor.projection ≫ P.torsor.projection
  inverseDiagonal : G ⊗ product P Q ⟶ product P Q
  first : inverseDiagonal ≫ pullback.fst P.torsor.projection Q.torsor.projection =
    (G ◁ pullback.fst P.torsor.projection Q.torsor.projection) ≫ γ[G,P.torsor.total]
  second : inverseDiagonal ≫ pullback.snd P.torsor.projection Q.torsor.projection =
    tensorHom ι[G] (pullback.snd P.torsor.projection Q.torsor.projection) ≫ γ[G,Q.torsor.total]
  invariant : inverseDiagonal ≫ quotient = snd G (product P Q) ≫ quotient
  [flat : Flat quotient.left]
  [presentation : LocallyOfFinitePresentation quotient.left]
  [surjective : Surjective quotient.left]
  [relation : IsIso (GroupTorsorGeometry.relation G inverseDiagonal quotient invariant)]
  productAction : G ⊗ product P Q ⟶ product P Q
  product_first : productAction ≫ pullback.fst P.torsor.projection Q.torsor.projection =
    (G ◁ pullback.fst P.torsor.projection Q.torsor.projection) ≫ γ[G,P.torsor.total]
  product_second : productAction ≫ pullback.snd P.torsor.projection Q.torsor.projection =
    snd G (product P Q) ≫ pullback.snd P.torsor.projection Q.torsor.projection
  equivariant : productAction ≫ quotient = (G ◁ quotient) ≫ γ[G,R.torsor.total]
  universal : ∀ (Z : Over S) (z : Z ⟶ X) (f : product P Q ⟶ Z),
    f ≫ z = pullback.fst P.torsor.projection Q.torsor.projection ≫ P.torsor.projection →
    inverseDiagonal ≫ f = snd G (product P Q) ≫ f →
      ∃! h : R.torsor.total ⟶ Z, h ≫ z = R.torsor.projection ∧ quotient ≫ h = f

def tensorPoint {P Q R : Bundle G X} (D : TensorDiagram P Q R)
    {U : Over S} (p : U ⟶ P.torsor.total) (q : U ⟶ Q.torsor.total)
    (h : p ≫ P.torsor.projection = q ≫ Q.torsor.projection) : U ⟶ R.torsor.total :=
  pullback.lift p q h ≫ D.quotient

theorem tensorPoint_over {P Q R : Bundle G X} (D : TensorDiagram P Q R)
    {U : Over S} (p : U ⟶ P.torsor.total) (q : U ⟶ Q.torsor.total)
    (h : p ≫ P.torsor.projection = q ≫ Q.torsor.projection) :
    tensorPoint D p q h ≫ R.torsor.projection = p ≫ P.torsor.projection := by
  rw [tensorPoint, Category.assoc, D.projection, ← Category.assoc, pullback.lift_fst]

structure PullbackModel {X X' : Over S} (P : Bundle G X) (f : X' ⟶ X) (P' : Bundle G X') where
  comparison : P'.torsor.total ≅ pullback P.torsor.projection f
  projection : comparison.hom ≫ pullback.snd P.torsor.projection f = P'.torsor.projection
  action : γ[G,P'.torsor.total] ≫ comparison.hom ≫ pullback.fst P.torsor.projection f =
    (G ◁ (comparison.hom ≫ pullback.fst P.torsor.projection f)) ≫ γ[G,P.torsor.total]

def original {X X' : Over S} {P : Bundle G X} {f : X' ⟶ X} {P' : Bundle G X'}
    (R : PullbackModel P f P') : P'.torsor.total ⟶ P.torsor.total :=
  R.comparison.hom ≫ pullback.fst P.torsor.projection f

structure Families where
  change : ∀ {X X' : Over S}, (X' ⟶ X) → (Bundle G X ⥤ Bundle G X')
  pullback : ∀ {X X' : Over S} (f : X' ⟶ X) (P : Bundle G X),
    PullbackModel P f ((change f).obj P)
  arrows : ∀ {X X' : Over S} (f : X' ⟶ X) {P Q : Bundle G X} (a : P ⟶ Q),
    ((change f).map a).iso.hom ≫ original (pullback f Q) =
      original (pullback f P) ≫ a.iso.hom
  unit : ∀ X : Over S, change (𝟙 X) ≅ 𝟭 (Bundle G X)
  unit_original : ∀ (X : Over S) (P : Bundle G X),
    original (pullback (𝟙 X) P) = ((unit X).hom.app P).iso.hom
  composition : ∀ {X X' X'' : Over S} (f : X' ⟶ X) (g : X'' ⟶ X'),
    change f ⋙ change g ≅ change (g ≫ f)
  composition_original : ∀ {X X' X'' : Over S} (f : X' ⟶ X) (g : X'' ⟶ X') (P : Bundle G X),
    ((composition f g).hom.app P).iso.hom ≫ original (pullback (g ≫ f) P) =
      original (pullback g ((change f).obj P)) ≫ original (pullback f P)

variable (G)

structure TensorOperations where
  tensor : ∀ X : Over S, (Bundle G X × Bundle G X) ⥤ Bundle G X
  model : ∀ (X : Over S) (P Q : Bundle G X), TensorDiagram P Q ((tensor X).obj (P, Q))
  arrows : ∀ (X : Over S) {P Q P' Q' : Bundle G X} (a : P ⟶ P') (b : Q ⟶ Q')
      {U : Over S} (p : U ⟶ P.torsor.total) (q : U ⟶ Q.torsor.total)
      (h : p ≫ P.torsor.projection = q ≫ Q.torsor.projection)
      (h' : (p ≫ a.iso.hom) ≫ P'.torsor.projection = (q ≫ b.iso.hom) ≫ Q'.torsor.projection),
    tensorPoint (model X P Q) p q h ≫ ((tensor X).map (a, b)).iso.hom =
      tensorPoint (model X P' Q') (p ≫ a.iso.hom) (q ≫ b.iso.hom) h'

variable {G} (H : Over S) [GrpObj H] (δ : G ⟶ H) [IsMonHom δ]

/-- Extension of structure group along `δ`: the quotient of `P × H` by
`g · (p, h) = (g · p, h · δ(g)⁻¹)`, with `H` acting on the left of the second factor. -/
structure Pushout (P : Bundle G X) (Q : Bundle H X) where
  quotient : P.torsor.total ⊗ H ⟶ Q.torsor.total
  projection : quotient ≫ Q.torsor.projection = fst P.torsor.total H ≫ P.torsor.projection
  inverseDiagonal : G ⊗ (P.torsor.total ⊗ H) ⟶ P.torsor.total ⊗ H
  first : inverseDiagonal ≫ fst P.torsor.total H =
    (G ◁ fst P.torsor.total H) ≫ γ[G,P.torsor.total]
  second : inverseDiagonal ≫ snd P.torsor.total H =
    CartesianMonoidalCategory.lift (snd G (P.torsor.total ⊗ H) ≫ snd P.torsor.total H)
      (fst G (P.torsor.total ⊗ H) ≫ δ ≫ ι[H]) ≫ μ[H]
  invariant : inverseDiagonal ≫ quotient = snd G (P.torsor.total ⊗ H) ≫ quotient
  [flat : Flat quotient.left]
  [presentation : LocallyOfFinitePresentation quotient.left]
  [surjective : Surjective quotient.left]
  [relation : IsIso (GroupTorsorGeometry.relation G inverseDiagonal quotient invariant)]
  universal : ∀ (Z : Over S) (z : Z ⟶ X) (f : P.torsor.total ⊗ H ⟶ Z),
    f ≫ z = fst P.torsor.total H ≫ P.torsor.projection →
    inverseDiagonal ≫ f = snd G (P.torsor.total ⊗ H) ≫ f →
      ∃! h : Q.torsor.total ⟶ Z, h ≫ z = Q.torsor.projection ∧ quotient ≫ h = f
  scalar : ∀ {U : Over S} (p : U ⟶ P.torsor.total) (h t : U ⟶ H),
    CartesianMonoidalCategory.lift p
      (CartesianMonoidalCategory.lift t h ≫ μ[H]) ≫ quotient =
      CartesianMonoidalCategory.lift t
        (CartesianMonoidalCategory.lift p h ≫ quotient) ≫ γ[H,Q.torsor.total]

end MathlibExt.AlgebraicGeometry.ContractedTorsorModels
