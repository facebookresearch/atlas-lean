/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LinearizedLineBundles
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Actual group torsors and associated-bundle quotient diagrams

A torsor has an actual total scheme, fppf projection, group action and
invertible action-to-fibre-product map. A quotient-stack object also
contains the actual equivariant map to the acted-on scheme. The
associated bundle below is the diagonal quotient of those two actual
schemes, with its actual descended section and relative universal
property. Scheme-valued tests retain nonreduced parameter data.

The left-action convention is used on both the torsor and the target:
`u(gp) = g u(p)`. It is equivalent to the usual right-torsor convention
after inversion of the group action.

References: Stacks Project, Tags 04UR and 0CQJ; Ciocan-Fontanine--Kim--
Maulik, arXiv:1106.3724v2, Sections 2 and 7. Native fppf torsor/source
integration is already implemented in AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
Spaces/Groupoids/GroupSpaces/FppfTorsorsPrincipalComparison.lean.
The definitions here are original adapters to native scheme actions.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GroupTorsorGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The literal action-to-fibre-product map of an invariant scheme projection. -/
def relation {P T : Over S} (a : G ⊗ P ⟶ P) (p : P ⟶ T)
    (h : a ≫ p = snd G P ≫ p) :
    (G ⊗ P).left ⟶ pullback p.left p.left :=
  pullback.lift (snd G P).left a.left
    (by simpa using (congrArg Over.Hom.left h).symm)

/-- A genuine fppf group torsor on the specified parameter scheme. -/
structure Torsor (T : Over S) where
  total : Over S
  projection : total ⟶ T
  [action : ModObj G total]
  invariant : γ[G,total] ≫ projection = snd G total ≫ projection
  [flat : Flat projection.left]
  [presentation : LocallyOfFinitePresentation projection.left]
  [surjective : Surjective projection.left]
  [relation_isIso : IsIso (relation G γ[G,total] projection invariant)]

attribute [instance] Torsor.action Torsor.flat Torsor.presentation
  Torsor.surjective Torsor.relation_isIso

variable (W : Over S) [ModObj G W]

/-- The actual torsor and equivariant map presenting a quotient-stack point. -/
structure QuotientObject (T : Over S) where
  torsor : Torsor G T
  map : torsor.total ⟶ W
  equivariant : γ[G,torsor.total] ≫ map = (G ◁ map) ≫ γ[G,W]

/-- Actual equivariant isomorphisms, preserving the parameter and the target map. -/
structure QuotientIso {T : Over S} (P Q : QuotientObject G W T) where
  iso : P.torsor.total ≅ Q.torsor.total
  over : iso.hom ≫ Q.torsor.projection = P.torsor.projection
  equivariant : γ[G,P.torsor.total] ≫ iso.hom = (G ◁ iso.hom) ≫ γ[G,Q.torsor.total]
  target : iso.hom ≫ Q.map = P.map

@[ext] theorem QuotientIso.ext {T : Over S} {P Q : QuotientObject G W T}
    (f g : QuotientIso G W P Q) (h : f.iso.hom = g.iso.hom) : f = g := by
  have hi : f.iso = g.iso := Iso.ext h
  cases f
  cases g
  cases hi
  rfl

def QuotientIso.id {T : Over S} (P : QuotientObject G W T) : QuotientIso G W P P where
  iso := Iso.refl _
  over := by simp
  equivariant := by simp
  target := by simp

def QuotientIso.comp {T : Over S} {P Q R : QuotientObject G W T}
    (f : QuotientIso G W P Q) (g : QuotientIso G W Q R) : QuotientIso G W P R where
  iso := f.iso ≪≫ g.iso
  over := by simp only [Iso.trans_hom, Category.assoc, g.over, f.over]
  equivariant := by
    change γ[G,P.torsor.total] ≫ (f.iso.hom ≫ g.iso.hom) =
      (G ◁ (f.iso.hom ≫ g.iso.hom)) ≫ γ[G,R.torsor.total]
    rw [← Category.assoc, f.equivariant, Category.assoc, g.equivariant,
      ← Category.assoc, ← whiskerLeft_comp]
  target := by simp only [Iso.trans_hom, Category.assoc, g.target, f.target]

def QuotientIso.symm {T : Over S} {P Q : QuotientObject G W T}
    (f : QuotientIso G W P Q) : QuotientIso G W Q P where
  iso := f.iso.symm
  over := by rw [← f.over]; simp
  equivariant := by
    apply (cancel_mono f.iso.hom).1
    change (γ[G,Q.torsor.total] ≫ f.iso.inv) ≫ f.iso.hom =
      ((G ◁ f.iso.inv) ≫ γ[G,P.torsor.total]) ≫ f.iso.hom
    rw [Category.assoc, f.iso.inv_hom_id, Category.comp_id,
      Category.assoc, f.equivariant, ← Category.assoc, ← whiskerLeft_comp,
      f.iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  target := by rw [← f.target]; simp

instance quotientCategory (T : Over S) : Category (QuotientObject G W T) where
  Hom := QuotientIso G W
  id := QuotientIso.id G W
  comp := QuotientIso.comp G W
  id_comp _ := by apply QuotientIso.ext; exact Category.id_comp _
  comp_id _ := by apply QuotientIso.ext; exact Category.comp_id _
  assoc _ _ _ := by apply QuotientIso.ext; exact Category.assoc _ _ _

/-- Every quotient-stack arrow has its actual equivariant inverse. -/
def quotientArrowIso {T : Over S} {P Q : QuotientObject G W T} (f : P ⟶ Q) : P ≅ Q where
  hom := f
  inv := QuotientIso.symm G W f
  hom_inv_id := by apply QuotientIso.ext; exact f.iso.hom_inv_id
  inv_hom_id := by apply QuotientIso.ext; exact f.iso.inv_hom_id

instance quotientIsGroupoid (T : Over S) : IsGroupoid (QuotientObject G W T) where
  all_isIso f := by
    let e := quotientArrowIso G W f
    exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- A torsor reindex is normalized against the actual Cartesian scheme pullback. -/
structure Reindex {T T' : Over S} (P : Torsor G T) (f : T' ⟶ T) where
  torsor : Torsor G T'
  comparison : torsor.total ≅ pullback P.projection f
  projection : comparison.hom ≫ pullback.snd P.projection f = torsor.projection
  action : γ[G,torsor.total] ≫ (comparison.hom ≫ pullback.fst P.projection f) =
    (G ◁ (comparison.hom ≫ pullback.fst P.projection f)) ≫ γ[G,P.total]

/-- The actual map back to the original total torsor. -/
def Reindex.original {T T' : Over S} {P : Torsor G T} {f : T' ⟶ T}
    (R : Reindex G P f) : R.torsor.total ⟶ P.total :=
  R.comparison.hom ≫ pullback.fst P.projection f

theorem Reindex.square {T T' : Over S} {P : Torsor G T} {f : T' ⟶ T}
    (R : Reindex G P f) : R.original G ≫ P.projection = R.torsor.projection ≫ f := by
  rw [Reindex.original, Category.assoc, pullback.condition, ← Category.assoc, R.projection]

/-- Reindexing retains the literal original equivariant section map. -/
def reindexObject {T T' : Over S} (P : QuotientObject G W T) (f : T' ⟶ T)
    (R : Reindex G P.torsor f) : QuotientObject G W T' where
  torsor := R.torsor
  map := R.original G ≫ P.map
  equivariant := by
    have ha : γ[G,R.torsor.total] ≫ R.original G =
        (G ◁ R.original G) ≫ γ[G,P.torsor.total] := R.action
    change γ[G,R.torsor.total] ≫ (R.original G ≫ P.map) =
      (G ◁ (R.original G ≫ P.map)) ≫ γ[G,W]
    rw [← Category.assoc, ha, Category.assoc, P.equivariant,
      ← Category.assoc, ← whiskerLeft_comp]

/-- The diagonal action is computed on both actual scheme components. -/
def diagonalAction {T : Over S} (P : QuotientObject G W T) :
    G ⊗ (P.torsor.total ⊗ W) ⟶ P.torsor.total ⊗ W :=
  lift ((G ◁ fst P.torsor.total W) ≫ γ[G,P.torsor.total])
    ((G ◁ snd P.torsor.total W) ≫ γ[G,W])

/-- The actual graph of the equivariant map. -/
def graph {T : Over S} (P : QuotientObject G W T) :
    P.torsor.total ⟶ P.torsor.total ⊗ W := lift (𝟙 _) P.map

@[simp] theorem graph_projection {T : Over S} (P : QuotientObject G W T) :
    graph G W P ≫ fst P.torsor.total W = 𝟙 _ := by simp [graph]

/-- An associated bundle is the actual diagonal quotient, with its
projection and graph-descended section fixed. -/
structure AssociatedBundle {T : Over S} (P : QuotientObject G W T) where
  bundle : Over S
  projection : bundle ⟶ T
  quotient : P.torsor.total ⊗ W ⟶ bundle
  square : quotient ≫ projection = fst P.torsor.total W ≫ P.torsor.projection
  invariant : diagonalAction G W P ≫ quotient = snd G (P.torsor.total ⊗ W) ≫ quotient
  [flat : Flat quotient.left]
  [presentation : LocallyOfFinitePresentation quotient.left]
  [surjective : Surjective quotient.left]
  [relation_isIso : IsIso (relation G (diagonalAction G W P) quotient invariant)]
  sectionMap : T ⟶ bundle
  section_over : sectionMap ≫ projection = 𝟙 T
  section_normalized : P.torsor.projection ≫ sectionMap = graph G W P ≫ quotient
  universal : ∀ (Z : Over S) (z : Z ⟶ T) (f : P.torsor.total ⊗ W ⟶ Z),
    f ≫ z = fst P.torsor.total W ≫ P.torsor.projection →
    diagonalAction G W P ≫ f = snd G (P.torsor.total ⊗ W) ≫ f →
      ∃! h : bundle ⟶ Z, h ≫ z = projection ∧ quotient ≫ h = f

attribute [instance] AssociatedBundle.flat AssociatedBundle.presentation
  AssociatedBundle.surjective AssociatedBundle.relation_isIso

/-- The associated-bundle base change keeps the actual Cartesian quotient
map and the actual section; these maps are not independent choices. -/
structure AssociatedReindex {T T' : Over S} (P : QuotientObject G W T) (f : T' ⟶ T)
    (R : Reindex G P.torsor f) (B : AssociatedBundle G W P)
    (B' : AssociatedBundle G W (reindexObject G W P f R)) where
  comparison : B'.bundle ≅ pullback B.projection f
  projection : comparison.hom ≫ pullback.snd B.projection f = B'.projection
  quotient : B'.quotient ≫ comparison.hom ≫ pullback.fst B.projection f =
    tensorHom (R.original G) (𝟙 W) ≫ B.quotient
  sectionMap : B'.sectionMap ≫ comparison.hom ≫ pullback.fst B.projection f = f ≫ B.sectionMap

end MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
