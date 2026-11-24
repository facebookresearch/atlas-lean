/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGluingChowModels

/-!
# The actual admissible root-equivalence catalogue for a fixed degeneration class

The carrier contains the actual two relative types, genera, numerical
classes, root orders, leg ordering and source-qualified degree equation.
Its equivalence relation relabels the actual roots and vertices while
preserving every global leg, genus and numerical class. A finite catalogue
is an OUTPUT complete modulo that relation on all geometrically realized
matching families; it is not a supplied arbitrary summation index.

All entries use the SAME standard degeneration and central moduli model.
Only the required total-leg transport changes its type parameter. The
matching and Phi structures are the actual native geometric outputs.

Source: Jun Li math/0110113v1 introduction pp2--4, Sections3.1--3.2,
(3.2)/(3.14) and Theorem3.15; empty branches of math/0009097v1 after(4.8).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiDegenerationCatalogueModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry StackCycleRelations StackAffineModules
open ExpandedTargetChainGeometry ExpandedTargetGluingModels RelativeProjectiveLineModels
open LiGluingRelativeTypes LiGluingGeometryModels LiExpandedDegenerationModels

variable {k : Type} [Field k] (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
  [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
  [LocallyOfFiniteType W0.scheme.hom]
  [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
  (N g : ℕ) (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)

structure Splitting where
  leftLegs : ℕ
  rightLegs : ℕ
  roots : ℕ
  legs : leftLegs + rightLegs = N
  left : FullType leftLegs roots
  right : FullType rightLegs roots
  leftClass : Fin left.vertices → StableMapNumericalClasses.NumericalClass P.target.left
  rightClass : Fin right.vertices → StableMapNumericalClasses.NumericalClass Q.target.left
  admissible : AdmissibleTriple (g := g) left right P Q W0 leftClass rightClass total

variable {P Q W0 N g total}

def Splitting.leftMark (s : Splitting P Q W0 N g total) (i : Fin s.leftLegs) : Fin N :=
  Fin.cast s.legs (s.admissible.legs.labels (Sum.inl i))

def Splitting.rightMark (s : Splitting P Q W0 N g total) (i : Fin s.rightLegs) : Fin N :=
  Fin.cast s.legs (s.admissible.legs.labels (Sum.inr i))

/-- Literal simultaneous root/vertex relabeling, preserving every global leg and degree. -/
def Relabeled (s t : Splitting P Q W0 N g total) : Prop :=
  ∃ (roots : Fin s.roots ≃ Fin t.roots)
    (left : Fin s.left.vertices ≃ Fin t.left.vertices)
    (right : Fin s.right.vertices ≃ Fin t.right.vertices)
    (leftLegs : Fin s.leftLegs ≃ Fin t.leftLegs)
    (rightLegs : Fin s.rightLegs ≃ Fin t.rightLegs),
    (∀ v, t.left.genus (left v) = s.left.genus v) ∧
    (∀ v, t.right.genus (right v) = s.right.genus v) ∧
    (∀ v, t.leftClass (left v) = s.leftClass v) ∧
    (∀ v, t.rightClass (right v) = s.rightClass v) ∧
    (∀ i, t.leftMark (leftLegs i) = s.leftMark i) ∧
    (∀ i, t.rightMark (rightLegs i) = s.rightMark i) ∧
    (∀ i, (t.left.legLabels (leftLegs i)).1 = left (s.left.legLabels i).1) ∧
    (∀ i, (t.right.legLabels (rightLegs i)).1 = right (s.right.legLabels i).1) ∧
    (∀ i, (t.left.rootLabels (roots i)).1 = left (s.left.rootLabels i).1) ∧
    (∀ i, (t.right.rootLabels (roots i)).1 = right (s.right.rootLabels i).1) ∧
    (∀ i, t.left.order (roots i) = s.left.order i) ∧
    (∀ i, t.right.order (roots i) = s.right.order i)

def splittingSetoid : Setoid (Splitting P Q W0 N g total) where
  r := Relation.EqvGen Relabeled
  iseqv :=
    { refl := fun x => Relation.EqvGen.refl x
      symm := fun h => Relation.EqvGen.symm _ _ h
      trans := fun h j => Relation.EqvGen.trans _ _ _ h j }

abbrev RootClass := Quotient (splittingSetoid (P := P) (Q := Q) (W0 := W0) (N := N) (g := g) (total := total))

variable (P Q W0 N g total)
  (W : OneParameter P Q W0)

/-- Shared original geometry and central target for EVERY admissible term. -/
structure Environment where
  expanded : LiExpandedDegenerationModels.StandardSystem W
  leftLine : ProjectiveLine P.divisor.left (normalLineModule P)
  rightLine : ProjectiveLine Q.divisor.left (normalLineModule Q)
  leftExpanded : StandardRelativeExpansionModels.StandardSystem P leftLine
  rightExpanded : StandardRelativeExpansionModels.StandardSystem Q rightLine
  central : LiExpandedCentralModels.ModuliModel W expanded N g total

variable {P Q W0 N g total W}
  (E : Environment P Q W0 N g total W) (s : Splitting P Q W0 N g total)

structure GeometricRealization where
  coefficient : Type
  [field : Field coefficient]
  [algebra : Algebra k coefficient]
  [closed : IsAlgClosed coefficient]
  left : LiGluingRelativeTypes.StableFamily P E.leftLine E.leftExpanded s.left
    (Over.mk (Spec.algebraMap k coefficient)) s.leftClass
  right : LiGluingRelativeTypes.StableFamily Q E.rightLine E.rightExpanded s.right
    (Over.mk (Spec.algebraMap k coefficient)) s.rightClass
  roots : RootMatch s.left s.right P Q W0 E.leftLine E.rightLine E.leftExpanded E.rightExpanded
    (Over.mk (Spec.algebraMap k coefficient)) left.obj right.obj

def Realized : Prop := Nonempty (GeometricRealization E s)

/-- The actual finite list is complete and has no repeated root-equivalence class. -/
structure Enumeration where
  count : ℕ
  representative : Fin count → Splitting P Q W0 N g total
  realized : ∀ i, Realized E (representative i)
  injective : Function.Injective (fun i => Quotient.mk
    (splittingSetoid (P := P) (Q := Q) (W0 := W0) (N := N) (g := g) (total := total)) (representative i))
  complete : ∀ s : Splitting P Q W0 N g total, Realized E s →
    ∃ i, Quotient.mk (splittingSetoid (P := P) (Q := Q) (W0 := W0) (N := N) (g := g) (total := total))
      (representative i) = Quotient.mk _ s

def centralAt : LiExpandedCentralModels.ModuliModel W E.expanded (s.leftLegs + s.rightLegs) g total :=
  s.legs.symm ▸ E.central

private theorem centralTransport_stack {a b : ℕ} (h : a = b)
    (C : LiExpandedCentralModels.ModuliModel W E.expanded a g total) :
    (h ▸ C).stack = C.stack := by
  cases h
  rfl

theorem centralAt_stack : (centralAt E s).stack = E.central.stack := by
  exact centralTransport_stack E s.legs.symm E.central

structure Entry where
  left : LiGluingRelativeTypes.ModuliModel P E.leftLine E.leftExpanded s.left s.leftClass
  right : LiGluingRelativeTypes.ModuliModel Q E.rightLine E.rightExpanded s.right s.rightClass
  matching : MatchingModel s.left s.right P Q W0 E.leftLine E.rightLine E.leftExpanded E.rightExpanded
    s.leftClass s.rightClass left right
  gluing : GluingModel s.left s.right P Q W0 E.leftLine E.rightLine E.leftExpanded E.rightExpanded
    s.leftClass s.rightClass left right W E.expanded total s.admissible (centralAt E s) matching

variable (P Q W0 N g total W)

/-- Catalogue geometry is constructed from original inputs, with one central moduli model. -/
structure Catalogue where
  environment : Environment P Q W0 N g total W
  enumeration : Enumeration environment
  entry : ∀ i, Entry environment (enumeration.representative i)

end MathlibExt.AlgebraicGeometry.LiDegenerationCatalogueModels
