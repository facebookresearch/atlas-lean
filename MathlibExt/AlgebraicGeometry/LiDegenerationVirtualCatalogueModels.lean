/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiCentralSourceModels
public import MathlibExt.AlgebraicGeometry.LiDegenerationCatalogueModels
public import MathlibExt.AlgebraicGeometry.LiSourceQualifiedVirtualModels
public import MathlibExt.AlgebraicGeometry.LiQualifiedDGVirtualModels

/-!
# Source-qualified virtual outputs for the actual degeneration catalogue

Every source, POT, bundle, cone, virtual recipe and Chow correspondence is
an OUTPUT of one construction on the original degeneration/type/class.
The central source is the original-parameter homotopy fibre. Relative
sources retain empty branches and one target on every disconnected curve.

Each summand uses its actual two virtual recipes, their actual product,
the same matching-evaluation diagonal Gysin, and its actual proper Phi.
The coefficient is the computed contact product divided by the actual
root-equivalence group order. The sum ranges over the source-qualified
complete finite root-equivalence catalogue, with one fixed central model.

Source: Jun Li math/0110113v1, (3.2)/(3.14), Theorem3.15 pp39--40;
Proposition2.4 and Theorems2.3/2.5 for the source virtual recipes.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiDegenerationVirtualCatalogueModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry StackCycleRelations StackChowGroups StackBundleCones
open ExpandedTargetChainGeometry ExpandedTargetGluingModels LiExpandedDegenerationModels
open LiDegenerationCatalogueModels
open scoped BigOperators

variable {k : Type} [Field k] {P Q : RelativePair (k := k)} {W0 : SingularTarget P Q}
  [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
  [LocallyOfFiniteType W0.scheme.hom]
  [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
  {n g : ℕ} {beta : StableMapNumericalClasses.NumericalClass W0.scheme.left}
  {W : OneParameter P Q W0}
  (C : Catalogue P Q W0 n g beta W)
  (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
  (Z : RubberVirtualClassModels.Point D K)

/-- Source/virtual/correspondence data are constructed together, with no final-class input. -/
structure VirtualCatalogue where
  centralSource : LiCentralSourceModels.Source W C.environment.expanded beta C.environment.central
  central : LiSourceQualifiedVirtualModels.VirtualData centralSource.parentModel D K C.environment.central.finiteType Z
  centralDG : LiQualifiedDGVirtualModels.Central centralSource central
  leftSource : ∀ i,
    LiRelativeSourceModels.Source P C.environment.leftLine C.environment.leftExpanded
      (C.enumeration.representative i).left (C.enumeration.representative i).leftClass (C.entry i).left
  rightSource : ∀ i,
    LiRelativeSourceModels.Source Q C.environment.rightLine C.environment.rightExpanded
      (C.enumeration.representative i).right (C.enumeration.representative i).rightClass (C.entry i).right
  left : ∀ i, LiSourceQualifiedVirtualModels.VirtualData (leftSource i).assembly.parentModel D K (C.entry i).left.finiteType Z
  right : ∀ i, LiSourceQualifiedVirtualModels.VirtualData (rightSource i).assembly.parentModel D K (C.entry i).right.finiteType Z
  leftDG : ∀ i, LiQualifiedDGVirtualModels.Relative (leftSource i) (left i)
  rightDG : ∀ i, LiQualifiedDGVirtualModels.Relative (rightSource i) (right i)
  operations : ∀ i,
    LiGluingChowModels.ChowOperations D K
      (C.enumeration.representative i).left (C.enumeration.representative i).right
      P Q W0 C.environment.leftLine C.environment.rightLine C.environment.leftExpanded C.environment.rightExpanded
      (C.enumeration.representative i).leftClass (C.enumeration.representative i).rightClass
      (C.entry i).left (C.entry i).right (C.entry i).matching W C.environment.expanded beta
      (C.enumeration.representative i).admissible (centralAt C.environment (C.enumeration.representative i))
      (C.entry i).gluing
  degree : ∀ i, (0 - (left i).bundle.virtualRank) + (0 - (right i).bundle.virtualRank) -
    ((operations i).diagonal.dimension : ℤ) = 0 - central.bundle.virtualRank

def transportClass {X Y : Stack (Spec (.of k))} {hX : FiniteTypeArtin k X} {hY : FiniteTypeArtin k Y}
    {d e : ℤ} (stack : X = Y) (degree : d = e) (x : RationalChowGroup D K X hX d) :
    RationalChowGroup D K Y hY e := by
  cases stack
  cases degree
  exact x

variable (V : VirtualCatalogue C D K Z)

def summand (i : Fin C.enumeration.count) :
    RationalChowGroup D K C.environment.central.stack C.environment.central.finiteType
      (0 - V.central.bundle.virtualRank) :=
  transportClass D K (centralAt_stack C.environment (C.enumeration.representative i)) (V.degree i)
    (LiGluingChowModels.weightedTerm D K
      (C.enumeration.representative i).left (C.enumeration.representative i).right
      P Q W0 C.environment.leftLine C.environment.rightLine C.environment.leftExpanded C.environment.rightExpanded
      (C.enumeration.representative i).leftClass (C.enumeration.representative i).rightClass
      (C.entry i).left (C.entry i).right (C.entry i).matching W C.environment.expanded beta
      (C.enumeration.representative i).admissible (centralAt C.environment (C.enumeration.representative i))
      (C.entry i).gluing (V.operations i)
      (0 - (V.left i).bundle.virtualRank) (0 - (V.right i).bundle.virtualRank)
      (LiSourceQualifiedVirtualModels.virtualClass
        (L := (V.leftSource i).assembly.parentModel) (D := D) (K := K)
        (hX := (C.entry i).left.finiteType) (Z := Z) (V.left i))
      (LiSourceQualifiedVirtualModels.virtualClass
        (L := (V.rightSource i).assembly.parentModel) (D := D) (K := K)
        (hX := (C.entry i).right.finiteType) (Z := Z) (V.right i)))

def sum : RationalChowGroup D K C.environment.central.stack C.environment.central.finiteType
    (0 - V.central.bundle.virtualRank) :=
  ∑ i : Fin C.enumeration.count, summand C D K Z V i

/-- The literal source-qualified virtual degeneration identity. -/
def Identity : Prop := LiSourceQualifiedVirtualModels.virtualClass
  (L := V.centralSource.parentModel) (D := D) (K := K)
  (hX := C.environment.central.finiteType) (Z := Z) V.central = sum C D K Z V

end MathlibExt.AlgebraicGeometry.LiDegenerationVirtualCatalogueModels
