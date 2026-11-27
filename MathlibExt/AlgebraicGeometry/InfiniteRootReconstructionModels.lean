/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CanonicalLogRootArrowModels

/-!
# Reconstruction along the given base map

A root morphism already includes its actual scheme map f. Its source
is the original infinite root of Y and its target the literal pullback
of the original infinite root of X. Preservation tests every root on
every whole geometric fibre. Recovery asks for a unique native log arrow
along f whose canonical original finite-root maps induce the given arrow
up to native invertible modification.

Source: Talpo--Vistoli1410.1164v2, Definitions5.20--5.21 and Theorem5.24.
The scheme base is an input and is never reconstructed from field points.
Constructing the canonical reconstruction for arbitrary root realizations is
left to a separate development: it needs realizations whose evaluated root
comparisons are coherent over the whole tower (identities, composites, base
change and the mixed base/exponent squares), which they do not record.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.InfiniteRootReconstructionModels

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels CanonicalLogRootArrowModels
open InfiniteRootPreservationModels InfiniteRootSectionModels

local instance modificationCategory {S : Scheme.{0}} (A B : Stack S) :
    Category (StackHom A B) :=
  Pseudofunctor.StrongTrans.homCategory (F := A.toPseudofunctor) (G := B.toPseudofunctor)

variable [InverseImageTheory.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  (X Y : LogScheme.{0}) (RX : RootRealization X D I) (RY : RootRealization Y D I)
  [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]

/-- Original native log morphisms along the specified scheme map. -/
def Along (f : Y.scheme ⟶ X.scheme) := {a : EtaleLogSchemes.Hom Y X // a.map = f}

variable (f : Y.scheme ⟶ X.scheme)
  (q : StackHom RY.infinite.stack (baseChanged RX.infinite.stack f))

/-- The canonical finite and infinite map data of the recovered native log arrow. -/
structure Induces (a : Along X Y f) where
  finite : FiniteArrow I D a.val RY RX
  infinite : InfiniteArrow I D a.val RY RX finite
  modification :
    Equiv.cast (congrArg (fun b => StackHom RY.infinite.stack (baseChanged RX.infinite.stack b))
      a.property) infinite.morphism ≅ q

/-- Recovery and uniqueness concern actual log-monoid arrows and their base map. -/
def IsReconstruction : Prop := ∃! a : Along X Y f, Nonempty (Induces I D X Y RX RY f q a)

end MathlibExt.AlgebraicGeometry.InfiniteRootReconstructionModels
