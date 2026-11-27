/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LiGluingChowModels

/-!
# Sourced geometry and operators for Jun Li's degeneration formula

The geometry constructor takes the original projective one-parameter W,
the actual weighted relative types and their admissible matching/shuffle.
It produces all standard systems, actual moduli realizations, the D^r
matching square and Phi with its exact image. No final geometry is an input.
The Chow constructor explicitly depends on that geometry OUTPUT through
Batteries Wanted, and produces the fixed representative-normalized
external product, the same diagonal refined Gysin and the actual proper
Phi push. Virtual/POT/source comparisons are additional sourced outputs.

Source: Jun Li arXiv:math/0110113v1, pp3--4, equations(3.1)--(3.2),
diagram(3.14), Lemma3.14 and Theorem3.15, pp31--32 and39--40.
Primary PDF SHA256:
70b4202f5882ae4c0dcc0e80879f043146e84e57dbf3c7c9fa193e5a741dd14b.
Curve-class push descent: Stacks Tag02RY and the actual native quotient.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LiGluingGeometryWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open ExpandedTargetChainGeometry ExpandedTargetGluingModels LiGluingRelativeTypes
open LiGluingGeometryModels LiGluingChowModels StackCycleRelations StackChowGroups

def_wanted nativeLiGeometry (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
    [LocallyOfFiniteType W0.scheme.hom]
    [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
    {n n' r g : ℕ} (G : FullType n r) (H : FullType n' r)
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
    (gamma : Fin H.vertices → StableMapNumericalClasses.NumericalClass Q.target.left)
    (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (eta : AdmissibleTriple (g := g) G H P Q W0 beta gamma total)
    (W : LiExpandedDegenerationModels.OneParameter P Q W0) :
    GeometryOutput G H P Q W0 beta gamma total eta W

def_wanted nativeLiChowOperations (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
    [LocallyOfFiniteType W0.scheme.hom]
    [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
    {n n' r g : ℕ} (G : FullType n r) (H : FullType n' r)
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
    (gamma : Fin H.vertices → StableMapNumericalClasses.NumericalClass Q.target.left)
    (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (eta : AdmissibleTriple (g := g) G H P Q W0 beta gamma total)
    (W : LiExpandedDegenerationModels.OneParameter P Q W0)
    (D : StackCycleRelations.CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
    (K : KreschPresentation D) :
    let O := ❰nativeLiGeometry❱ k P Q W0 G H beta gamma total eta W
    ChowOperations D K G H P Q W0 O.leftLine O.rightLine O.leftExpanded O.rightExpanded
      beta gamma O.leftModuli O.rightModuli O.matching W O.expanded total eta O.centralModuli O.gluing

end WantedExt.AlgebraicGeometry.LiGluingGeometryWanted
