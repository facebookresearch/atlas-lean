/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LiExpandedCentralModels
public import MathlibExt.AlgebraicGeometry.LiGluingRelativeTypes

/-!
# Source-qualified expanded geometry and full relative moduli constructors

These requests produce the actual systems defined in MathlibExt. Inputs
are original projective degenerations or relative pairs and native types
and classes. No arbitrary final expansion, moduli family or gluing map is
an input. The providers are deferred; their full proofs are not interface
completion gates.

Source: Jun Li arXiv:math/0009097v1, Sections1--2 and4;
arXiv:math/0110113v1, introduction pp1--4 and Sections1--3.
Primary math/0110113v1 PDF SHA256:
70b4202f5882ae4c0dcc0e80879f043146e84e57dbf3c7c9fa193e5a741dd14b.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LiExpandedGeometryWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open ExpandedTargetChainGeometry RelativeProjectiveLineModels ExpandedTargetGluingModels

def_wanted nativeAdjacentDegenerationTransition (B : Type) [CommRing B] {n : ℕ}
    (i j : Fin (n + 1)) (next : j.val = i.val + 1) :
    LiExpandedDegenerationModels.AdjacentTransition B i j next

def_wanted nativeStandardDegenerationSystem (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {P Q : RelativePair (k := k)} {W0 : SingularTarget P Q}
    (W : LiExpandedDegenerationModels.OneParameter P Q W0) :
    LiExpandedDegenerationModels.StandardSystem W

def_wanted nativeCentralMapModuli (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {P Q : RelativePair (k := k)} {W0 : SingularTarget P Q}
    [LocallyOfFiniteType W0.scheme.hom] [IsNoetherian W0.scheme.left]
    (W : LiExpandedDegenerationModels.OneParameter P Q W0)
    (S : LiExpandedDegenerationModels.StandardSystem W) (n g : ℕ)
    (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left) :
    LiExpandedCentralModels.ModuliModel W S n g beta

def_wanted nativeFullRelativeModuli (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]
    (R : ProjectiveLine P.divisor.left (normalLineModule P))
    (S : StandardRelativeExpansionModels.StandardSystem P R) {n r : ℕ}
    (G : LiGluingRelativeTypes.FullType n r)
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left) :
    LiGluingRelativeTypes.ModuliModel P R S G beta

end WantedExt.AlgebraicGeometry.LiExpandedGeometryWanted
