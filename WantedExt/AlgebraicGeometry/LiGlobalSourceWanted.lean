/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LiCentralSourceModels
public import MathlibExt.AlgebraicGeometry.LiDegenerationCatalogueModels

/-!
# Full relative/central Li source and admissible-catalogue construction requests

The native construction targets retain actual marked-curve extensions,
universal local target lifts, all full base Cech coefficients (including
mixed and empty source intersections), tensor coefficients, actual
scaling jets and every interpreted family/stabilizer arrow. Their whole
diagram is replaced K-injectively before native right Kan assembly.

The central request constructs the original-parameter derivative and its
actual cone[-1] source. The catalogue supplies the actual admissible
root-equivalence classes and the same central geometry for every term.
No final POT, bundle, virtual class, gluing operator or sum is an input.
Source: Jun Li math/0110113v1 Sections1--3, Proposition2.4, Theorems2.3/2.5/3.15;
math/0009097v1 Sections2 and4, including the empty graph after(4.8).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LiGlobalSourceWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open ExpandedTargetChainGeometry ExpandedTargetGluingModels RelativeProjectiveLineModels
open StandardRelativeExpansionModels LiGluingRelativeTypes LiExpandedDegenerationModels

public def_wanted nativeFullRelativeLiSource (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]
    (R : ProjectiveLine P.divisor.left (normalLineModule P))
    (S : StandardRelativeExpansionModels.StandardSystem P R)
    {n r : ℕ} (G : FullType n r)
    (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
    (M : LiGluingRelativeTypes.ModuliModel P R S G beta) :
    LiRelativeSourceModels.Source P R S G beta M

public def_wanted nativeCentralLiSource (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    [LocallyOfFiniteType W0.scheme.hom] [IsNoetherian W0.scheme.left]
    (W : OneParameter P Q W0) (S : LiExpandedDegenerationModels.StandardSystem W)
    {n g : ℕ} (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (M : LiExpandedCentralModels.ModuliModel W S n g beta) :
    LiCentralSourceModels.Source W S beta M

public def_wanted nativeLiCatalogue (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
    [LocallyOfFiniteType W0.scheme.hom]
    [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
    (n g : ℕ) (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (W : OneParameter P Q W0) :
    LiDegenerationCatalogueModels.Catalogue P Q W0 n g beta W

end WantedExt.AlgebraicGeometry.LiGlobalSourceWanted
