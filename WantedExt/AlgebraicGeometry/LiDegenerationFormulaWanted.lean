/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.AlgebraicGeometry.LiGlobalSourceWanted
import all WantedExt.AlgebraicGeometry.LiGlobalSourceWanted
public import MathlibExt.AlgebraicGeometry.LiDegenerationVirtualCatalogueModels

/-!
# Source-produced virtual recipes and the actual weighted degeneration identity

The original projective degeneration, numerical type and actual total
numerical class are the geometric inputs. The catalogue, both relative
sources, central original-parameter fibre source, full global POT/bundle/
cone/virtual recipes, and actual matching/Phi Chow operations are all
construction outputs. The final proof request uses those same outputs.

The sum is the complete actual root-equivalence catalogue. Every term
uses the computed m/|Eq| coefficient, same ML x MR external product,
same D^r diagonal refined Gysin and actual proper Phi push, with empty
branches and r=0 included. No final virtual class or operator is an input.

Source: Jun Li math/0110113v1, equations(3.2)/(3.14), Theorem3.15,
printed pp39--40; source constructions Sections1--2 and Proposition2.4.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LiDegenerationFormulaWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open ExpandedTargetChainGeometry ExpandedTargetGluingModels LiExpandedDegenerationModels
open StackCycleRelations StackChowGroups
open WantedExt.AlgebraicGeometry.LiGlobalSourceWanted

public def_wanted nativeLiVirtualCatalogue (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
    [LocallyOfFiniteType W0.scheme.hom]
    [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
    (n g : ℕ) (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (W : OneParameter P Q W0)
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (Z : RubberVirtualClassModels.Point D K) :
    LiDegenerationVirtualCatalogueModels.VirtualCatalogue
      (❰nativeLiCatalogue❱ k P Q W0 n g beta W) D K Z

public theorem_wanted nativeLiDegenerationFormula (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
    [LocallyOfFiniteType W0.scheme.hom]
    [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
    (n g : ℕ) (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (W : OneParameter P Q W0)
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (Z : RubberVirtualClassModels.Point D K) :
    let C := ❰nativeLiCatalogue❱ k P Q W0 n g beta W
    LiDegenerationVirtualCatalogueModels.Identity C D K Z
      (❰nativeLiVirtualCatalogue❱ k P Q W0 n g beta W D K Z)

end WantedExt.AlgebraicGeometry.LiDegenerationFormulaWanted
