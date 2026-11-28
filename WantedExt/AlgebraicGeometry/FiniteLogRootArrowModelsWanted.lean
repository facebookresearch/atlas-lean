/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FiniteLogRootArrowModels

/-!
# Native finite-root arrow assembly

The target fixes every original root line, section, tensor, unit,
coefficient arrow and source restriction triangle. These are native
DF operations, before any global root or topos comparison conclusion.
Source: Talpo--Vistoli1410.1164v2, Sections3--5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FiniteLogRootArrowModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open DeligneFaltingsSheaves DenominatorRootFamilies FiniteRootTowers FiniteLogRootArrowModels

public def_wanted nativeFiniteRootArrow (X : Scheme.{0})
    (A B : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A) (E : Structure B)
    (j : A ⟶ B) (c : ComparisonAlong j D E) (n : Exponent) :
    Restriction D E j c n

end WantedExt.AlgebraicGeometry.FiniteLogRootArrowModels
