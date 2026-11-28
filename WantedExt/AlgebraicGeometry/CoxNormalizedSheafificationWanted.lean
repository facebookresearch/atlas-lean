/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification

/-!
# Cox's normalized graded-module sheafification

Cox, alg-geom/9210008v3, Proposition 3.1 and Theorem 3.2.
The chart comparison and affine-local sheaf formulas are fixed on actual
characters and homogeneous fractions. The target of essential surjectivity
is quasicoherent modules, with the source's simplicial hypothesis.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoxNormalizedSheafificationWanted

open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification

open CategoryTheory FiniteToricCoordinates CoxGradedSheaves

def_wanted cox_character_chart_comparison {n : ℕ} {F : FiniteFan n}
    (R : Rays F) : ChartComparison R

def_wanted cox_sheafification {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (C : ChartComparison R) (T : Realization ℂ F) : Sheafification R C T

theorem_wanted cox_quasicoherent_essentialSurjectivity {n : ℕ} {F : FiniteFan n}
    (R : Rays F) (h : IsSimplicial R) (C : ChartComparison R) (T : Realization ℂ F)
    (S : Sheafification R C T) (N : T.scheme.left.Modules) (hN : N.IsQuasicoherent) :
    ∃ M : GradedModule R, Nonempty (S.functor.obj M ≅ N)

end WantedExt.AlgebraicGeometry.CoxNormalizedSheafificationWanted
