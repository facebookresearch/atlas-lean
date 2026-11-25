/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CoxDivisorialModules

/-!
# Cox divisorial shift normalization and exactness

Reference: Cox, alg-geom/9210008v3, Proposition 3.1 and formula (5), pp11–12.
All fans retain spanning rays; simpliciality is not needed for these statements.
The target O(D) is defined by its Laurent character modules and face maps,
independently of the claimed Cox shift comparison. No line-bundle hypothesis
is imposed on an arbitrary invariant Weil divisor.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoxDivisorialModulesWanted

open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.CoxDivisorialModules

open CategoryTheory _root_.AlgebraicGeometry FiniteToricCoordinates CoxGradedSheaves
  CoxNormalizedSheafification

def_wanted toric_divisorial_sheaf {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (T : Realization ℂ F) (D : InvariantDivisor R) : DivisorialSheaf R T D

def_wanted cox_shift_chart_comparison {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (C : ChartComparison R) (σ : F.Face) (D : InvariantDivisor R) :
    ShiftChartComparison R C σ D

def_wanted cox_shift_divisor_comparison {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (C : ChartComparison R) (T : Realization ℂ F) (S : Sheafification R C T)
    (D : InvariantDivisor R) (O : DivisorialSheaf R T D)
    (J : ∀ σ : F.Face, ShiftChartComparison R C σ D) :
    {e : O.sheaf ≅ S.functor.obj (shiftedPolynomial R (divisorClass R D)) //
      ∀ σ : F.Face,
        (Scheme.Modules.pullback (T.chartMap σ).left).map e.hom ≫
          (S.localIso σ _).hom = (O.localIso σ).hom ≫ (J σ).sheafIso.hom}

theorem_wanted cox_sheafification_exact {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (C : ChartComparison R) (T : Realization ℂ F) (S : Sheafification R C T)
    (M N P : GradedModule R) (f : M ⟶ N) (g : N ⟶ P)
    (h : Function.Exact f.map g.map) :
    ∃ hzero : S.functor.map f ≫ S.functor.map g = 0,
      (ShortComplex.mk (S.functor.map f) (S.functor.map g) hzero).Exact

end WantedExt.AlgebraicGeometry.CoxDivisorialModulesWanted
