/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricHallStackFunctions
public import MathlibExt.AlgebraicGeometry.HallExactSequenceFamilies
public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels

/-!
# Native geometric Hall and integral Chern source-comparison requests

Every source model retains the actual scheme/stack, complete family
categories and native ring/cycle maps. These requests concern their
construction, descent and source comparison. They supply no arbitrary
Hall ring, Behrend weight, integration map or virtual-class function.

References: Bridgeland, arXiv:1002.4374v3, §4.1 and §5.1;
Behrend, arXiv:math/0507523v2, §1.1–1.2;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Quot/CoherentStackCategory.lean, Chow/GenuineChern/Classes.lean,
BivariantChernClass.lean and Chow/Bivariant/TotalChernClass.lean,
Apache 2.0. Generic source constructions are completed upstream;
these are native source-integration and normalization requests.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HallGeometricFoundations

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeometricHallStackFunctions IntegralChowChernModels
open StablePairFamilies AlgebraicBundleGeometry CoherentCurveLinearSeries

def_wanted finite_scheme_stack (U : IntegerSchemeChow.FieldScheme ℂ) :
    Σ A : FiniteTypeStack, {S : SchemeSource A // S.scheme = U.scheme}

def_wanted finite_stack_product (X Y : FiniteTypeStack) : ProductModel X Y

def_wanted actual_lefschetz_product (M : ComplexStack) (g : Generator M) : LefschetzProduct g

theorem_wanted integral_proper_push_descent {X Y : SchemeData}
    (f : X.scheme ⟶ Y.scheme) [IsProper f.left] : ProperPushDescent f

theorem_wanted integral_smooth_pull_descent {X Y : SchemeData}
    (f : Y.scheme ⟶ X.scheme) (r : ℕ) [SmoothOfRelativeDimension r f.left] :
    SmoothPullDescent f r

def_wanted actual_line_total_space (X : SchemeData) (L : X.scheme.left.Modules) (hL : IsLine L) :
    LineTotalModel X L

def_wanted actual_line_chow_homotopy {X : SchemeData} {L : X.scheme.left.Modules}
    (V : LineTotalModel X L) : LineChowComparison V

def_wanted actual_projective_quotient_model (X : SchemeData) (E : X.scheme.left.Modules)
    (r : ℕ) (hr : 0 < r) (hE : IsBundle E r) : ProjectiveModel X E r

def_wanted actual_projective_chern_data (X : SchemeData) (E : X.scheme.left.Modules)
    (r : ℕ) (hr : 0 < r) (hE : IsBundle E r) : ProjectiveChernData X E r

def_wanted actual_all_rank_chern_construction (X : SchemeData) (E : X.scheme.left.Modules)
    (r : ℕ) (hE : IsBundle E r) : ChernConstruction X E r

theorem_wanted coherent_low_dimension_cohomology
    (X : Over (Spec (.of ℂ))) (HX : Threefold X)
    (F : HallExactSequenceFamilies.CoherentObject X) :
    FiniteDimensional ℂ (cohomology X.hom F.val 0) ∧
      FiniteDimensional ℂ (cohomology X.hom F.val 1) ∧
        ∀ n : ℕ, 1 < n → IsZero (cohomology X.hom F.val n)

theorem_wanted coherent_curve_numerical_profile
    (X : Over (Spec (.of ℂ))) (HX : Threefold X)
    (F : HallExactSequenceFamilies.CoherentObject X) :
    HallExactSequenceFamilies.sheafCurveDegrees X HX F ∈ HallExactSequenceFamilies.CurveLattice X

end WantedExt.AlgebraicGeometry.HallGeometricFoundations
