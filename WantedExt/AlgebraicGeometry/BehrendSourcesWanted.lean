/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StackBehrendModels
public import MathlibExt.AlgebraicGeometry.CriticalMilnorFibreModels

/-!
# Ordinary cone, Nash, Segre and canonical Behrend source requests

All construction requests return the normalized native models.
The scheme weight is computed from its distinguished normal-cone
cycle and the actual Nash Chern–Segre degree; the stack weight has
genuine smooth-atlas descent. Critical normalization uses the actual
df ideal and nearby-level coordinate-ball fibre. No arbitrary
weight/Euler function or orientation hypothesis is introduced.

References: Behrend, arXiv:math/0507523v2, §1.1–1.2,
equations (3)–(4), Proposition 1.1 and Definition 1.4;
Bridgeland, arXiv:1002.4374v3, Theorem 5.1, equation (25).
Generic upstream Chern/Chow producers are source integration from
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Apache 2.0. Actual native formulas are defined in the imported modules.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BehrendSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open IntegralChowChernModels GradedConeProjectiveModels OrdinaryNormalConeModels
open NashBlowupModels ConeSegreOperations BehrendEulerObstructionModels
open StackBehrendModels CriticalMilnorFibreModels ConstructibleEulerCharacteristics
open ComplexAnalytification GeometricHallStackFunctions

def_wanted actual_normal_rees_grading {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (P : _root_.Algebra.Extension.{0} A B) : NormalGrading P

def_wanted actual_ordinary_normal_cone {X M : SchemeData} (i : X.scheme ⟶ M.scheme)
    [IsClosedImmersion i.left] : OrdinaryNormalCone i

def_wanted actual_distinguished_image_dimensions {X M : SchemeData}
    {i : X.scheme ⟶ M.scheme} (N : OrdinaryNormalCone i) : DistinguishedDimension N

def_wanted actual_graded_cone_completion {X : SchemeData} (C : GlobalGradedCone X) :
    GlobalCompletion C

def_wanted actual_integral_cone_segre {X : SchemeData} (C : GlobalGradedCone X) : SegreData C

def_wanted actual_quotient_grassmannian (V : SchemeData) (d : ℕ) : QuotientGrassmannian V d

def_wanted actual_nash_blowup (V : SchemeData) (I : IntegralDimension V) :
    {N : NashModel V // N.dimension=I}

theorem_wanted actual_nash_point_fibre {V : SchemeData} (N : NashModel V) (p : space V.scheme) :
    FibreGeometry N p

def_wanted actual_euler_obstruction (V : SchemeData) (I : IntegralDimension V) :
    {D : EulerObstructionData V // D.nash.dimension=I}

def_wanted actual_prime_closure_euler (X : SchemeData) (x : X.scheme.left) : PrimeEulerData X x

def_wanted actual_scheme_behrend (X : SchemeData) : SchemeBehrendModel X

def_wanted actual_artin_behrend (M : LocallyFiniteTypeStack) : StackBehrendModel M

def_wanted actual_critical_derivative_ideal (M : SchemeData) [Smooth M.scheme.hom]
    (f : Γ(M.scheme.left, ⊤)) : CriticalIdealModel M f

def_wanted actual_critical_coordinate_neighbourhood {X : SchemeData}
    (C : CriticalChart X) (p : space X.scheme) : CriticalNeighbourhood C p

theorem_wanted actual_behrend_milnor_normalization {X : SchemeData}
    (C : CriticalChart X) (W : SchemeBehrendModel X) (p : space X.scheme)
    (U : CriticalNeighbourhood C p) : MilnorNormalization C W p U

theorem_wanted actual_smooth_euler_obstruction (V : SchemeData) [Smooth V.scheme.hom]
    (D : EulerObstructionData V) (p : space V.scheme) : eulerObstruction D p=1

theorem_wanted actual_smooth_behrend (X : SchemeData) (r : ℕ)
    [SmoothOfRelativeDimension r X.scheme.hom] (W : SchemeBehrendModel X)
    (p : space X.scheme) : W.value p=(-1 : ℤ)^r

theorem_wanted actual_behrend_chart_independence (X : SchemeData)
    (A B : SchemeBehrendModel X) : A.value=B.value

def_wanted actual_weighted_generator_presentation {M : LocallyFiniteTypeStack}
    (W : StackBehrendModel M) (g : Generator M.stack) (S : SchemeSource g.source) :
    EulerPresentation S.scheme (pulledStackWeight W g S)

end WantedExt.AlgebraicGeometry.BehrendSources
