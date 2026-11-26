/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HallSemiclassicalOperations
public import MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics

/-!
# Actual Hall correspondence, semiclassical and Euler source requests

Each request constructs a normalized source model or proves a property
of the already computed geometric operation. In particular division
uses the actual BG_m product, not a scalar supplied to satisfy the
Poisson identities. Canonical Behrend weights and their integration
normalization are separate constructions.

References: Bridgeland, arXiv:1002.4374v3, equations (15), (24)–(25),
Theorem 5.1 and the corrected regular coefficient ring in §7.3,
equation (50); arXiv:1002.4372v1, §3.3; Behrend,
arXiv:math/0507523v2, §1.2. Native coherent-stack source:
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Quot/CoherentStackCategory.lean, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HallConvolutionSources

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallConvolutionOperations
open HallSemiclassicalOperations ConstructibleEulerCharacteristics
open HallProjectiveInverseModels
open StablePairFamilies ComplexAnalytification

def_wanted actual_hall_family_stacks (X : Over (Spec (.of ℂ))) (HX : Threefold X) :
    HallStacks X

def_wanted actual_exact_sequence_convolutions {X : Over (Spec (.of ℂ))}
    (HX : Threefold X) (H : HallStacks X) : ConvolutionModels H

theorem_wanted actual_geometric_convolution_descent {X : Over (Spec (.of ℂ))}
    (HX : Threefold X) {H : HallStacks X} (D : ConvolutionModels H) : ConvolutionDescent D

theorem_wanted actual_lefschetz_descent (M : ComplexStack)
    (L : ∀ g : Generator M, LefschetzProduct g) : LefschetzDescent L

theorem_wanted actual_geometric_scalar_descent {M : ComplexStack} {A : FiniteTypeStack}
    (P : ScalarProductModels M A) : ScalarDescent P

def_wanted actual_classifying_line_stack : ClassifyingLineStackModel

def_wanted actual_projective_space_inverse (k : ℕ) : ProjectiveInverseModel k

theorem_wanted actual_projective_space_inverse_action (M : ComplexStack) (k : ℕ)
    (J : ProjectiveInverseModel k) (P : ScalarProductModels M J.projectiveStack)
    (Q : ScalarProductModels M J.inverseStack) (hP : ScalarDescent P) (hQ : ScalarDescent Q)
    (a : LefschetzStackFunctions M) : scalarAction hP (scalarAction hQ a) = a

variable {X : Over (Spec (.of ℂ))} {H : HallStacks X} {D : ConvolutionModels H}
  {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
  {hL : LefschetzDescent L}

theorem_wanted actual_regular_hall_closure (HX : Threefold X) : RegularClosure h hL

def_wanted actual_regular_divided_commutator (HX : Threefold X)
    (C : RegularClosure h hL) : DividedCommutatorData C

theorem_wanted geometric_line_stack_inverse {C : RegularClosure h hL}
    (B : DividedCommutatorData C) (a : LefschetzStackFunctions H.moduli) :
    lefschetz hL (scalarAction B.descent a) - scalarAction B.descent a = a

theorem_wanted divided_commutator_normalization {C : RegularClosure h hL}
    (B : DividedCommutatorData C) (a b : Regular H.moduli) :
    regularLefschetz C (dividedCommutator B a b) - dividedCommutator B a b =
      regularMultiplication C a b - regularMultiplication C b a

theorem_wanted actual_semiclassical_product_descent (C : RegularClosure h hL) :
    SemiclassicalMultiplicationDescent C

theorem_wanted actual_semiclassical_bracket_descent {C : RegularClosure h hL}
    (B : DividedCommutatorData C) : SemiclassicalBracketDescent B

theorem_wanted actual_convolution_associative
    (a b c : LefschetzStackFunctions H.moduli) :
    convolution h (convolution h a b) c = convolution h a (convolution h b c)

theorem_wanted actual_semiclassical_commutative {C : RegularClosure h hL}
    (S : SemiclassicalMultiplicationDescent C) (a b : Semiclassical C) :
    semiclassicalMultiplication S a b = semiclassicalMultiplication S b a

theorem_wanted actual_semiclassical_jacobi {C : RegularClosure h hL}
    {B : DividedCommutatorData C} (S : SemiclassicalBracketDescent B)
    (a b c : Semiclassical C) :
    semiclassicalBracket S a (semiclassicalBracket S b c) +
      semiclassicalBracket S b (semiclassicalBracket S c a) +
      semiclassicalBracket S c (semiclassicalBracket S a b) = 0

theorem_wanted actual_semiclassical_leibniz {C : RegularClosure h hL}
    {B : DividedCommutatorData C} (M : SemiclassicalMultiplicationDescent C)
    (S : SemiclassicalBracketDescent B) (a b c : Semiclassical C) :
    semiclassicalBracket S a (semiclassicalMultiplication M b c) =
      semiclassicalMultiplication M (semiclassicalBracket S a b) c +
        semiclassicalMultiplication M b (semiclassicalBracket S a c)

def_wanted finite_compact_support_betti (Y : IntegerSchemeChow.FieldScheme ℂ)
    [IsSeparated Y.scheme.hom] : FiniteCompactBetti (space Y.scheme)

theorem_wanted compact_euler_bound_independence (Z : TopCat.{0})
    (A B : FiniteCompactBetti Z) : compactEuler A = compactEuler B

theorem_wanted weighted_euler_presentation_independence
    (Y : IntegerSchemeChow.FieldScheme ℂ) [IsSeparated Y.scheme.hom]
    (f : space Y.scheme → ℤ) (A B : EulerPresentation Y.scheme f) :
    weightedEuler A = weightedEuler B

end WantedExt.AlgebraicGeometry.HallConvolutionSources
