/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplexPolynomialDiagonal
public import MathlibExt.RingTheory.Kaehler.PolynomialExterior

/-!
# Polynomial diagonal lifts and their actual cotangent images

The original multiplication kernel supplies a finitely supported lift of
the diagonal difference of every polynomial. The diagonal lift represents
the differential of that polynomial after multiplication of its enveloping
coefficients. Consequently a polynomial algebra map has a lift on
Koszul generators whose reduced coordinates are its actual Jacobian.

The lift is chosen from a proved kernel/range equality. Neither a desired
chain comparison nor a desired homology isomorphism is an input.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v v'

namespace MvPolynomial

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "E" => PolynomialEnveloping k σ
local notation "V" => σ →₀ E
local notation "Ω" => KaehlerDifferential k A
local notation "x" => KoszulComplex.finsuppFunctional E (diagonalDifference k σ)

/-- The original diagonal difference of an arbitrary polynomial, in the
same enveloping carrier as the variable diagonal differences. -/
def polynomialOuterDifference (p : A) : E :=
  p ⊗ₜ[k] MulOpposite.op (1 : A) - (1 : A) ⊗ₜ[k] MulOpposite.op p

/-- Multiplication kills every original polynomial diagonal difference. -/
theorem diagonalMultiplication_polynomialOuterDifference (p : A) :
    diagonalMultiplication k σ (polynomialOuterDifference k σ p) = 0 := by
  simp only [polynomialOuterDifference, map_sub, diagonalMultiplication_tmul,
    mul_one, one_mul, sub_self]

/-- The negative of the native tensor derivation has the left-minus-right
sign convention of the original polynomial Koszul functional. -/
def envelopingCotangentLinear : E →ₗ[k] Ω :=
  -(((KaehlerDifferential.D k A).tensorProductTo.restrictScalars k).comp
    (envelopingPlainEquiv k σ).toAlgHom.toLinearMap)

/-- Literal evaluation on the two original enveloping factors. -/
theorem envelopingCotangentLinear_tmul (a b : A) :
    envelopingCotangentLinear k σ (a ⊗ₜ[k] MulOpposite.op b) =
      -(a • KaehlerDifferential.D k A b) := by
  change -((KaehlerDifferential.D k A).tensorProductTo
    (envelopingPlainEquiv k σ (a ⊗ₜ[k] MulOpposite.op b))) = _
  rw [envelopingPlainEquiv_tmul, Derivation.tensorProductTo_tmul]

/-- The original diagonal difference is the actual universal differential. -/
theorem envelopingCotangentLinear_outerDifference (p : A) :
    envelopingCotangentLinear k σ (polynomialOuterDifference k σ p) =
      KaehlerDifferential.D k A p := by
  rw [polynomialOuterDifference, map_sub, envelopingCotangentLinear_tmul,
    envelopingCotangentLinear_tmul]
  simp only [Derivation.map_one_eq_zero, smul_zero, neg_zero, one_smul,
    zero_sub, neg_neg]

/-- The native tensor derivation gives the original multiplication-relative
Leibniz law on the enveloping ring. -/
theorem envelopingCotangentLinear_mul (e z : E) :
    envelopingCotangentLinear k σ (e * z) =
      diagonalMultiplication k σ e • envelopingCotangentLinear k σ z +
        diagonalMultiplication k σ z • envelopingCotangentLinear k σ e := by
  change -((KaehlerDifferential.D k A).tensorProductTo
      (envelopingPlainEquiv k σ (e * z))) =
    (Algebra.TensorProduct.lmul' k) (envelopingPlainEquiv k σ e) •
        (-((KaehlerDifferential.D k A).tensorProductTo (envelopingPlainEquiv k σ z))) +
      (Algebra.TensorProduct.lmul' k) (envelopingPlainEquiv k σ z) •
        (-((KaehlerDifferential.D k A).tensorProductTo (envelopingPlainEquiv k σ e)))
  rw [map_mul, Derivation.tensorProductTo_mul, neg_add, smul_neg, smul_neg]

/-- The actual coefficient of a lifted variable differential. -/
def diagonalCotangentSingle (i : σ) : E →ₗ[k] Ω :=
  (((LinearMap.id : A →ₗ[A] A).smulRight
    (KaehlerDifferential.D k A (MvPolynomial.X i))).restrictScalars k).comp
      (diagonalMultiplication k σ).toLinearMap

/-- Finitely supported diagonal coordinates give their actual universal
differential by multiplying their original enveloping coefficients. -/
def diagonalCotangentCoordinates : V →ₗ[k] Ω :=
  Finsupp.lsum ℕ (diagonalCotangentSingle k σ)

/-- A literal single diagonal coordinate maps to its coefficient times `dX`. -/
theorem diagonalCotangentCoordinates_single (i : σ) (e : E) :
    diagonalCotangentCoordinates k σ (Finsupp.single i e) =
      diagonalMultiplication k σ e • KaehlerDifferential.D k A (MvPolynomial.X i) := by
  rw [diagonalCotangentCoordinates, Finsupp.lsum_single]
  rfl

/-- The diagonal coordinate map is the actual conormal differential of
the original Koszul functional. -/
theorem diagonalCotangentCoordinates_eq :
    diagonalCotangentCoordinates k σ =
      (envelopingCotangentLinear k σ).comp ((x).restrictScalars k) := by
  apply Finsupp.lhom_ext
  intro i e
  rw [diagonalCotangentCoordinates_single, LinearMap.comp_apply]
  change _ = envelopingCotangentLinear k σ
    (Finsupp.linearCombination E (diagonalDifference k σ) (Finsupp.single i e))
  rw [Finsupp.linearCombination_single, smul_eq_mul, envelopingCotangentLinear_mul]
  change _ = diagonalMultiplication k σ e •
    envelopingCotangentLinear k σ (polynomialOuterDifference k σ (MvPolynomial.X i)) +
      diagonalMultiplication k σ (diagonalDifference k σ i) • envelopingCotangentLinear k σ e
  rw [envelopingCotangentLinear_outerDifference, diagonalMultiplication_difference,
    zero_smul, add_zero]

/-- The already proved diagonal multiplication kernel gives a literal
finitely supported lift of every original polynomial difference. -/
theorem exists_diagonalCotangentLift (p : A) :
    ∃ w : V, x w = polynomialOuterDifference k σ p := by
  have h : polynomialOuterDifference k σ p ∈
      KoszulComplex.ideal E V x := by
    rw [KoszulComplex.polynomialDiagonalIdeal_eq_ker_multiplication]
    exact diagonalMultiplication_polynomialOuterDifference k σ p
  exact h

/-- Choose a lift from the earned kernel/range equality. -/
def diagonalCotangentLift (p : A) : V :=
  Classical.choose (exists_diagonalCotangentLift k σ p)

/-- The chosen lift satisfies the original diagonal relation. -/
theorem diagonalCotangentLift_equation (p : A) :
    x (diagonalCotangentLift k σ p) = polynomialOuterDifference k σ p :=
  Classical.choose_spec (exists_diagonalCotangentLift k σ p)

/-- Every lift has the same actual differential coordinates.
This is independent of the choice of a diagonal preimage. -/
theorem diagonalCotangentCoordinates_of_lift (p : A) (w : V)
    (hw : x w = polynomialOuterDifference k σ p) :
    diagonalCotangentCoordinates k σ w = KaehlerDifferential.D k A p := by
  rw [diagonalCotangentCoordinates_eq, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    hw, envelopingCotangentLinear_outerDifference]

/-- The actual chosen diagonal lift reduces to the original polynomial differential. -/
theorem diagonalCotangentLift_coordinates (p : A) :
    diagonalCotangentCoordinates k σ (diagonalCotangentLift k σ p) =
      KaehlerDifferential.D k A p :=
  diagonalCotangentCoordinates_of_lift k σ p _ (diagonalCotangentLift_equation k σ p)

section AlgebraMaps

variable {σ} (τ : Type v') (g : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)

/-- The actual algebra map on the two original enveloping factors. -/
def polynomialEnvelopingMap : PolynomialEnveloping k σ →ₐ[k] PolynomialEnveloping k τ :=
  Algebra.TensorProduct.map g g.op

/-- The original variable diagonal difference maps to the difference of
the actual image polynomial. -/
theorem polynomialEnvelopingMap_difference (i : σ) :
    polynomialEnvelopingMap k τ g (diagonalDifference k σ i) =
      polynomialOuterDifference k τ (g (MvPolynomial.X i)) := by
  have hOp (a : MvPolynomial σ k) : g.op (MulOpposite.op a) = MulOpposite.op (g a) := rfl
  simp only [polynomialEnvelopingMap, diagonalDifference, polynomialOuterDifference,
    map_sub, Algebra.TensorProduct.map_tmul, hOp, map_one]

/-- Multiplication of the two original factors commutes with the actual
algebra map, without changing its coefficient ring. -/
theorem polynomialEnvelopingMap_multiplication (e : PolynomialEnveloping k σ) :
    diagonalMultiplication k τ (polynomialEnvelopingMap k τ g e) =
      g (diagonalMultiplication k σ e) := by
  induction e using TensorProduct.inductionOn with
  | tmul a b =>
      have hb : g.op b = MulOpposite.op (g b.unop) := rfl
      rw [polynomialEnvelopingMap, Algebra.TensorProduct.map_tmul, hb]
      rw [diagonalMultiplication_tmul]
      have h := diagonalMultiplication_tmul k σ a b.unop
      rw [MulOpposite.op_unop] at h
      rw [h, map_mul]
  | add e e' he he' => simp only [map_add, he, he']

/-- A diagonal generator lift for an arbitrary polynomial algebra map. -/
def polynomialDiagonalGeneratorLift (i : σ) : τ →₀ PolynomialEnveloping k τ :=
  diagonalCotangentLift k τ (g (MvPolynomial.X i))

/-- The lift covers the image of the original diagonal generator. -/
theorem polynomialDiagonalGeneratorLift_equation (i : σ) :
    KoszulComplex.finsuppFunctional (PolynomialEnveloping k τ) (diagonalDifference k τ)
      (polynomialDiagonalGeneratorLift k τ g i) =
        polynomialEnvelopingMap k τ g (diagonalDifference k σ i) := by
  rw [polynomialEnvelopingMap_difference]
  exact diagonalCotangentLift_equation k τ _

/-- Reduction of the generator lift is the actual Jacobian
column, expressed intrinsically as the differential of the image polynomial. -/
theorem polynomialDiagonalGeneratorLift_coordinates (i : σ) :
    diagonalCotangentCoordinates k τ (polynomialDiagonalGeneratorLift k τ g i) =
      KaehlerDifferential.D k (MvPolynomial τ k) (g (MvPolynomial.X i)) :=
  diagonalCotangentLift_coordinates k τ _

/-- The actual semilinear image of a single enveloping coefficient times
an original diagonal generator. -/
def polynomialDiagonalGeneratorSingle (i : σ) :
    PolynomialEnveloping k σ →ₛₗ[(polynomialEnvelopingMap k τ g).toRingHom]
      (τ →₀ PolynomialEnveloping k τ) where
  toFun e := polynomialEnvelopingMap k τ g e • polynomialDiagonalGeneratorLift k τ g i
  map_add' e e' := by rw [map_add, add_smul]
  map_smul' e e' := by
    change polynomialEnvelopingMap k τ g (e * e') • polynomialDiagonalGeneratorLift k τ g i =
      polynomialEnvelopingMap k τ g e •
        (polynomialEnvelopingMap k τ g e' • polynomialDiagonalGeneratorLift k τ g i)
    exact (congrArg (fun a : PolynomialEnveloping k τ =>
      a • polynomialDiagonalGeneratorLift k τ g i)
      ((polynomialEnvelopingMap k τ g).map_mul e e')).trans
        (smul_smul (polynomialEnvelopingMap k τ g e)
          (polynomialEnvelopingMap k τ g e') (polynomialDiagonalGeneratorLift k τ g i)).symm

/-- Extend the earned generator lifts semilinearly on the actual free
enveloping coordinate modules. -/
def polynomialDiagonalGeneratorMap :
    (σ →₀ PolynomialEnveloping k σ) →ₛₗ[(polynomialEnvelopingMap k τ g).toRingHom]
      (τ →₀ PolynomialEnveloping k τ) :=
  Finsupp.lsum ℕ (polynomialDiagonalGeneratorSingle k τ g)

/-- Literal evaluation on an original free coordinate. -/
theorem polynomialDiagonalGeneratorMap_single (i : σ) (e : PolynomialEnveloping k σ) :
    polynomialDiagonalGeneratorMap k τ g (Finsupp.single i e) =
      polynomialEnvelopingMap k τ g e • polynomialDiagonalGeneratorLift k τ g i := by
  rw [polynomialDiagonalGeneratorMap, Finsupp.lsum_single]
  rfl

/-- The actual semilinear generator map intertwines the original diagonal
functionals, as required for the full Koszul chain map. -/
theorem polynomialDiagonalGeneratorMap_functional (w : σ →₀ PolynomialEnveloping k σ) :
    KoszulComplex.finsuppFunctional (PolynomialEnveloping k τ) (diagonalDifference k τ)
      (polynomialDiagonalGeneratorMap k τ g w) =
        polynomialEnvelopingMap k τ g
          (KoszulComplex.finsuppFunctional (PolynomialEnveloping k σ)
            (diagonalDifference k σ) w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | single i e =>
      rw [polynomialDiagonalGeneratorMap_single, map_smul,
        polynomialDiagonalGeneratorLift_equation]
      change _ = polynomialEnvelopingMap k τ g
        (Finsupp.linearCombination (PolynomialEnveloping k σ)
          (diagonalDifference k σ) (Finsupp.single i e))
      rw [Finsupp.linearCombination_single]
      change polynomialEnvelopingMap k τ g e *
          polynomialEnvelopingMap k τ g (diagonalDifference k σ i) =
        polynomialEnvelopingMap k τ g (e * diagonalDifference k σ i)
      exact (polynomialEnvelopingMap k τ g).map_mul e (diagonalDifference k σ i) |>.symm

end AlgebraMaps

end MvPolynomial
