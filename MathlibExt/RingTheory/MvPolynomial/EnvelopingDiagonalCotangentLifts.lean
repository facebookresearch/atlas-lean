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
# Diagonal lifts and polynomial differentials

For a commutative ring `k` and a type `σ`, let `A = k[σ]`, `E = A ⊗[k] Aᵐᵒᵖ`, and `µ(a ⊗
op(b)) = a*b`. Define `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)` and `F(w) = ∑ i, w_i δ_i` for `w : σ
→₀ E`.

Every polynomial difference `Δp = p ⊗ op(1) - 1 ⊗ op(p)` has a finitely supported lift `w`
with `F(w) = Δp`. The cotangent reduction is `C(w) = ∑ i, µ(w_i) dX_i`, and every such lift
satisfies `C(w) = dp`.

For a polynomial algebra map `g : k[σ] →ₐ[k] k[τ]`, chosen lifts of `Δ(g X_i)` extend to a
semilinear map on free enveloping-coordinate modules. It intertwines the diagonal functionals.
Its cotangent reductions are `d(g X_i)`, with coefficients `∂g(X_i)/∂X_j` in the target
variable basis.

References: Loday, *Cyclic Homology*, Sections 1.1 and 3.2; Hochschild, Kostant and Rosenberg,
*Differential forms on regular affine algebras*, Transactions of the AMS 102 (1962), 383–408.
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

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `p : A`, `polynomialOuterDifference k σ p` is `Δp = p ⊗ op(1) - 1 ⊗ op(p)` in `E`. -/
def polynomialOuterDifference (p : A) : E :=
  p ⊗ₜ[k] MulOpposite.op (1 : A) - (1 : A) ⊗ₜ[k] MulOpposite.op p

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For every `p : A`, diagonal multiplication `µ(a ⊗ op(b)) = a*b` satisfies
`µ(polynomialOuterDifference k σ p) = 0`. -/
theorem diagonalMultiplication_polynomialOuterDifference (p : A) :
    diagonalMultiplication k σ (polynomialOuterDifference k σ p) = 0 := by
  simp only [polynomialOuterDifference, map_sub, diagonalMultiplication_tmul,
    mul_one, one_mul, sub_self]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. This is the `k`-linear map `θ : E → Ω¹(A/k)` defined by `θ(a ⊗ op(b)) = -a db`. The
negative sign makes `θ(p ⊗ op(1) - 1 ⊗ op(p)) = dp`. -/
def envelopingCotangentLinear : E →ₗ[k] Ω :=
  -(((KaehlerDifferential.D k A).tensorProductTo.restrictScalars k).comp
    (envelopingPlainEquiv k σ).toAlgHom.toLinearMap)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `a,b : A`, `envelopingCotangentLinear k σ (a ⊗ op(b)) = -(a • D k A b)` in
`Ω¹(A/k)`. -/
theorem envelopingCotangentLinear_tmul (a b : A) :
    envelopingCotangentLinear k σ (a ⊗ₜ[k] MulOpposite.op b) =
      -(a • KaehlerDifferential.D k A b) := by
  change -((KaehlerDifferential.D k A).tensorProductTo
    (envelopingPlainEquiv k σ (a ⊗ₜ[k] MulOpposite.op b))) = _
  rw [envelopingPlainEquiv_tmul, Derivation.tensorProductTo_tmul]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For every `p : A`, the map `θ(a ⊗ op(b)) = -a db` satisfies
`θ(polynomialOuterDifference k σ p) = D k A p`. -/
theorem envelopingCotangentLinear_outerDifference (p : A) :
    envelopingCotangentLinear k σ (polynomialOuterDifference k σ p) =
      KaehlerDifferential.D k A p := by
  rw [polynomialOuterDifference, map_sub, envelopingCotangentLinear_tmul,
    envelopingCotangentLinear_tmul]
  simp only [Derivation.map_one_eq_zero, smul_zero, neg_zero, one_smul,
    zero_sub, neg_neg]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For `e,z : E`, the signed cotangent map
satisfies `θ(e*z) = µ(e) • θ(z) + µ(z) • θ(e)`, where `θ = envelopingCotangentLinear k σ` and
the coefficients act on `Ω` as elements of `A`. -/
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

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For `i : σ`, this is the `k`-linear map `E
→ Ω` with `e ↦ µ(e) • D k A (X_i)`. -/
def diagonalCotangentSingle (i : σ) : E →ₗ[k] Ω :=
  (((LinearMap.id : A →ₗ[A] A).smulRight
    (KaehlerDifferential.D k A (MvPolynomial.X i))).restrictScalars k).comp
      (diagonalMultiplication k σ).toLinearMap

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. The `k`-linear map `C : V → Ω` sends `w`
to `∑ i ∈ supp(w), µ(w_i) • D k A (X_i)`. -/
def diagonalCotangentCoordinates : V →ₗ[k] Ω :=
  Finsupp.lsum ℕ (diagonalCotangentSingle k σ)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For `i : σ` and `e : E`,
`diagonalCotangentCoordinates k σ (Finsupp.single i e) = µ(e) • D k A (X_i)`. -/
theorem diagonalCotangentCoordinates_single (i : σ) (e : E) :
    diagonalCotangentCoordinates k σ (Finsupp.single i e) =
      diagonalMultiplication k σ e • KaehlerDifferential.D k A (MvPolynomial.X i) := by
  rw [diagonalCotangentCoordinates, Finsupp.lsum_single]
  rfl

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. The cotangent coordinate map equals the
composite `C = θ ∘ F`, where `θ(a ⊗ op(b)) = -a db`. In code, `diagonalCotangentCoordinates k
σ = (envelopingCotangentLinear k σ).comp (F.restrictScalars k)`. -/
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

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For every `p : A`, there exists `w : V`
with `F(w) = p ⊗ op(1) - 1 ⊗ op(p)`. Thus the polynomial diagonal difference is an
enveloping-linear combination of the variable diagonal differences. -/
theorem exists_diagonalCotangentLift (p : A) :
    ∃ w : V, x w = polynomialOuterDifference k σ p := by
  have h : polynomialOuterDifference k σ p ∈
      KoszulComplex.ideal E V x := by
    rw [KoszulComplex.polynomialDiagonalIdeal_eq_ker_multiplication]
    exact diagonalMultiplication_polynomialOuterDifference k σ p
  exact h

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For each `p : A`, choose a finitely
supported vector `w_p : V` satisfying `F(w_p) = p ⊗ op(1) - 1 ⊗ op(p)`. The function
`diagonalCotangentLift k σ` returns this chosen preimage. -/
def diagonalCotangentLift (p : A) : V :=
  Classical.choose (exists_diagonalCotangentLift k σ p)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For every `p : A`,
`F(diagonalCotangentLift k σ p) = p ⊗ op(1) - 1 ⊗ op(p)`. -/
theorem diagonalCotangentLift_equation (p : A) :
    x (diagonalCotangentLift k σ p) = polynomialOuterDifference k σ p :=
  Classical.choose_spec (exists_diagonalCotangentLift k σ p)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. If `p : A` and `w : V` satisfy `F(w) = p ⊗
op(1) - 1 ⊗ op(p)`, then `diagonalCotangentCoordinates k σ w = D k A p`. -/
theorem diagonalCotangentCoordinates_of_lift (p : A) (w : V)
    (hw : x w = polynomialOuterDifference k σ p) :
    diagonalCotangentCoordinates k σ w = KaehlerDifferential.D k A p := by
  rw [diagonalCotangentCoordinates_eq, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    hw, envelopingCotangentLinear_outerDifference]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For every `p : A`,
`diagonalCotangentCoordinates k σ (diagonalCotangentLift k σ p) = D k A p`. -/
theorem diagonalCotangentLift_coordinates (p : A) :
    diagonalCotangentCoordinates k σ (diagonalCotangentLift k σ p) =
      KaehlerDifferential.D k A p :=
  diagonalCotangentCoordinates_of_lift k σ p _ (diagonalCotangentLift_equation k σ p)

section AlgebraMaps

variable {σ} (τ : Type v') (g : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. This is the `k`-algebra homomorphism `F_g`, with `a ⊗ op(b) ↦ g(a) ⊗ op(g(b))`. -/
def polynomialEnvelopingMap : PolynomialEnveloping k σ →ₐ[k] PolynomialEnveloping k τ :=
  Algebra.TensorProduct.map g g.op

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, `F_g(δ_i) = Δ(g(X_i))`, where `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)` and
`Δp = p ⊗ op(1) - 1 ⊗ op(p)` in the appropriate enveloping algebra. -/
theorem polynomialEnvelopingMap_difference (i : σ) :
    polynomialEnvelopingMap k τ g (diagonalDifference k σ i) =
      polynomialOuterDifference k τ (g (MvPolynomial.X i)) := by
  have hOp (a : MvPolynomial σ k) : g.op (MulOpposite.op a) = MulOpposite.op (g a) := rfl
  simp only [polynomialEnvelopingMap, diagonalDifference, polynomialOuterDifference,
    map_sub, Algebra.TensorProduct.map_tmul, hOp, map_one]

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `e : E_σ`, `µ_τ(F_g e) = g(µ_σ e)`, where `µ_σ,µ_τ` are the diagonal
multiplication augmentations. -/
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

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, choose `L_i : τ →₀ E_τ` with `F_τ(L_i) = Δ(g(X_i))`, where `F_τ(w)
= ∑ j, w_j δ_j`. This chosen target diagonal vector is `polynomialDiagonalGeneratorLift k τ g
i`. -/
def polynomialDiagonalGeneratorLift (i : σ) : τ →₀ PolynomialEnveloping k τ :=
  diagonalCotangentLift k τ (g (MvPolynomial.X i))

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, the target diagonal functional satisfies
`F_τ(polynomialDiagonalGeneratorLift k τ g i) = F_g(δ_i)`. Here `F_τ(w) = ∑ j, w_j δ_j` and
`δ_i` is the source left-minus-right variable difference. -/
theorem polynomialDiagonalGeneratorLift_equation (i : σ) :
    KoszulComplex.finsuppFunctional (PolynomialEnveloping k τ) (diagonalDifference k τ)
      (polynomialDiagonalGeneratorLift k τ g i) =
        polynomialEnvelopingMap k τ g (diagonalDifference k σ i) := by
  rw [polynomialEnvelopingMap_difference]
  exact diagonalCotangentLift_equation k τ _

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, cotangent reduction of `polynomialDiagonalGeneratorLift k τ g i` is
`D k (k[τ]) (g(X_i))`. Its coordinate at a target variable `j : τ` is `∂g(X_i)/∂X_j`. -/
theorem polynomialDiagonalGeneratorLift_coordinates (i : σ) :
    diagonalCotangentCoordinates k τ (polynomialDiagonalGeneratorLift k τ g i) =
      KaehlerDifferential.D k (MvPolynomial τ k) (g (MvPolynomial.X i)) :=
  diagonalCotangentLift_coordinates k τ _

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, write `L_i = polynomialDiagonalGeneratorLift k τ g i`. This is the
`F_g`-semilinear map `E_σ →ₛₗ[F_g] (τ →₀ E_τ)` given by `e ↦ F_g(e) • L_i`. -/
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

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. The chosen image-generator lifts `L_i` define an `F_g`-semilinear map `(σ →₀
E_σ) →ₛₗ[F_g] (τ →₀ E_τ)`, with `w ↦ ∑ i ∈ supp(w), F_g(w_i) • L_i`. -/
def polynomialDiagonalGeneratorMap :
    (σ →₀ PolynomialEnveloping k σ) →ₛₗ[(polynomialEnvelopingMap k τ g).toRingHom]
      (τ →₀ PolynomialEnveloping k τ) :=
  Finsupp.lsum ℕ (polynomialDiagonalGeneratorSingle k τ g)

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ` and `e : E_σ`, `polynomialDiagonalGeneratorMap k τ g (Finsupp.single
i e) = F_g(e) • polynomialDiagonalGeneratorLift k τ g i`. -/
theorem polynomialDiagonalGeneratorMap_single (i : σ) (e : PolynomialEnveloping k σ) :
    polynomialDiagonalGeneratorMap k τ g (Finsupp.single i e) =
      polynomialEnvelopingMap k τ g e • polynomialDiagonalGeneratorLift k τ g i := by
  rw [polynomialDiagonalGeneratorMap, Finsupp.lsum_single]
  rfl

/-- Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. Let `G_g` be the semilinear generator map and `F_σ,F_τ` the diagonal functionals
`w ↦ ∑ i, w_i δ_i`. For every `w : σ →₀ E_σ`, `F_τ(G_g w) = F_g(F_σ w)`. -/
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
