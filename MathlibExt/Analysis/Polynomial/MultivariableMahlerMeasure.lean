/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Complex MeasureTheory Finset
open scoped Real

@[expose] public section

noncomputable section

namespace LogarithmicMahlerMeasure

variable {n : ℕ}

/-!
# Multivariable logarithmic Mahler measure

For a Laurent polynomial in `n` variables, this file defines evaluation on the unit torus and the
normalized integral of the logarithm of its norm. This is the formula in arXiv:2608.01951v1,
`MMP5_arxiv_v1.tex`, lines 139–146.
-/

/-- **Phase of an exponent vector.** For an angle vector $\theta \in \mathbb{R}^n$ and an exponent
vector $e \in \mathbb{Z}^n$, the real phase of $e$ at $\theta$ is $\sum_{j} e_j \theta_j$. -/
def realSum (θ : Fin n → ℝ) (e : Fin n → ℤ) : ℝ :=
  ∑ j, (e j : ℝ) * θ j

@[simp]
lemma realSum_zero (θ : Fin n → ℝ) : realSum θ 0 = 0 := by
  simp [realSum]

lemma realSum_add (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
    realSum θ (a + b) = realSum θ a + realSum θ b := by
  simp only [realSum, Pi.add_apply, Int.cast_add, add_mul, sum_add_distrib]

/-- **Torus character.** For an angle vector $\theta \in \mathbb{R}^n$, the torus character at
$\theta$ sends an exponent vector $e \in \mathbb{Z}^n$ to
$\exp\bigl(i \sum_{j} e_j \theta_j\bigr) \in \mathbb{C}$. -/
def torusCharacter (θ : Fin n → ℝ) (e : Fin n → ℤ) : ℂ :=
  Complex.exp (Complex.I * (realSum θ e : ℂ))

@[simp]
lemma torusCharacter_zero (θ : Fin n → ℝ) : torusCharacter θ 0 = 1 := by
  simp [torusCharacter]

lemma torusCharacter_add (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
    torusCharacter θ (a + b) = torusCharacter θ a * torusCharacter θ b := by
  simp only [torusCharacter, realSum_add, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- **Torus character as a monoid homomorphism.** For an angle vector $\theta \in \mathbb{R}^n$,
the torus character $e \mapsto \exp\bigl(i \sum_{j} e_j \theta_j\bigr)$, viewed as a map from the
additive group $\mathbb{Z}^n$ written multiplicatively to the multiplicative monoid of
$\mathbb{C}$, is a monoid homomorphism: it sends $0$ to $1$ and sums to products. -/
def torusCharacterHom (θ : Fin n → ℝ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun e := torusCharacter θ e.toAdd
  map_one' := by simp
  map_mul' a b := by
    have h : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    simpa only [h] using torusCharacter_add θ a.toAdd b.toAdd

/-- **Evaluation on the unit torus.** For an angle vector $\theta \in \mathbb{R}^n$, evaluation at
the point $(\exp(i\theta_1), \dots, \exp(i\theta_n))$ of the unit torus is the
$\mathbb{C}$-algebra homomorphism from complex Laurent polynomials in $n$ variables to
$\mathbb{C}$ that, writing $X^e$ for the monomial with exponent vector $e \in \mathbb{Z}^n$,
sends $\sum_e c_e X^e$ to $\sum_e c_e \exp\bigl(i \sum_{j} e_j \theta_j\bigr)$. -/
noncomputable def torusEval (θ : Fin n → ℝ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) →ₐ[ℂ] ℂ :=
  (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)) (torusCharacterHom θ)

@[simp]
lemma torusEval_single_zero (θ : Fin n → ℝ) (c : ℂ) :
    torusEval θ (AddMonoidAlgebra.single 0 c) = c := by
  simp [torusEval]

@[simp]
theorem torusEval_single (θ : Fin n → ℝ) (c : ℂ) (e : Fin n → ℤ) :
    torusEval θ (AddMonoidAlgebra.single e c) = c * torusCharacter θ e := by
  rw [torusEval, AddMonoidAlgebra.lift_single (torusCharacterHom θ) e c]
  simp [torusCharacterHom, smul_eq_mul]

/-- **Normalized box integral.** For a function $f \colon \mathbb{R}^m \to \mathbb{R}$, the
normalized box integral of $f$ is $(2\pi)^{-m} \int_{[0, 2\pi]^m} f(x) \, dx$, the integral taken
with respect to Lebesgue measure (and equal to $0$ when $f$ is not integrable on the box). -/
noncomputable def normalizedBoxIntegral {m : ℕ} (f : (Fin m → ℝ) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ m)⁻¹ *
    ∫ x in Set.Icc (0 : Fin m → ℝ) (fun _ => 2 * Real.pi), f x ∂volume

/-- **Logarithmic Mahler measure.** For a complex Laurent polynomial $F$ in $m$ variables, the
logarithmic Mahler measure of $F$ is the real number
$(2\pi)^{-m} \int_{[0, 2\pi]^m} \log |F(e^{i\theta_1}, \dots, e^{i\theta_m})| \, d\theta$,
the integral taken with respect to Lebesgue measure.

The cited source applies this formula to nonzero polynomials. As with Mathlib's logarithmic
Mahler measure of one-variable polynomials, the definition here is total: $\log 0 = 0$ and a
non-integrable function has integral $0$, so in particular the value at $F = 0$ is $0$. -/
noncomputable def logarithmicMahlerMeasure {m : ℕ}
    (F : AddMonoidAlgebra ℂ (Fin m → ℤ)) : ℝ :=
  normalizedBoxIntegral fun θ => Real.log ‖torusEval θ F‖

@[simp]
theorem logarithmicMahlerMeasure_const {m : ℕ} (c : ℂ) :
    logarithmicMahlerMeasure
      (AddMonoidAlgebra.single (0 : Fin m → ℤ) c) = Real.log ‖c‖ := by
  simp only [logarithmicMahlerMeasure, torusEval_single_zero, normalizedBoxIntegral,
    integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ, Measure.real]
  rw [Real.volume_Icc_pi_toReal (fun _ => by positivity)]
  simp [Finset.prod_const, Real.pi_ne_zero]

@[simp]
theorem logarithmicMahlerMeasure_zero {m : ℕ} :
    logarithmicMahlerMeasure (0 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
  simp [logarithmicMahlerMeasure, normalizedBoxIntegral]

/-- **Integer vectors of length one.** The additive isomorphism from $\mathbb{Z}^1$, the group of
functions $\{0\} \to \mathbb{Z}$ under pointwise addition, to $\mathbb{Z}$ that sends a function
$e$ to its value $e(0)$. -/
def finOneAddEquiv : (Fin 1 → ℤ) ≃+ ℤ :=
  AddEquiv.funUnique (Fin 1) ℤ

/-- **Identification of one-variable Laurent polynomials.** The $\mathbb{C}$-algebra isomorphism
from complex Laurent polynomials whose exponents are vectors $e \in \mathbb{Z}^1$ (functions
$\{0\} \to \mathbb{Z}$) to complex Laurent polynomials $\mathbb{C}[T, T^{-1}]$ in one variable,
induced by the additive isomorphism $\mathbb{Z}^1 \cong \mathbb{Z}$, $e \mapsto e(0)$. Writing
$X^{e}$ for the monomial with exponent vector $e$, it sends $c\,X^{e}$ to $c\,T^{e(0)}$. -/
noncomputable def bridgeLaurent :
    AddMonoidAlgebra ℂ (Fin 1 → ℤ) ≃ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.domCongr ℂ ℂ finOneAddEquiv

@[simp]
lemma bridgeLaurent_single (c : ℂ) (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) c) =
      AddMonoidAlgebra.single k c := by
  simp [bridgeLaurent, finOneAddEquiv]

@[simp]
lemma bridgeLaurent_C (c : ℂ) :
    bridgeLaurent (AddMonoidAlgebra.single (0 : Fin 1 → ℤ) c) = LaurentPolynomial.C c := by
  rw [show (0 : Fin 1 → ℤ) = fun _ => 0 from rfl, bridgeLaurent_single]
  rfl

@[simp]
lemma bridgeLaurent_T (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) 1) = LaurentPolynomial.T k := by
  rw [bridgeLaurent_single]
  rfl

@[simp]
theorem logarithmicMahlerMeasure_one {m : ℕ} :
    logarithmicMahlerMeasure (1 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
  simp [logarithmicMahlerMeasure, normalizedBoxIntegral]

end LogarithmicMahlerMeasure

end
