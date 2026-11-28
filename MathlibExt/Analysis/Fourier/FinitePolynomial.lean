/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Fourier
public import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Fourier polynomials on the two-dimensional torus

The additive monoid algebra of the integer frequency lattice supplies exact
finite convolution. Its realization uses the existing normalized-Haar torus
characters. Coefficient recovery and Parseval connect the algebra to actual
functions; physical coordinate derivatives on the period-`2π` torus have the
multiplier `i * k_j`. Hermitian coefficients give real functions, and the zero
coefficient of a derivative vanishes, yielding integration by parts.

The normalized coefficients here are `c_k`; `TorusSobolev.fourierCoefficient`
uses `a_k = 2π c_k`. These conventions underlie the classical periodic Fourier
model in Agrachev–Sarychev, *Navier-Stokes Equations: Controllability by Means of
Low Modes Forcing*, Section 2.2, and Bedrossian–Punshon-Smith, *Chaos in Stochastic
2d Galerkin-Navier-Stokes* (2024), Section 1.1. The physical derivative bridge
fixes the scaling independently of formal coefficient manipulations.
-/

@[expose] public section

open MeasureTheory TorusSobolev
open scoped ComplexConjugate
noncomputable section
namespace TorusFourier
/-- Finite complex Fourier polynomials on the integer two-dimensional frequency lattice, with
exact convolution multiplication. -/
abbrev Polynomial := AddMonoidAlgebra ℂ Frequency

/-- Realize a finite coefficient polynomial as a continuous function on the unit torus using its
normalized Fourier characters. This map preserves sums, products and complex scalar
multiplication. -/
def realize : Polynomial →ₐ[ℂ] C(UnitAddTorus (Fin 2), ℂ) :=
  AddMonoidAlgebra.lift ℂ _ _ {
    toFun k := UnitAddTorus.mFourier k.toAdd
    map_one' := UnitAddTorus.mFourier_zero
    map_mul' k l := by ext x; exact UnitAddTorus.mFourier_add
  }

/-- A single coefficient at frequency k realizes as that coefficient times the k-th unit-torus
character. -/
@[simp] theorem realize_single (k : Frequency) (c : ℂ) :
    realize (AddMonoidAlgebra.single k c) = c • UnitAddTorus.mFourier k := by
  exact AddMonoidAlgebra.lift_single _ k c

/-- The normalized Haar Fourier coefficient of the realized polynomial at any frequency is exactly
its stored coefficient. -/
theorem coefficient_realize (p : Polynomial) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (realize p) k = p.coeff k := by
  induction p using AddMonoidAlgebra.induction_on with
  | of m =>
    change UnitAddTorus.mFourierCoeff (realize (AddMonoidAlgebra.single m 1)) k = _
    simp [TorusSobolev.mFourierCoeff_monomial, Finsupp.single_apply, eq_comm]
  | add p q hp hq =>
    rw [map_add, TorusSobolev.mFourierCoeff_add, hp, hq]
    rfl
  | smul c p hp =>
    rw [map_smul, TorusSobolev.mFourierCoeff_smul, hp]
    rfl

/-- Apply an arbitrary complex frequency multiplier to a finite polynomial. The coefficients
remain finitely supported; the map is complex-linear. -/
def multiplier (m : Frequency → ℂ) : Polynomial →ₗ[ℂ] Polynomial where
  toFun p := AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset p.coeff.support (fun k ↦ m k * p.coeff k)
      (by
        intro k hk
        by_contra h
        simp only [Finsupp.mem_support_iff, not_not] at h
        simp [h] at hk))
  map_add' p q := by ext k; simp [mul_add]
  map_smul' c p := by ext k; simp [mul_left_comm]

/-- A frequency multiplier acts coefficientwise by multiplication, including frequencies outside
the finite support. -/
@[simp] theorem multiplier_coeff (m : Frequency → ℂ) (p : Polynomial) (k : Frequency) :
    (multiplier m p).coeff k = m k * p.coeff k := rfl

/-- A frequency multiplier preserves a single mode and multiplies its coefficient by the
multiplier at that mode. -/
@[simp] theorem multiplier_single (m : Frequency → ℂ) (k : Frequency) (c : ℂ) :
    multiplier m (AddMonoidAlgebra.single k c) = AddMonoidAlgebra.single k (m k * c) := by
  classical
  ext j
  by_cases h : k = j <;> simp [h]

/-- The physical coordinate derivative multiplier i*k_j on the torus of period 2π in both
coordinates. -/
def derivative (j : Fin 2) : Polynomial →ₗ[ℂ] Polynomial :=
  multiplier fun k ↦ Complex.I * (k j : ℂ)

/-- The j-th physical derivative multiplies the coefficient at k by i*k_j. -/
@[simp] theorem derivative_coeff (j : Fin 2) (p : Polynomial) (k : Frequency) :
    (derivative j p).coeff k = Complex.I * (k j : ℂ) * p.coeff k := rfl

/-- Physical Fourier differentiation obeys the product rule for exact finite convolution. -/
theorem derivative_mul (j : Fin 2) (p q : Polynomial) :
    derivative j (p * q) = derivative j p * q + p * derivative j q := by
  induction p using AddMonoidAlgebra.induction_on with
  | of k =>
    induction q using AddMonoidAlgebra.induction_on with
    | of l =>
      change derivative j (AddMonoidAlgebra.single k 1 * AddMonoidAlgebra.single l 1) =
        derivative j (AddMonoidAlgebra.single k 1) * AddMonoidAlgebra.single l 1 +
        AddMonoidAlgebra.single k 1 * derivative j (AddMonoidAlgebra.single l 1)
      simp only [AddMonoidAlgebra.single_mul_single, derivative, multiplier_single,
        one_mul, mul_one, Pi.add_apply, Int.cast_add, ← AddMonoidAlgebra.single_add]
      congr 1
      ring
    | add q r hq hr => simp only [mul_add, map_add, hq, hr]; abel
    | smul c q hq =>
      simp only [mul_smul_comm, map_smul, hq, smul_add]
  | add p r hp hr => simp only [add_mul, map_add, hp, hr]; abel
  | smul c p hp =>
    simp only [smul_mul_assoc, map_smul, hp, smul_add]

/-- The two physical Fourier coordinate derivatives commute on every finite polynomial. -/
theorem derivative_commute (i j : Fin 2) (p : Polynomial) :
    derivative i (derivative j p) = derivative j (derivative i p) := by
  ext k
  simp only [derivative_coeff]
  ring


local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The integral of the squared norm of a finite Fourier polynomial, with normalized Haar
probability measure on the unit torus, equals the finite sum of squared coefficient norms. -/
theorem parseval (p : Polynomial) :
    ∫ x, ‖realize p x‖ ^ 2 = ∑ k ∈ p.coeff.support, ‖p.coeff k‖ ^ 2 := by
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff ((realize p).toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp, coefficient_realize] at h
  have hi : (∫ x, ‖((realize p).toLp 2 volume ℂ) x‖ ^ 2) =
      ∫ x, ‖realize p x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (realize p)] with x hx
    rw [hx]
  rw [hi] at h
  rw [← h.tsum_eq]
  exact tsum_eq_sum (fun k hk ↦ by simp [Finsupp.notMem_support_iff.mp hk])

/-- Realize a finite Fourier polynomial on the torus of period 2π by the canonical rescaling to
the unit torus. -/
def physical (p : Polynomial) : C(Torus, ℂ) :=
  (realize p).comp ⟨unitRescaling, unitRescaling.continuous⟩

/-- Lift the realized period-2π Fourier polynomial to a periodic complex function of two real
coordinates. -/
def physicalLift (p : Polynomial) (x : Fin 2 → ℝ) : ℂ :=
  physical p (fun j ↦ (x j : AddCircle (2 * Real.pi)))

/-- The physical lift of a single mode is its coefficient times the product of the two period-2π
circle characters. -/
theorem physicalLift_single (k : Frequency) (c : ℂ) (x : Fin 2 → ℝ) :
    physicalLift (AddMonoidAlgebra.single k c) x =
      c * ∏ j : Fin 2, fourier (k j) (x j : AddCircle (2 * Real.pi)) := by
  simp only [physicalLift, physical, ContinuousMap.comp_apply, realize_single,
    ContinuousMap.smul_apply, smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  apply congrArg (c * ·)
  apply Finset.prod_congr rfl
  intro j _
  change fourier (k j) (AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _
    (x j : AddCircle (2 * Real.pi))) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  simp only [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_one, mul_one, div_one]
  congr 1
  ring

/-- Complex conjugation of a physical Fourier polynomial: conjugate the coefficients and reverse
the frequency. This is a ring homomorphism, not a complex-linear map. -/
def conjugate : Polynomial →+* Polynomial :=
  (AddMonoidAlgebra.mapDomainRingEquiv ℂ (AddEquiv.neg Frequency)).toRingHom.comp
    (AddMonoidAlgebra.mapRingHom Frequency (starRingEnd ℂ))

/-- The coefficient of the conjugate polynomial at k is the complex conjugate of the original
coefficient at -k. -/
@[simp] theorem conjugate_coeff (p : Polynomial) (k : Frequency) :
    (conjugate p).coeff k = conj (p.coeff (-k)) := by
  simp [conjugate, AddMonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]


/-- Physical realization preserves sums of finite Fourier polynomials. -/
@[simp] theorem physicalLift_add (p q : Polynomial) (x : Fin 2 → ℝ) :
    physicalLift (p + q) x = physicalLift p x + physicalLift q x := by
  simp [physicalLift, physical]

/-- Physical realization turns complex scalar multiplication into pointwise multiplication. -/
@[simp] theorem physicalLift_smul (c : ℂ) (p : Polynomial) (x : Fin 2 → ℝ) :
    physicalLift (c • p) x = c * physicalLift p x := by
  simp [physicalLift, physical]

private theorem physical_single_deriv (j : Fin 2) (k : Frequency) (c : ℂ)
    (x : Fin 2 → ℝ) :
    HasDerivAt (fun t ↦ physicalLift (AddMonoidAlgebra.single k c) (Function.update x j t))
      (physicalLift (derivative j (AddMonoidAlgebra.single k c)) x) (x j) := by
  have hs (n : ℤ) : 2 * (Real.pi : ℂ) * Complex.I * n / (2 * Real.pi) =
      Complex.I * n := by field_simp
  simp only [physicalLift_single, derivative, multiplier_single, Fin.prod_univ_two]
  fin_cases j
  · change HasDerivAt (fun t ↦ c * (fourier (k 0) (Function.update x 0 t 0 : AddCircle _) *
        fourier (k 1) (Function.update x 0 t 1 : AddCircle _)))
      (Complex.I * (k 0 : ℂ) * c * (fourier (k 0) (x 0 : AddCircle _) *
        fourier (k 1) (x 1 : AddCircle _))) (x 0)
    convert (((hasDerivAt_fourier (2 * Real.pi) (k 0) (x 0)).mul_const
      (fourier (k 1) (x 1 : AddCircle (2 * Real.pi)))).const_mul c) using 1
    · ext t; simp
    · simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, hs]
      ring
  · change HasDerivAt (fun t ↦ c * (fourier (k 0) (Function.update x 1 t 0 : AddCircle _) *
        fourier (k 1) (Function.update x 1 t 1 : AddCircle _)))
      (Complex.I * (k 1 : ℂ) * c * (fourier (k 0) (x 0 : AddCircle _) *
        fourier (k 1) (x 1 : AddCircle _))) (x 1)
    convert (((hasDerivAt_fourier (2 * Real.pi) (k 1) (x 1)).const_mul
      (fourier (k 0) (x 0 : AddCircle (2 * Real.pi)))).const_mul c) using 1
    · ext t; simp
    · simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, hs]
      ring

/-- Varying the j-th real coordinate of the actual physical lift has derivative equal to the
physical lift of the multiplier i*k_j, at every point. -/
theorem hasDerivAt_physicalLift (j : Fin 2) (p : Polynomial) (x : Fin 2 → ℝ) :
    HasDerivAt (fun t ↦ physicalLift p (Function.update x j t))
      (physicalLift (derivative j p) x) (x j) := by
  induction p using AddMonoidAlgebra.induction_on with
  | of k => exact physical_single_deriv j k 1 x
  | add p q hp hq => simpa only [map_add, physicalLift_add] using hp.fun_add hq
  | smul c p hp => simpa only [map_smul, physicalLift_smul] using hp.const_mul c

/-- Conjugation reverses the frequency of a single mode and conjugates its coefficient. -/
@[simp] theorem conjugate_single (k : Frequency) (c : ℂ) :
    conjugate (AddMonoidAlgebra.single k c) = AddMonoidAlgebra.single (-k) (conj c) := by
  ext j
  simp only [conjugate_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    apply_ite, map_zero, neg_eq_iff_eq_neg]
  split_ifs <;> rfl

/-- Conjugation is conjugate-linear for complex scalar multiplication. -/
@[simp] theorem conjugate_smul (c : ℂ) (p : Polynomial) :
    conjugate (c • p) = conj c • conjugate p := by
  ext k
  simp [map_mul]

/-- Realization of the conjugate polynomial is pointwise complex conjugation of the realized
function. -/
theorem realize_conjugate (p : Polynomial) (x : UnitAddTorus (Fin 2)) :
    realize (conjugate p) x = conj (realize p x) := by
  induction p using AddMonoidAlgebra.induction_on with
  | of k =>
    change realize (conjugate (AddMonoidAlgebra.single k 1)) x = _
    simp [UnitAddTorus.mFourier_neg]
  | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq]
  | smul c p hp => simp only [conjugate_smul, map_smul, ContinuousMap.smul_apply,
      smul_eq_mul, hp, map_mul]

/-- Hermitian symmetry of finite Fourier coefficients: the coefficient at -k is the complex
conjugate of the coefficient at k, for every integer frequency. -/
def IsReal (p : Polynomial) : Prop := ∀ k, p.coeff (-k) = conj (p.coeff k)

/-- A Hermitian polynomial is fixed by coefficient conjugation with frequency reversal. -/
theorem IsReal.conjugate_eq {p : Polynomial} (hp : IsReal p) : conjugate p = p := by
  ext k
  simp [hp k]

/-- A finite polynomial with Hermitian coefficients realizes as a real-valued function on the unit
torus. -/
theorem IsReal.realize_im {p : Polynomial} (hp : IsReal p) (x : UnitAddTorus (Fin 2)) :
    (realize p x).im = 0 := by
  have h := realize_conjugate p x
  rw [hp.conjugate_eq] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith


/-- Exact convolution of two Hermitian finite Fourier polynomials is Hermitian. -/
theorem IsReal.mul {p q : Polynomial} (hp : IsReal p) (hq : IsReal q) : IsReal (p * q) := by
  intro k
  have h : conjugate (p * q) = p * q := by rw [map_mul, hp.conjugate_eq, hq.conjugate_eq]
  have he := congrArg (fun r : Polynomial ↦ r.coeff (-k)) h
  simpa only [conjugate_coeff, neg_neg] using he.symm

/-- Physical coordinate differentiation preserves Hermitian symmetry of finite Fourier
coefficients. -/
theorem IsReal.derivative {p : Polynomial} (hp : IsReal p) (j : Fin 2) :
    IsReal (derivative j p) := by
  intro k
  simp only [derivative_coeff, Pi.neg_apply, Int.cast_neg, hp k, map_mul,
    Complex.conj_I, map_intCast]
  ring

/-- The real part of the physical realization on the period-2π torus. For Hermitian coefficients
this retains the whole realized function. -/
def realPhysical (p : Polynomial) : C(Torus, ℝ) where
  toFun x := (physical p x).re
  continuous_toFun := Complex.continuous_re.comp (physical p).continuous

/-- For a Hermitian polynomial, the complex unit representative of its real physical realization
equals its original unit-torus realization. -/
theorem IsReal.unitRepresentative {p : Polynomial} (hp : IsReal p) :
    TorusSobolev.unitRepresentative (realPhysical p) = realize p := by
  ext x
  change ((realize p (unitRescaling (unitRescaling.symm x))).re : ℂ) = realize p x
  rw [unitRescaling.apply_symm_apply]
  exact Complex.ext (by simp) (by simp [hp.realize_im x])

/-- The TorusSobolev coefficient of a real Hermitian finite polynomial is 2π times its normalized
mean coefficient. -/
theorem IsReal.fourierCoefficient {p : Polynomial} (hp : IsReal p) (k : Frequency) :
    TorusSobolev.fourierCoefficient (realPhysical p) k = (2 * Real.pi : ℂ) * p.coeff k := by
  rw [TorusSobolev.fourierCoefficient, hp.unitRepresentative, coefficient_realize]

/-- The normalized Haar integral of a finite Fourier polynomial is its
zero-frequency coefficient. -/
theorem integral_realize (p : Polynomial) : ∫ x, realize p x = p.coeff 0 := by
  have h := coefficient_realize p 0
  simpa only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul] using h

/-- The zero-frequency coefficient of each physical derivative is zero. -/
@[simp] theorem derivative_coeff_zero (j : Fin 2) (p : Polynomial) :
    (derivative j p).coeff 0 = 0 := by simp

/-- Finite Fourier integration by parts: the zero coefficient of D_j(p)*q is the negative of that
of p*D_j(q). The zero coefficient is the normalized integral of the realized product. -/
theorem integration_by_parts (j : Fin 2) (p q : Polynomial) :
    (derivative j p * q).coeff 0 = -(p * derivative j q).coeff 0 := by
  have h := derivative_coeff_zero j (p * q)
  rw [derivative_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  exact eq_neg_of_add_eq_zero_left h


/-- Conjugation with frequency reversal is an involution on finite Fourier polynomials. -/
@[simp] theorem conjugate_conjugate (p : Polynomial) : conjugate (conjugate p) = p := by
  ext k
  simp only [conjugate_coeff, neg_neg, starRingEnd_apply, star_star]

/-- Hermitian coefficient symmetry is equivalent to being fixed by polynomial conjugation. -/
theorem isReal_iff_conjugate_eq (p : Polynomial) : IsReal p ↔ conjugate p = p := by
  refine ⟨IsReal.conjugate_eq, fun h k ↦ ?_⟩
  have he := congrArg (fun r : Polynomial ↦ r.coeff (-k)) h
  simpa only [conjugate_coeff, neg_neg] using he.symm

/-- Sums of Hermitian finite Fourier polynomials have Hermitian coefficients. -/
theorem IsReal.add {p q : Polynomial} (hp : IsReal p) (hq : IsReal q) : IsReal (p + q) := by
  rw [isReal_iff_conjugate_eq, map_add, hp.conjugate_eq, hq.conjugate_eq]

/-- A frequency multiplier satisfying m(-k)=conj(m(k)) preserves Hermitian coefficient symmetry. -/
theorem IsReal.multiplier {p : Polynomial} (hp : IsReal p) (m : Frequency → ℂ)
    (hm : ∀ k, m (-k) = conj (m k)) : IsReal (multiplier m p) := by
  intro k
  simp only [multiplier_coeff, hm, hp k, map_mul]

end TorusFourier
