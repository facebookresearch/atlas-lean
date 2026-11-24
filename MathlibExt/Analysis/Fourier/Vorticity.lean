/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Fourier.FinitePolynomial
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Periodic vorticity transport and Fourier projection cancellation

For normalized Fourier coefficients on the period-`2π` torus, set
`ψ_k = -ω_k / |k|²`, with the reciprocal at zero totalized to zero. The velocity
`u = (-D₁ψ, D₀ψ)` is divergence-free and has curl `ω` when `ω₀ = 0`.
Transport is `u · ∇ω = {ψ, ω}`; its negative enters the evolution equation.

Zero-mode integration by parts proves both convection cancellations. A symmetric
finite coefficient projection preserves the pairings against supported input,
without assuming the retained modes are closed under addition. Hermitian reality
turns these into the complex sums for enstrophy and kinetic energy; the latter
weights each mode by `1 / |k|²`. Square cutoffs explicitly exclude the zero mode.

This is the classical finite Fourier-Galerkin vorticity model in Agrachev–Sarychev,
*Navier-Stokes Equations: Controllability by Means of Low Modes Forcing*, Section
2.2, and Bedrossian–Punshon-Smith, *Chaos in Stochastic 2d Galerkin-Navier-Stokes*
(2024), Section 1.1. The curl and transport signs are fixed by the definitions
above and the actual physical derivative bridge. These algebraic results do not
assert a global ODE trajectory or existence of a PDE solution.
-/

@[expose] public section

open TorusSobolev
open scoped ComplexConjugate
noncomputable section
namespace TorusFourier

/-- The Jacobian bracket of two finite Fourier polynomials: {p,q}=D₀p D₁q-D₁p D₀q, using physical
derivatives and exact convolution. -/
def bracket (p q : Polynomial) : Polynomial :=
  derivative 0 p * derivative 1 q - derivative 1 p * derivative 0 q

/-- The Jacobian bracket of any two finite complex Fourier polynomials has zero mean coefficient. -/
theorem bracket_coeff_zero (p q : Polynomial) : (bracket p q).coeff 0 = 0 := by
  simp only [bracket, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rw [integration_by_parts, integration_by_parts, derivative_commute 0 1]
  exact sub_self _

/-- The finite Fourier Jacobian bracket satisfies the product rule in its second argument. -/
theorem bracket_mul_right (p q r : Polynomial) :
    bracket p (q * r) = bracket p q * r + q * bracket p r := by
  simp only [bracket, derivative_mul]
  ring

/-- The finite Fourier Jacobian bracket satisfies the product rule in its first argument. -/
theorem bracket_mul_left (p q r : Polynomial) :
    bracket (p * q) r = p * bracket q r + q * bracket p r := by
  simp only [bracket, derivative_mul]
  ring

/-- The normalized bilinear pairing of q with {p,q} vanishes for any finite complex Fourier
polynomials p and q. -/
theorem bracket_pair_self_right (p q : Polynomial) : (q * bracket p q).coeff 0 = 0 := by
  have h := bracket_coeff_zero p (q * q)
  rw [bracket_mul_right, mul_comm (bracket p q) q,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  linear_combination h / 2

/-- The normalized bilinear pairing of p with {p,q} vanishes for any finite complex Fourier
polynomials p and q. -/
theorem bracket_pair_self_left (p q : Polynomial) : (p * bracket p q).coeff 0 = 0 := by
  have h := bracket_coeff_zero (p * p) q
  rw [bracket_mul_left, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  linear_combination h / 2


/-- The exact Fourier projection onto a finite set S keeps precisely its coefficients.
Multiplication is not wrapped modulo a grid. -/
def project (S : Finset Frequency) : Polynomial →ₗ[ℂ] Polynomial :=
  multiplier fun k ↦ if k ∈ S then 1 else 0

/-- The projected coefficient is the original coefficient on S and zero outside S. -/
@[simp] theorem project_coeff (S : Finset Frequency) (p : Polynomial) (k : Frequency) :
    (project S p).coeff k = if k ∈ S then p.coeff k else 0 := by
  classical
  simp only [project, multiplier_coeff]
  split_ifs <;> simp

/-- A Fourier polynomial supported in S is fixed by projection onto S. -/
theorem project_eq_self (S : Finset Frequency) {p : Polynomial}
    (hp : p.coeff.support ⊆ S) : project S p = p := by
  classical
  ext k
  rw [project_coeff]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 (fun hk ↦ h (hp hk))).symm

/-- For a symmetric finite mode set S and a polynomial p supported in S, projecting an arbitrary
q preserves the zero-mode pairing of p with q. No additive closure of S is assumed. -/
theorem project_pair (S : Finset Frequency) (hS : ∀ k, k ∈ S ↔ -k ∈ S)
    {p : Polynomial} (hp : p.coeff.support ⊆ S) (q : Polynomial) :
    (p * project S q).coeff 0 = (p * q).coeff 0 := by
  classical
  simp only [AddMonoidAlgebra.coeff_mul_apply_left, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [project_coeff, ite_eq_left ((hS k).1 (hp hk))]

/-- Projection onto a symmetric finite frequency set preserves Hermitian coefficient symmetry. -/
theorem IsReal.project {p : Polynomial} (hp : IsReal p) (S : Finset Frequency)
    (hS : ∀ k, k ∈ S ↔ -k ∈ S) : IsReal (project S p) := by
  apply hp.multiplier
  intro k
  simp only [← (hS k), apply_ite, map_one, map_zero]
  split_ifs <;> rfl

/-- Recover the zero-mean streamfunction by the multiplier -1/|k|². The inverse at zero is
defined to be zero, so any input mean is discarded. -/
def streamFunction (p : Polynomial) : Polynomial :=
  multiplier (fun k ↦ -(frequencyWeight k : ℂ)⁻¹) p

/-- The finite vorticity transport is {ψ,ω}, with ψ recovered by the inverse Laplacian. This is
the positive transport u·∇ω; the convective evolution term is its negative. -/
def transport (p : Polynomial) : Polynomial := bracket (streamFunction p) p

/-- The bilinear zero-mode pairing of vorticity with its finite Fourier transport is zero. This
algebraic cancellation needs neither reality nor zero mean. -/
theorem transport_enstrophy_cancel (p : Polynomial) : (p * transport p).coeff 0 = 0 :=
  bracket_pair_self_right _ _

/-- The bilinear zero-mode pairing of streamfunction with vorticity transport is zero. This
algebraic cancellation needs neither reality nor zero mean. -/
theorem transport_energy_cancel (p : Polynomial) :
    (streamFunction p * transport p).coeff 0 = 0 := bracket_pair_self_left _ _

/-- Inverse-Laplacian reconstruction does not enlarge finite coefficient support. -/
theorem streamFunction_support (p : Polynomial) :
    (streamFunction p).coeff.support ⊆ p.coeff.support := by
  intro k hk
  contrapose hk
  simp only [Finsupp.notMem_support_iff] at hk ⊢
  simp [streamFunction, hk]

/-- For a symmetric finite set S and vorticity supported in S, projecting the exact transport
preserves its zero pairing with vorticity. -/
theorem project_transport_enstrophy_cancel (S : Finset Frequency)
    (hS : ∀ k, k ∈ S ↔ -k ∈ S) {p : Polynomial} (hp : p.coeff.support ⊆ S) :
    (p * project S (transport p)).coeff 0 = 0 := by
  rw [project_pair S hS hp, transport_enstrophy_cancel]

/-- For a symmetric finite set S and vorticity supported in S, projecting the exact transport
preserves its zero pairing with the recovered streamfunction. -/
theorem project_transport_energy_cancel (S : Finset Frequency)
    (hS : ∀ k, k ∈ S ↔ -k ∈ S) {p : Polynomial} (hp : p.coeff.support ⊆ S) :
    (streamFunction p * project S (transport p)).coeff 0 = 0 := by
  rw [project_pair S hS ((streamFunction_support p).trans hp), transport_energy_cancel]


/-- The physical Fourier Laplacian is D₀²+D₁² on finite polynomials. -/
def laplacian (p : Polynomial) : Polynomial := derivative 0 (derivative 0 p) +
  derivative 1 (derivative 1 p)

/-- The physical Fourier Laplacian multiplies each coefficient by -|k|². -/
theorem laplacian_coeff (p : Polynomial) (k : Frequency) :
    (laplacian p).coeff k = -(frequencyWeight k : ℂ) * p.coeff k := by
  simp only [laplacian, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, derivative_coeff,
    frequencyWeight, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_intCast]
  linear_combination Complex.I_sq * ((k 0 : ℂ)^2 * p.coeff k + (k 1 : ℂ)^2 * p.coeff k)

/-- The squared Euclidean weight of an integer two-dimensional frequency is zero exactly at the
zero frequency. -/
theorem weight_eq_zero_iff (k : Frequency) : frequencyWeight k = 0 ↔ k = 0 := by
  constructor
  · intro h
    ext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (k i : ℝ))).1 h
      j (Finset.mem_univ j)
    have hz : (k j : ℝ) = 0 := by nlinarith [hj]
    exact_mod_cast hz
  · rintro rfl
    simp [frequencyWeight]

/-- Squared frequency weight is invariant under reversing the frequency. -/
theorem weight_neg (k : Frequency) : frequencyWeight (-k) = frequencyWeight k := by
  simp [frequencyWeight]

/-- The Laplacian of the recovered streamfunction equals the original finite polynomial when its
zero coefficient vanishes. -/
theorem laplacian_streamFunction {p : Polynomial} (hp : p.coeff 0 = 0) :
    laplacian (streamFunction p) = p := by
  ext k
  rw [laplacian_coeff]
  simp only [streamFunction, multiplier_coeff]
  by_cases hk : k = 0
  · subst k; simp [hp]
  · have hw : (frequencyWeight k : ℂ) ≠ 0 := by
      exact_mod_cast (mt (weight_eq_zero_iff k).1 hk)
    field_simp

/-- The velocity reconstructed from finite vorticity is (-D₁ψ,D₀ψ), with ψ the inverse-Laplacian
streamfunction. -/
def velocity (p : Polynomial) : Fin 2 → Polynomial :=
  ![-derivative 1 (streamFunction p), derivative 0 (streamFunction p)]

/-- The reconstructed finite Fourier velocity is divergence-free, including when the input has a
nonzero mean that reconstruction discards. -/
theorem velocity_divergence (p : Polynomial) :
    derivative 0 (velocity p 0) + derivative 1 (velocity p 1) = 0 := by
  simp only [velocity, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]
  rw [derivative_commute]
  exact neg_add_cancel _

/-- For zero-mean finite vorticity, the reconstructed velocity has curl D₀u₁-D₁u₀ equal to that
vorticity. -/
theorem velocity_curl {p : Polynomial} (hp : p.coeff 0 = 0) :
    derivative 0 (velocity p 1) - derivative 1 (velocity p 0) = p := by
  simpa [velocity, laplacian] using laplacian_streamFunction hp

/-- Inverse-Laplacian streamfunction reconstruction preserves Hermitian reality. -/
theorem IsReal.streamFunction {p : Polynomial} (hp : IsReal p) :
    IsReal (streamFunction p) := by
  apply hp.multiplier
  intro k
  simp only [weight_neg, map_neg, map_inv₀, Complex.conj_ofReal]


/-- The symmetric square cutoff consists of nonzero integer frequencies with both coordinates
between -N and N. N=0 gives no retained modes. -/
def squareModes (N : ℕ) : Finset Frequency :=
  (Fintype.piFinset fun _ : Fin 2 ↦ Finset.Icc (-(N : ℤ)) N).erase 0

/-- Membership in the square cutoff means a nonzero frequency and coordinate bounds -N≤k_j≤N for
both coordinates. -/
theorem mem_squareModes (N : ℕ) (k : Frequency) :
    k ∈ squareModes N ↔ k ≠ 0 ∧ ∀ j, -(N : ℤ) ≤ k j ∧ k j ≤ N := by
  simp [squareModes, Fintype.mem_piFinset]

/-- Every square frequency cutoff is invariant under frequency reversal. -/
theorem squareModes_symmetric (N : ℕ) (k : Frequency) :
    k ∈ squareModes N ↔ -k ∈ squareModes N := by
  simp only [mem_squareModes, neg_ne_zero, Pi.neg_apply]
  constructor <;> rintro ⟨h0, h⟩ <;> refine ⟨h0, fun j ↦ ?_⟩ <;> have := h j <;> omega

/-- Vorticity transport equals u₀D₀ω+u₁D₁ω for the reconstructed velocity, with the stated curl
convention. -/
theorem transport_eq_velocity (p : Polynomial) :
    transport p = velocity p 0 * derivative 0 p + velocity p 1 * derivative 1 p := by
  simp only [transport, bracket, velocity, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Negating a Hermitian finite Fourier polynomial preserves Hermitian reality. -/
theorem IsReal.neg {p : Polynomial} (hp : IsReal p) : IsReal (-p) := by
  rw [isReal_iff_conjugate_eq, map_neg, hp.conjugate_eq]

/-- The difference of two Hermitian finite Fourier polynomials is Hermitian. -/
theorem IsReal.sub {p q : Polynomial} (hp : IsReal p) (hq : IsReal q) : IsReal (p-q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

/-- The Jacobian bracket of two Hermitian finite Fourier polynomials is Hermitian. -/
theorem IsReal.bracket {p q : Polynomial} (hp : IsReal p) (hq : IsReal q) :
    IsReal (bracket p q) :=
  ((hp.derivative 0).mul (hq.derivative 1)).sub ((hp.derivative 1).mul (hq.derivative 0))

/-- The finite vorticity transport of a Hermitian polynomial is Hermitian. -/
theorem IsReal.transport {p : Polynomial} (hp : IsReal p) : IsReal (transport p) :=
  hp.streamFunction.bracket hp

/-- The oriented frequency determinant is det(k,l)=k₀l₁-k₁l₀ as a real number. -/
def determinant (k l : Frequency) : ℝ := (k 0 : ℝ) * l 1 - (k 1 : ℝ) * l 0

/-- The Jacobian bracket of single modes a e_k and b e_l is the single mode -det(k,l)ab e_(k+l). -/
theorem bracket_single (k l : Frequency) (a b : ℂ) :
    bracket (AddMonoidAlgebra.single k a) (AddMonoidAlgebra.single l b) =
      AddMonoidAlgebra.single (k+l) (-(determinant k l : ℂ) * a * b) := by
  simp only [bracket, derivative, multiplier_single, AddMonoidAlgebra.single_mul_single,
    ← AddMonoidAlgebra.single_sub, determinant, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_intCast]
  congr 1
  linear_combination Complex.I_sq * ((k 0 : ℂ) * (l 1 : ℂ) * a * b -
    (k 1 : ℂ) * (l 0 : ℂ) * a * b)


private theorem multiplier_support (m : Frequency → ℂ) (p : Polynomial) :
    (multiplier m p).coeff.support ⊆ p.coeff.support := by
  intro k hk
  contrapose hk
  simp only [Finsupp.notMem_support_iff] at hk ⊢
  simp [hk]

private theorem coefficient_multiplier_mul (m : Frequency → ℂ) (p q : Polynomial)
    (k : Frequency) :
    (multiplier m p * q).coeff k =
      ∑ l ∈ p.coeff.support, m l * p.coeff l * q.coeff (k-l) := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp only [Finsupp.sum, multiplier_coeff]
  have he (l : Frequency) : -l+k = k-l := by abel
  simp only [he]
  apply Finset.sum_subset (multiplier_support m p)
  intro l _ hl
  have hz := Finsupp.notMem_support_iff.1 hl
  rw [multiplier_coeff] at hz
  rw [hz, zero_mul]

private theorem derivative_streamFunction (j : Fin 2) (p : Polynomial) :
    derivative j (streamFunction p) =
      multiplier (fun k ↦ Complex.I * (k j : ℂ) * -(frequencyWeight k : ℂ)⁻¹) p := by
  ext k
  simp only [derivative_coeff, streamFunction, multiplier_coeff]
  ring

/-- The transport coefficient at k is the finite sum det(l,k)/|l|² times ω_l ω_(k-l), over the
input support. The zero denominator is totalized to zero. Both ordered interacting pairs are
included; the evolution uses the negative of this transport. -/
theorem transport_coeff (p : Polynomial) (k : Frequency) :
    (transport p).coeff k = ∑ l ∈ p.coeff.support,
      (determinant l k : ℂ) / (frequencyWeight l : ℂ) * p.coeff l * p.coeff (k-l) := by
  classical
  simp only [transport, bracket, derivative_streamFunction, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, coefficient_multiplier_mul, derivative_coeff]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [determinant, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast,
    Pi.sub_apply, Int.cast_sub, div_eq_mul_inv]
  linear_combination Complex.I_sq *
    (-(l 0 : ℂ) * (k 1 : ℂ) * (frequencyWeight l : ℂ)⁻¹ * p.coeff l * p.coeff (k-l) +
      (l 1 : ℂ) * (k 0 : ℂ) * (frequencyWeight l : ℂ)⁻¹ * p.coeff l * p.coeff (k-l))


/-- The actual physical lift of finite transport equals the Jacobian of the actual physical lifts
of streamfunction and vorticity, using real coordinate derivatives at every point. -/
theorem physicalLift_transport (p : Polynomial) (x : Fin 2 → ℝ) :
    physicalLift (transport p) x =
      deriv (fun t ↦ physicalLift (streamFunction p) (Function.update x 0 t)) (x 0) *
        deriv (fun t ↦ physicalLift p (Function.update x 1 t)) (x 1) -
      deriv (fun t ↦ physicalLift (streamFunction p) (Function.update x 1 t)) (x 1) *
        deriv (fun t ↦ physicalLift p (Function.update x 0 t)) (x 0) := by
  rw [(hasDerivAt_physicalLift 0 (streamFunction p) x).deriv,
    (hasDerivAt_physicalLift 1 (streamFunction p) x).deriv,
    (hasDerivAt_physicalLift 0 p x).deriv, (hasDerivAt_physicalLift 1 p x).deriv]
  simp [transport, bracket, physicalLift, physical]

/-- The coefficient support of an exact Fourier projection is contained in its retained set. -/
theorem project_support (S : Finset Frequency) (p : Polynomial) :
    (project S p).coeff.support ⊆ S := by
  intro k hk
  by_contra h
  have hn := Finsupp.mem_support_iff.1 hk
  simp [h] at hn

/-- If p is Hermitian and q is supported in S, the sum over S of conj(p_k)q_k is the zero
coefficient of qp. No reality assumption on q is needed. -/
theorem pairing_eq_coeff_zero (S : Finset Frequency) {p q : Polynomial}
    (hp : IsReal p) (hq : q.coeff.support ⊆ S) :
    ∑ k ∈ S, conj (p.coeff k) * q.coeff k = (q*p).coeff 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  have hr (k : Frequency) : p.coeff (-k) = conj (p.coeff k) := hp k
  simp only [Finsupp.sum, add_zero, hr, mul_comm]
  symm
  apply Finset.sum_subset hq
  intro k _ hk
  simp [Finsupp.notMem_support_iff.1 hk]

/-- For Hermitian vorticity supported in a symmetric finite set S, the complex sum of conj(ω_k)
times its projected transport coefficient over S is zero. -/
theorem sum_project_transport_enstrophy_cancel (S : Finset Frequency)
    (hS : ∀ k, k ∈ S ↔ -k ∈ S) {p : Polynomial} (hp : p.coeff.support ⊆ S)
    (hr : IsReal p) :
    ∑ k ∈ S, conj (p.coeff k) * (project S (transport p)).coeff k = 0 := by
  rw [pairing_eq_coeff_zero S hr (project_support _ _), mul_comm,
    project_transport_enstrophy_cancel S hS hp]


/-- For Hermitian vorticity supported in a symmetric finite set S, the complex sum of conj(ω_k)
times projected transport divided by |k|² is zero. The reciprocal at zero is totalized to
zero; zero mean is needed separately for full velocity-vorticity reconstruction. -/
theorem sum_project_transport_energy_cancel (S : Finset Frequency)
    (hS : ∀ k, k ∈ S ↔ -k ∈ S) {p : Polynomial} (hp : p.coeff.support ⊆ S)
    (hr : IsReal p) :
    ∑ k ∈ S, conj (p.coeff k) * (project S (transport p)).coeff k /
      (frequencyWeight k : ℂ) = 0 := by
  have he := pairing_eq_coeff_zero S hr.streamFunction
    (project_support S (transport p))
  rw [mul_comm, project_transport_energy_cancel S hS hp] at he
  calc
    _ = -(∑ k ∈ S, conj ((streamFunction p).coeff k) *
        (project S (transport p)).coeff k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [streamFunction, multiplier_coeff, map_mul, map_neg, map_inv₀,
        Complex.conj_ofReal, div_eq_mul_inv]
      ring
    _ = 0 := by rw [he, neg_zero]

end TorusFourier
