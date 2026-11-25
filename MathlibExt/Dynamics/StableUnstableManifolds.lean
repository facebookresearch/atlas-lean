/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/StableUnstableManifolds.lean` (leanprover/lean-eval):
Copyright (c) Lean FRO.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison (problem submitter).
The adapted portions are the three definitions and the statement of the main theorem.
They come from revision 1 of the problem at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Ring.GeomSum
-- Preserve the instances inferred for `complexEigenvalues` by the original `Mathlib` import.
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Local stable and unstable sets at a hyperbolic fixed point

The local stable and unstable sets of a hyperbolic fixed point intersect only at that point.

On bounded two-sided sequences the shift is an isometry, so subtracting any scalar off the
unit circle gives an operator bounded below. Factoring the characteristic polynomial gives
such a bound for the polynomial in the shift. Cayley–Hamilton then bounds the difference
between the shift and pointwise application of the derivative. Near the fixed point, the
linearization error is too small for a nonconstant full orbit to stay in the neighbourhood.
-/

@[expose] public section

namespace MathlibExt.Dynamics.StableUnstableManifoldsWanted
namespace Dynamics
namespace StableUnstableManifoldsProblem

open scoped Topology
open Filter Polynomial

set_option linter.dupNamespace false in
/-- **Euclidean space $\mathbb{R}^n$ for local stable and unstable sets.** For a natural number
$n$, this is the space $\mathbb{R}^n$ of real $n$-tuples with the Euclidean inner product and
norm. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

set_option linter.dupNamespace false in
/-- **Complex eigenvalues of a real linear map.** For a continuous linear map $L$ from
$\mathbb{R}^n$ to itself, the complex eigenvalues of $L$ form the multiset of complex roots of the
characteristic polynomial of $L$, each counted with its multiplicity as a root. -/
noncomputable def complexEigenvalues {n : ℕ} (L : E n →L[ℝ] E n) : Multiset ℂ :=
  ((L : E n →ₗ[ℝ] E n).charpoly.map (algebraMap ℝ ℂ)).roots

set_option linter.dupNamespace false in
/-- **Hyperbolic linear map.** A continuous linear map $L$ from $\mathbb{R}^n$ to itself is
hyperbolic when none of its complex eigenvalues lies on the unit circle, that is, every complex
root $\mu$ of the characteristic polynomial of $L$ satisfies $|\mu| \ne 1$. -/
def IsHyperbolicLinear {n : ℕ} (L : E n →L[ℝ] E n) : Prop :=
  ∀ μ ∈ complexEigenvalues L, ‖μ‖ ≠ 1

open BoundedContinuousFunction

private noncomputable def orbitShift (𝕜 V : Type*) [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] : (ℤ →ᵇ V) →L[𝕜] (ℤ →ᵇ V) :=
  compContinuousCLM V 𝕜 ⟨fun k => k + 1, continuous_of_discreteTopology⟩

private theorem orbitShift_apply {𝕜 V : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (u : ℤ →ᵇ V) (k : ℤ) :
    orbitShift 𝕜 V u k = u (k + 1) := rfl

private theorem norm_orbitShift {𝕜 V : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (u : ℤ →ᵇ V) :
    ‖orbitShift 𝕜 V u‖ = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · exact norm_compContinuous_le _ _
  refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun k => ?_
  simpa [orbitShift_apply] using (orbitShift 𝕜 V u).norm_coe_le_norm (k - 1)

private theorem root_factor_lower_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (μ : ℂ) (u : ℤ →ᵇ V) :
    |1 - ‖μ‖| * ‖u‖ ≤ ‖aeval (orbitShift ℂ V) (X - Polynomial.C μ) u‖ := by
  rw [map_sub, aeval_X, aeval_C, sub_apply,
    ContinuousLinearMap.algebraMap_apply]
  have h : ‖u‖ - ‖μ‖ * ‖u‖ = (1 - ‖μ‖) * ‖u‖ := by rw [sub_mul, one_mul]
  simpa only [norm_orbitShift, norm_smul, h, abs_mul, abs_norm] using
    abs_norm_sub_norm_le (orbitShift ℂ V u) (μ • u)

private theorem root_product_lower_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ‖ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℤ →ᵇ V,
      c * ‖u‖ ≤ ‖aeval (orbitShift ℂ V) (s.map fun μ => X - Polynomial.C μ).prod u‖ := by
  induction s using Multiset.induction_on with
  | empty =>
    exact ⟨1, zero_lt_one, fun u => by simp [map_one, one_apply_eq_self]⟩
  | cons μ s ih =>
    obtain ⟨c, hc, h⟩ := ih fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    have hμ : 0 < |1 - ‖μ‖| := abs_pos.mpr (sub_ne_zero.mpr (hs μ (by simp)).symm)
    refine ⟨|1 - ‖μ‖| * c, mul_pos hμ hc, fun u => ?_⟩
    let v := aeval (orbitShift ℂ V) (s.map fun a => X - Polynomial.C a).prod u
    simpa only [mul_assoc, Multiset.map_cons, Multiset.prod_cons, map_mul,
      mul_apply_eq_comp] using
      (mul_le_mul_of_nonneg_left (h u) hμ.le).trans (root_factor_lower_bound μ v)

private noncomputable def complexInclusion (n : ℕ) :
    E n →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun x := WithLp.toLp 2 fun i => (x i : ℂ)
  map_add' x y := by ext i; exact Complex.ofReal_add _ _
  map_smul' r x := by ext i; exact Complex.ofReal_mul _ _
  norm_map' x := by simp [EuclideanSpace.norm_eq, Complex.norm_real]

private theorem norm_complexSequence {n : ℕ} (u : ℤ →ᵇ E n) :
    ‖(complexInclusion n).toContinuousLinearMap.compLeftContinuousBounded ℤ u‖ = ‖u‖ := by
  simp only [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContinuousLinearMap.compLeftContinuousBounded_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]

private theorem complexSequence_aeval {n : ℕ} (p : ℝ[X]) (u : ℤ →ᵇ E n) :
    let I := (complexInclusion n).toContinuousLinearMap.compLeftContinuousBounded ℤ
    aeval (orbitShift ℂ (EuclideanSpace ℂ (Fin n))) (p.map (algebraMap ℝ ℂ)) (I u) =
      I (aeval (orbitShift ℝ (E n)) p u) := by
  dsimp only
  let I := (complexInclusion n).toContinuousLinearMap.compLeftContinuousBounded ℤ
  change _ = I _
  have hpow (k : ℕ) :
      (orbitShift ℂ (EuclideanSpace ℂ (Fin n)) ^ k) (I u) =
        I ((orbitShift ℝ (E n) ^ k) u) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ', mul_apply_eq_comp, ih]
      ext1 i
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.map_add, map_add, add_apply, hp, hq]
  | monomial k a =>
    simp only [Polynomial.map_monomial, aeval_monomial, mul_apply_eq_comp,
      ContinuousLinearMap.algebraMap_apply, map_smul]
    change (algebraMap ℝ ℂ) a • ((orbitShift ℂ (EuclideanSpace ℂ (Fin n)) ^ k) (I u)) = _
    rw [hpow, algebraMap_smul]

-- Pointwise application of an endomorphism to a bounded sequence.
private noncomputable def orbitAction (n : ℕ) :
    (E n →ₗ[ℝ] E n) →ₐ[ℝ] ((ℤ →ᵇ E n) →L[ℝ] (ℤ →ᵇ E n)) where
  toFun A := A.toContinuousLinearMap.compLeftContinuousBounded ℤ
  map_zero' := by ext1 u; ext1 k; rfl
  map_one' := by ext1 u; ext1 k; rfl
  map_add' A B := by ext1 u; ext1 k; rfl
  map_mul' A B := by ext1 u; ext1 k; rfl
  commutes' a := by ext1 u; ext1 k; rfl

private theorem aeval_sub_factor {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    {a b : A} (hab : Commute a b) (p : R[X]) :
    ∃ q : A, aeval a p - aeval b p = q * (a - b) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨q, hq⟩ := hp
    obtain ⟨s, hs⟩ := hr
    refine ⟨q + s, ?_⟩
    rw [add_mul, ← hq, ← hs, map_add, map_add]
    abel
  | monomial k r =>
    obtain ⟨q, hq⟩ : ∃ q : A, q * (a - b) = a ^ k - b ^ k := ⟨_, hab.geom_sum₂_mul k⟩
    refine ⟨algebraMap R A r * q, ?_⟩
    rw [aeval_monomial, aeval_monomial, ← mul_sub, mul_assoc, hq]

private theorem orbit_residual_lower_bound {n : ℕ} (A : E n →L[ℝ] E n)
    (hA : IsHyperbolicLinear A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℤ →ᵇ E n,
      ε * ‖u‖ ≤ ‖orbitShift ℝ (E n) u - orbitAction n A.toLinearMap u‖ := by
  let p := A.toLinearMap.charpoly
  let pℂ := p.map (algebraMap ℝ ℂ)
  obtain ⟨c, hc, hbound⟩ := root_product_lower_bound (V := EuclideanSpace ℂ (Fin n)) pℂ.roots hA
  rw [← (IsAlgClosed.splits pℂ).eq_prod_roots_of_monic (A.toLinearMap.charpoly_monic.map _)]
    at hbound
  have hpoly (u : ℤ →ᵇ E n) :
      c * ‖u‖ ≤ ‖aeval (orbitShift ℝ (E n)) p u‖ := by
    simpa only [pℂ, complexSequence_aeval, norm_complexSequence] using
      hbound ((complexInclusion n).toContinuousLinearMap.compLeftContinuousBounded ℤ u)
  let T := orbitAction n A.toLinearMap
  have hT : aeval T p = 0 := by
    rw [aeval_algHom_apply, A.toLinearMap.aeval_self_charpoly, map_zero]
  have hcomm : Commute (orbitShift ℝ (E n)) T := by
    ext1 u
    ext1 k
    rfl
  obtain ⟨Q, hQ⟩ := aeval_sub_factor hcomm p
  rw [hT, sub_zero] at hQ
  refine ⟨c / (‖Q‖ + 1), div_pos hc (by positivity), fun u => ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc
    c * ‖u‖ ≤ ‖aeval (orbitShift ℝ (E n)) p u‖ := hpoly u
    _ ≤ ‖Q‖ * ‖orbitShift ℝ (E n) u - T u‖ := by
      rw [hQ, mul_apply_eq_comp, sub_apply]
      exact Q.le_opNorm _
    _ ≤ ‖orbitShift ℝ (E n) u - T u‖ * (‖Q‖ + 1) := by
      rw [mul_comm]
      gcongr
      linarith

set_option linter.dupNamespace false in
/-- **Local stable and unstable sets at a hyperbolic fixed point.** Let $f : \mathbb{R}^n \to
\mathbb{R}^n$ be continuously differentiable on a neighbourhood of a point $x_0$ with
$f(x_0) = x_0$, and suppose that the derivative $Df(x_0)$ is invertible and hyperbolic. Then
there is an open set $U$ containing $x_0$ such that the local stable set
$W^s = \{x : f^k(x) \in U \text{ for all } k \ge 0 \text{ and } f^k(x) \to x_0 \text{ as }
k \to \infty\}$ and the local unstable set $W^u$, consisting of the points $x$ for which there
is a sequence $(y_k)_{k \ge 0}$ in $U$ with $y_0 = x$, $f(y_{k+1}) = y_k$ for all $k$ and
$y_k \to x_0$, satisfy $W^s \cap W^u = \{x_0\}$.

This is only the set-level part of the Hadamard–Perron theorem: it does not assert that $W^s$
and $W^u$ are $C^1$ submanifolds tangent to the stable and unstable subspaces of $Df(x_0)$.

Source: J. Hadamard, 'Sur l'itération et les solutions asymptotiques des équations différentielles',
Bull. Soc. Math. France 29 (1901); O. Perron, 'Über Stabilität und asymptotisches Verhalten der
Integrale von Differentialgleichungssystemen', Math. Z. 29 (1929) 129–160. Listed as §104 in O.
Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `stable_unstable_manifolds`. -/
public theorem stable_unstable_manifolds_exist (n : ℕ) (f : E n → E n) (x₀ : E n)
    (_hf : ContDiffAt ℝ 1 f x₀)
    (_hfix : f x₀ = x₀)
    (_hhyp : IsHyperbolicLinear (fderiv ℝ f x₀))
    (_hf_inv : (fderiv ℝ f x₀).IsInvertible) :
    ∃ U : Set (E n), IsOpen U ∧ x₀ ∈ U ∧
      ∃ Ws Wu : Set (E n),
        Ws = {x | (∀ k : ℕ, f^[k] x ∈ U) ∧
                  Tendsto (fun k => f^[k] x) atTop (𝓝 x₀)} ∧
        Wu = {x | ∃ y : ℕ → E n,
                    y 0 = x ∧
                    (∀ k : ℕ, y k ∈ U) ∧
                    (∀ k : ℕ, f (y (k + 1)) = y k) ∧
                    Tendsto y atTop (𝓝 x₀)} ∧
        Ws ∩ Wu = {x₀} := by
  let A := fderiv ℝ f x₀
  obtain ⟨ε, hε, hbound⟩ := orbit_residual_lower_bound A _hhyp
  have hε' : 0 < ε / 2 := half_pos hε
  have hderiv : HasFDerivAt f A x₀ := _hf.differentiableAt_one.hasFDerivAt
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff_ball.mp (hderiv.isLittleO.def hε')
  have hx₀ : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  refine ⟨Metric.ball x₀ r, Metric.isOpen_ball, hx₀, _, _, rfl, rfl, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hforward, -⟩, y, hy₀, hy, hbackward, -⟩
    let z : ℤ → E n
      | .ofNat k => f^[k] x
      | .negSucc k => y (k + 1)
    have hz (k : ℤ) : z k ∈ Metric.ball x₀ r := by
      cases k with
      | ofNat k => exact hforward k
      | negSucc k => exact hy (k + 1)
    have hstep (k : ℤ) : z (k + 1) = f (z k) := by
      cases k with
      | ofNat k => exact Function.iterate_succ_apply' f k x
      | negSucc k =>
        cases k with
        | zero => exact hy₀.symm.trans (hbackward 0).symm
        | succ k => exact (hbackward (k + 1)).symm
    let u := ofNormedAddCommGroupDiscrete (fun k : ℤ => z k - x₀) r fun k =>
      (show ‖z k - x₀‖ < r by simpa only [Metric.mem_ball, dist_eq_norm] using hz k).le
    have hres : ‖orbitShift ℝ (E n) u - orbitAction n A.toLinearMap u‖ ≤ ε / 2 * ‖u‖ := by
      refine (BoundedContinuousFunction.norm_le (mul_nonneg hε'.le (norm_nonneg _))).2 fun k => ?_
      change ‖z (k + 1) - x₀ - A (z k - x₀)‖ ≤ ε / 2 * ‖u‖
      rw [hstep]
      simpa only [_hfix] using (hnear (z k) (hz k)).trans
        (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm k) hε'.le)
    have hu : u = 0 := by
      have h := (hbound u).trans hres
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])
    have hz₀ : x - x₀ = 0 := congrArg (fun v : ℤ →ᵇ E n => v 0) hu
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hz₀)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hfixed (k : ℕ) : f^[k] x₀ = x₀ := Function.IsFixedPt.iterate _hfix k
    refine ⟨⟨fun k => by rw [hfixed]; exact hx₀, ?_⟩, fun _ => x₀, rfl, fun _ => hx₀, ?_, ?_⟩
    · simpa only [hfixed] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀))
    · exact fun _ => _hfix
    · exact tendsto_const_nhds

end StableUnstableManifoldsProblem
end Dynamics

end MathlibExt.Dynamics.StableUnstableManifoldsWanted
