/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.CausalEquation
public import MathlibExt.RingTheory.MvPowerSeries.ColeHopf

/-!
# Formal Cole–Hopf initial-value theory

Construct a formal heat solution from its entire time-zero slice, then identify
its Cole-Hopf transform as the unique formal Burgers solution with the transformed
boundary. For nonzero viscosity, the normalized inverse spatial ODE constructs
heat initial data for arbitrary Burgers initial data. Time and space axes must
be distinct; coefficients have characteristic zero. These are formal identities,
without an analytic convergence claim.

Mathematical reference: F. Gesztesy and H. Holden, The Cole-Hopf and Miura
Transformations Revisited, Theorem 3.3 and Remark 3.5,
https://arxiv.org/abs/solv-int/9812025. The inverse exponential-integral profile is
implemented by its normalized spatial linear ODE. Formal Picard existence and
uniqueness supply both the profile and heat evolution. This formal construction
does not assert the source's analytic regularity, positivity or convergence.
-/

@[expose] public section

namespace MvPowerSeries.ColeHopf

open Causal

variable {σ K : Type*} [Field K]

/-- The formal heat operator along the spatial axis. -/
noncomputable def heatRhs (ν : K) (x : σ) (φ : MvPowerSeries σ K) : MvPowerSeries σ K :=
  C ν * pderiv x (pderiv x φ)

/-- The formal viscous Burgers operator along the spatial axis. -/
noncomputable def burgersRhs (ν : K) (x : σ) (u : MvPowerSeries σ K) : MvPowerSeries σ K :=
  heatRhs ν x u - u * pderiv x u

/-- Spatial heat evolution is causal along a distinct time axis. -/
theorem heat_isCausal {t x : σ} (hxt : x ≠ t) (ν : K) :
    IsCausal t (heatRhs ν x) := by
  intro k a b h
  exact (Agree.refl t k (C ν)).mul ((h.pderiv hxt).pderiv hxt)

/-- The nonlinear Burgers operator is causal along a distinct time axis. -/
theorem burgers_isCausal {t x : σ} (hxt : x ≠ t) (ν : K) :
    IsCausal t (burgersRhs ν x) := by
  intro k a b h n hn
  have hd := heat_isCausal hxt ν k a b h
  have hm := h.mul (h.pderiv hxt)
  simp only [burgersRhs, map_sub, hd n hn, hm n hn]

private theorem agree_inv {t : σ} {k : ℕ} {a b : MvPowerSeries σ K}
    (h : Agree t k a b) (hb : constantCoeff b ≠ 0) : Agree t k a⁻¹ b⁻¹ := by
  have hc : constantCoeff a = constantCoeff b := by
    simpa only [coeff_zero_eq_constantCoeff_apply] using h 0 (by simp)
  have ha : constantCoeff a ≠ 0 := hc.trans_ne hb
  have hi := (Agree.refl t k b⁻¹).mul (h.mul (Agree.refl t k a⁻¹))
  rw [MvPowerSeries.mul_inv_cancel a ha, mul_one, ← mul_assoc,
    MvPowerSeries.inv_mul_cancel b hb, one_mul] at hi
  exact hi.symm

/-- Cole-Hopf preserves agreement in time when the boundary is invertible. -/
theorem coleHopf_agree {t x : σ} (hxt : x ≠ t) {ν : K} {k : ℕ}
    {a b : MvPowerSeries σ K} (h : Agree t k a b) (hb : constantCoeff b ≠ 0) :
    Agree t k (coleHopf ν x a) (coleHopf ν x b) :=
  (Agree.refl t k (C (-2 * ν))).mul ((h.pderiv hxt).mul (agree_inv h hb))

/-- The stabilized formal heat solution with the time-zero slice of `b`. -/
noncomputable def heatSolution (ν : K) (t x : σ) (b : MvPowerSeries σ K) :
    MvPowerSeries σ K := Causal.solution t (heatRhs ν x) b

/-- Every coefficient of the prescribed time-zero slice is preserved. -/
theorem heatSolution_slice {ν : K} {t x : σ} {b : MvPowerSeries σ K}
    (n : σ →₀ ℕ) (hn : n t = 0) :
    coeff n (heatSolution ν t x b) = coeff n b :=
  Causal.solution_slice n hn

/-- In particular, the heat solution has the boundary's constant coefficient. -/
@[simp] theorem constantCoeff_heatSolution (ν : K) (t x : σ) (b : MvPowerSeries σ K) :
    constantCoeff (heatSolution ν t x b) = constantCoeff b := by
  simpa only [coeff_zero_eq_constantCoeff_apply] using
    heatSolution_slice (ν := ν) (t := t) (x := x) (b := b) 0 (by simp)

/-- The constructed series solves the heat equation, without assuming a solution. -/
theorem heatSolution_pde [CharZero K] {t x : σ} (hxt : x ≠ t)
    (ν : K) (b : MvPowerSeries σ K) :
    pderiv t (heatSolution ν t x b) = heatRhs ν x (heatSolution ν t x b) :=
  Causal.solution_pde (heat_isCausal hxt ν)

/-- The formal heat equation and its entire boundary slice determine the solution. -/
theorem heatSolution_unique [CharZero K] {t x : σ} (hxt : x ≠ t)
    {ν : K} {b u : MvPowerSeries σ K}
    (hu : pderiv t u = heatRhs ν x u)
    (hb : ∀ n : σ →₀ ℕ, n t = 0 → coeff n u = coeff n b) :
    u = heatSolution ν t x b := by
  apply Causal.formal_unique (heat_isCausal hxt ν) u _ hu (heatSolution_pde hxt ν b)
  intro n hn
  exact (hb n (Nat.eq_zero_of_le_zero hn)).trans
    (heatSolution_slice n (Nat.eq_zero_of_le_zero hn)).symm

/-- The transform of the constructed heat solution solves formal Burgers. -/
theorem coleHopf_heatSolution_pde [CharZero K] {t x : σ} (hxt : x ≠ t)
    {ν : K} {b : MvPowerSeries σ K} (hb : constantCoeff b ≠ 0) :
    pderiv t (coleHopf ν x (heatSolution ν t x b)) =
      burgersRhs ν x (coleHopf ν x (heatSolution ν t x b)) :=
  pderiv_coleHopf_of_heat ν t x _ (by simpa using hb) (heatSolution_pde hxt ν b)

/-- Its whole initial slice is the Cole-Hopf transform of the supplied boundary. -/
theorem coleHopf_heatSolution_slice {t x : σ} (hxt : x ≠ t)
    {ν : K} {b : MvPowerSeries σ K} (hb : constantCoeff b ≠ 0)
    (n : σ →₀ ℕ) (hn : n t = 0) :
    coeff n (coleHopf ν x (heatSolution ν t x b)) = coeff n (coleHopf ν x b) := by
  have hs : Agree t 0 (heatSolution ν t x b) b :=
    fun m hm => heatSolution_slice m (Nat.eq_zero_of_le_zero hm)
  exact coleHopf_agree hxt hs hb n hn.le

/-- Cole-Hopf agrees with the canonical causal Burgers solution for its boundary. -/
theorem coleHopf_heatSolution_eq_solution [CharZero K] {t x : σ} (hxt : x ≠ t)
    {ν : K} {b : MvPowerSeries σ K} (hb : constantCoeff b ≠ 0) :
    coleHopf ν x (heatSolution ν t x b) =
      Causal.solution t (burgersRhs ν x) (coleHopf ν x b) := by
  apply Causal.formal_unique (burgers_isCausal hxt ν) _ _
    (coleHopf_heatSolution_pde hxt hb) (Causal.solution_pde (burgers_isCausal hxt ν))
  intro n hn
  exact (coleHopf_heatSolution_slice hxt hb n (Nat.eq_zero_of_le_zero hn)).trans
    (Causal.solution_slice n (Nat.eq_zero_of_le_zero hn)).symm

/-- The constructed transform is the unique formal Burgers solution for this slice. -/
theorem existsUnique_burgers_of_heat_boundary [CharZero K] {t x : σ} (hxt : x ≠ t)
    {ν : K} {b : MvPowerSeries σ K} (hb : constantCoeff b ≠ 0) :
    ∃! u : MvPowerSeries σ K, pderiv t u = burgersRhs ν x u ∧
      ∀ n : σ →₀ ℕ, n t = 0 → coeff n u = coeff n (coleHopf ν x b) := by
  refine ⟨coleHopf ν x (heatSolution ν t x b),
    ⟨coleHopf_heatSolution_pde hxt hb, coleHopf_heatSolution_slice hxt hb⟩, ?_⟩
  intro u hu
  apply Causal.formal_unique (burgers_isCausal hxt ν) _ _ hu.1
    (coleHopf_heatSolution_pde hxt hb)
  intro n hn
  exact (hu.2 n (Nat.eq_zero_of_le_zero hn)).trans
    (coleHopf_heatSolution_slice hxt hb n (Nat.eq_zero_of_le_zero hn)).symm

/-- The formal Burgers initial-value problem has a unique solution for every
viscosity, including zero. Only the entire time-zero slice of `v` is used. -/
theorem existsUnique_burgers [CharZero K] {t x : σ} (hxt : x ≠ t)
    (ν : K) (v : MvPowerSeries σ K) :
    ∃! u : MvPowerSeries σ K, pderiv t u = burgersRhs ν x u ∧
      ∀ n : σ →₀ ℕ, n t = 0 → coeff n u = coeff n v :=
  Causal.existsUnique_solution (burgers_isCausal hxt ν) v

/-- The normalized inverse Cole–Hopf profile. It solves the spatial linear
ODE `∂ₓb = -v b / (2ν)` in characteristic zero, with the entire spatial zero
slice equal to `1`.
For nonzero viscosity, this is the formal counterpart of `exp(-∫v/(2ν))`.
Time, if present, is a parameter here; this profile need not solve heat. -/
noncomputable def initialHeatProfile (ν : K) (x : σ) (v : MvPowerSeries σ K) :
    MvPowerSeries σ K :=
  Causal.solution x (fun b => C (-(2 * ν)⁻¹) * v * b) 1

/-- The entire spatial zero slice of the inverse profile is normalized to `1`;
all other axes are parameters in this spatial initial-value problem. -/
theorem initialHeatProfile_slice (ν : K) (x : σ) (v : MvPowerSeries σ K)
    (n : σ →₀ ℕ) (hn : n x = 0) :
    coeff n (initialHeatProfile ν x v) = coeff n (1 : MvPowerSeries σ K) :=
  Causal.solution_slice n hn

/-- The normalized profile has invertible constant coefficient. -/
@[simp] theorem constantCoeff_initialHeatProfile (ν : K) (x : σ)
    (v : MvPowerSeries σ K) : constantCoeff (initialHeatProfile ν x v) = 1 := by
  change coeff 0 (initialHeatProfile ν x v) = 1
  rw [initialHeatProfile_slice ν x v 0 (by simp)]
  simp

/-- The normalized inverse profile satisfies its defining spatial ODE. -/
theorem initialHeatProfile_pderiv [CharZero K] (ν : K) (x : σ)
    (v : MvPowerSeries σ K) :
    pderiv x (initialHeatProfile ν x v) =
      C (-(2 * ν)⁻¹) * v * initialHeatProfile ν x v := by
  apply Causal.solution_pde
  intro k a b h
  exact (Agree.refl x k (C (-(2 * ν)⁻¹) * v)).mul h

/-- Nonzero viscosity makes the normalized spatial construction a right inverse
of the Cole–Hopf transform, for arbitrary formal data. -/
theorem coleHopf_initialHeatProfile [CharZero K] {ν : K} (hν : ν ≠ 0)
    (x : σ) (v : MvPowerSeries σ K) :
    coleHopf ν x (initialHeatProfile ν x v) = v := by
  have hc : constantCoeff (initialHeatProfile ν x v) ≠ 0 := by simp
  have hscale : (C (-2 * ν) : MvPowerSeries σ K) * C (-(2 * ν)⁻¹) = 1 := by
    rw [← map_mul]
    have hν2 : 2 * ν ≠ 0 := mul_ne_zero two_ne_zero hν
    rw [show -2 * ν * -(2 * ν)⁻¹ = 1 by
      rw [neg_mul, neg_mul_neg, mul_inv_cancel₀ hν2]]
    exact map_one C
  rw [coleHopf, initialHeatProfile_pderiv, mul_assoc (C (-(2 * ν)⁻¹) * v),
    MvPowerSeries.mul_inv_cancel _ hc, mul_one, ← mul_assoc, hscale, one_mul]

/-- For arbitrary Burgers initial data and nonzero viscosity, normalize the
inverse profile, solve heat, and transform back. The result is the canonical
formal Burgers solution with the supplied entire time-zero slice. -/
theorem coleHopf_heatSolution_initialHeatProfile [CharZero K] {t x : σ}
    (hxt : x ≠ t) {ν : K} (hν : ν ≠ 0) (v : MvPowerSeries σ K) :
    coleHopf ν x (heatSolution ν t x (initialHeatProfile ν x v)) =
      Causal.solution t (burgersRhs ν x) v := by
  rw [coleHopf_heatSolution_eq_solution hxt (by simp), coleHopf_initialHeatProfile hν]

end MvPowerSeries.ColeHopf
