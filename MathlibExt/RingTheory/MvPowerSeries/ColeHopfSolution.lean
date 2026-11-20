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
# Formal heat solutions and Cole-Hopf boundary data

Construct a formal heat solution from its entire time-zero slice, then identify
its Cole-Hopf transform as the unique formal Burgers solution with the transformed
boundary. Time and space axes must be distinct; coefficients have characteristic
zero. These are formal identities, without an analytic convergence claim.
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

end MvPowerSeries.ColeHopf
