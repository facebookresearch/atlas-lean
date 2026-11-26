/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Ensemble Kalman inversion: invariant subspace and ensemble collapse

Ensemble Kalman inversion (EKI) solves an inverse problem `y = G(u) + η`, with unknown `u` in a
real vector space `X` and data in a real inner product space `F`, by moving an ensemble
`u⁽¹⁾, …, u⁽ᴶ⁾` with the Kalman update

`u⁽ʲ⁾ₙ₊₁ = u⁽ʲ⁾ₙ + C^{up}(uₙ) (C^{pp}(uₙ) + Γ)⁻¹ (y⁽ʲ⁾ₙ₊₁ - G(u⁽ʲ⁾ₙ))`,

where, with ensemble means `ū` and `Ḡ = (1/J) Σ G(u⁽ᵏ⁾)`,

* `C^{up}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (u⁽ᵏ⁾ - ū)` is the cross-covariance,
* `C^{pp}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (G(u⁽ᵏ⁾) - Ḡ)` is the output covariance,

and `y⁽ʲ⁾ₙ₊₁` are the (possibly perturbed) data (Iglesias, Law and Stuart, *Ensemble Kalman
methods for inverse problems*, Inverse Problems 29 (2013), arXiv:1209.2736, equations (19)-(25);
Schillings and Stuart, *Analysis of the ensemble Kalman filter for inverse problems*, SIAM J.
Numer. Anal. 55 (2017), arXiv:1602.02020, equations (4)-(5), where `Γ` is replaced by `h⁻¹Γ`).

## Main results

* `ekiStep`: one EKI update. The inverse of `C^{pp} + Γ` is `Ring.inverse` in the endomorphism
  ring of `F`, which is the true inverse whenever `C^{pp} + Γ` is invertible (for instance
  when `F` is finite-dimensional and `Γ` is positive definite).
* `ekiStep_mem` and `eki_mem_span` (**invariant subspace property**, Iglesias-Law-Stuart
  Theorem 2.1; Schillings-Stuart Lemma 1): every ensemble member, at every step, lies in the
  linear span of the initial ensemble. This holds for every forward map `G`, every `Γ` and every
  choice of perturbed data.
* `infDist_le_dist_ensembleMean` (Iglesias-Law-Stuart Corollary 2.3): the error of the ensemble
  mean is at least the distance from the truth to that span.
* `MathlibExt.Probability.EnsembleKalmanWanted.eki_ensemble_collapse` (Schillings-Stuart Theorem 3):
  for the continuous-time linear, noise-free flow, each observed spread entry is bounded by
  `J / (2 * t)` in absolute value at every positive time.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.BayesianInverse

open scoped InnerProductSpace

variable {X F : Type*} [AddCommGroup X] [Module ℝ X] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {J : ℕ}

/-- **Ensemble mean.** `(1/J) Σⱼ v⁽ʲ⁾` for an ensemble `v : Fin J → X` of `J ≥ 1` members. For
an empty ensemble (`J = 0`) the value is `0` (`0⁻¹ = 0`), which is not a mean of any members. -/
noncomputable def ensembleMean {V : Type*} [AddCommGroup V] [Module ℝ V] (v : Fin J → V) : V :=
  (J : ℝ)⁻¹ • ∑ j, v j

/-- **EKI cross-covariance applied to a vector.**
`C^{up}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (u⁽ᵏ⁾ - ū)` (Schillings and Stuart, arXiv:1602.02020,
equation (5); Iglesias, Law and Stuart, arXiv:1209.2736, equations (20) and (22)). For an empty
ensemble (`J = 0`) it is `0`, not an empirical covariance. -/
noncomputable def crossCov (G : X → F) (u : Fin J → X) (d : F) : X :=
  (J : ℝ)⁻¹ • ∑ k, ⟪G (u k) - ensembleMean (G ∘ u), d⟫_ℝ • (u k - ensembleMean u)

/-- **EKI output covariance.** The linear map
`C^{pp}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (G(u⁽ᵏ⁾) - Ḡ)` (Schillings and Stuart,
arXiv:1602.02020, equation (5); Iglesias, Law and Stuart, arXiv:1209.2736, equation (21)). For an
empty ensemble (`J = 0`) it is the zero map, not an empirical covariance. -/
noncomputable def outputCov (G : X → F) (u : Fin J → X) : F →ₗ[ℝ] F where
  toFun d := (J : ℝ)⁻¹ • ∑ k, ⟪G (u k) - ensembleMean (G ∘ u), d⟫_ℝ •
    (G (u k) - ensembleMean (G ∘ u))
  map_add' d₁ d₂ := by
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' c d := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1; ring

/-- **One step of ensemble Kalman inversion.**
`u⁽ʲ⁾ ↦ u⁽ʲ⁾ + C^{up}(u) (C^{pp}(u) + Γ)⁻¹ (y⁽ʲ⁾ - G(u⁽ʲ⁾))`, with the inverse taken by
`Ring.inverse` in `F →ₗ[ℝ] F` (Iglesias, Law and Stuart, arXiv:1209.2736, equation (25);
Schillings and Stuart, arXiv:1602.02020, equation (4) with `Γ ↦ h⁻¹Γ`). -/
noncomputable def ekiStep (G : X → F) (Γ : F →ₗ[ℝ] F) (u : Fin J → X) (y : Fin J → F) :
    Fin J → X :=
  fun j ↦ u j + crossCov G u (Ring.inverse (outputCov G u + Γ) (y j - G (u j)))

/-- **The ensemble mean stays in a subspace.** The ensemble mean of members of a subspace lies in
that subspace. -/
theorem ensembleMean_mem {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    {v : Fin J → V} (hv : ∀ j, v j ∈ S) : ensembleMean v ∈ S :=
  S.smul_mem _ (S.sum_mem fun j _ ↦ hv j)

/-- **The cross-covariance stays in the ensemble's subspace.** The cross-covariance of an ensemble
in a subspace takes values in that subspace: it is a
linear combination of the deviations `u⁽ᵏ⁾ - ū`. -/
theorem crossCov_mem (S : Submodule ℝ X) (G : X → F) {u : Fin J → X} (hu : ∀ j, u j ∈ S)
    (d : F) : crossCov G u d ∈ S :=
  S.smul_mem _ (S.sum_mem fun k _ ↦ S.smul_mem _ (S.sub_mem (hu k) (ensembleMean_mem S hu)))

/-- **One EKI step preserves every subspace containing the ensemble.** If every `u⁽ʲ⁾` lies in a
subspace `S`, so does every member of `ekiStep G Γ u y`, for any forward map `G`, any `Γ` and any
data `y` (the inductive step in the proof of Theorem 2.1 of Iglesias, Law and Stuart,
arXiv:1209.2736). -/
theorem ekiStep_mem (S : Submodule ℝ X) (G : X → F) (Γ : F →ₗ[ℝ] F) {u : Fin J → X}
    (hu : ∀ j, u j ∈ S) (y : Fin J → F) (j : Fin J) : ekiStep G Γ u y j ∈ S :=
  S.add_mem (hu j) (crossCov_mem S G hu _)

/-- **Invariant subspace property of ensemble Kalman inversion.** If `uₙ₊₁ = ekiStep G Γ uₙ yₙ₊₁`
for all `n`, then every ensemble member `u⁽ʲ⁾ₙ` lies in the linear span of the initial ensemble
`{u⁽¹⁾₀, …, u⁽ᴶ⁾₀}` (Iglesias, Law and Stuart, arXiv:1209.2736, Theorem 2.1; Schillings and
Stuart, arXiv:1602.02020, Lemma 1). -/
theorem eki_mem_span (G : X → F) (Γ : F →ₗ[ℝ] F) (u : ℕ → Fin J → X) (y : ℕ → Fin J → F)
    (hstep : ∀ n, u (n + 1) = ekiStep G Γ (u n) (y (n + 1))) (n : ℕ) (j : Fin J) :
    u n j ∈ Submodule.span ℝ (Set.range (u 0)) := by
  induction n generalizing j with
  | zero => exact Submodule.subset_span ⟨j, rfl⟩
  | succ n ih => rw [hstep n]; exact ekiStep_mem _ G Γ ih _ j

/-- **The EKI estimate cannot beat the best approximation from the initial span.** With
`uₙ₊₁ = ekiStep G Γ uₙ yₙ₊₁`, the ensemble mean satisfies
`‖ūₙ - u†‖ ≥ inf_{v ∈ A} ‖v - u†‖`, where `A` is the span of the initial ensemble (Iglesias, Law
and Stuart, arXiv:1209.2736, Corollary 2.3). -/
theorem infDist_le_dist_ensembleMean {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → F) (Γ : F →ₗ[ℝ] F) (u : ℕ → Fin J → X) (y : ℕ → Fin J → F)
    (hstep : ∀ n, u (n + 1) = ekiStep G Γ (u n) (y (n + 1))) (n : ℕ) (u_true : X) :
    Metric.infDist u_true (Submodule.span ℝ (Set.range (u 0)) : Set X) ≤
      ‖ensembleMean (u n) - u_true‖ := by
  rw [← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem
    (ensembleMean_mem _ fun j ↦ eki_mem_span G Γ u y hstep n j)

end MathlibExt.Probability.BayesianInverse

namespace MathlibExt.Probability.EnsembleKalmanWanted

open MathlibExt.Probability.BayesianInverse Set
open scoped InnerProductSpace

/-- Scalar decay on the open positive half-line, with no initial condition at zero. -/
private theorem le_inv_mul_of_deriv_le_neg_sq {g g' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hderiv : ∀ s > 0, HasDerivAt g (g' s) s)
    (hineq : ∀ s > 0, g' s ≤ -c * (g s) ^ 2) {t : ℝ} (ht : 0 < t) :
    g t ≤ (c * t)⁻¹ := by
  by_cases hgt : 0 < g t
  · have hanti : AntitoneOn g (Ioi 0) :=
      antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
        (fun r hr ↦ (hderiv r hr).continuousAt.continuousWithinAt)
        (fun r hr ↦ (hderiv r (interior_subset hr)).differentiableAt.differentiableWithinAt)
        (fun r hr ↦ by
          rw [(hderiv r (interior_subset hr)).deriv]
          exact (hineq r (interior_subset hr)).trans
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)))
    have hcompare (s : ℝ) (hs : 0 < s) (hst : s < t) : c * (t - s) ≤ (g t)⁻¹ := by
      have hpos (r : ℝ) (hr : r ∈ Icc s t) : 0 < g r :=
        hgt.trans_le (hanti (hs.trans_le hr.1) ht hr.2)
      let q : ℝ → ℝ := fun r ↦ (g r)⁻¹ - c * r
      have hq (r : ℝ) (hr : r ∈ Icc s t) :
          HasDerivAt q (-g' r / (g r) ^ 2 - c) r := by
        have hlin : HasDerivAt (fun x : ℝ ↦ c * x) c r := by
          simpa only [mul_one] using (hasDerivAt_id' r).const_mul c
        exact ((hderiv r (hs.trans_le hr.1)).fun_inv (hpos r hr).ne').fun_sub hlin
      have hmono : MonotoneOn q (Icc s t) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t)
          (fun r hr ↦ (hq r hr).continuousAt.continuousWithinAt)
          (fun r hr ↦ (hq r (interior_subset hr)).hasDerivWithinAt)
          (fun r hr ↦ by
            rw [sub_nonneg, le_div_iff₀ (pow_pos (hpos r (interior_subset hr)) 2)]
            linarith only [hineq r (hs.trans_le (interior_subset hr).1)])
      have hst' : q s ≤ q t := hmono (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) hst.le
      dsimp [q] at hst'
      linarith only [hst', inv_nonneg.mpr (hpos s (left_mem_Icc.mpr hst.le)).le]
    -- Send the starting time down to zero in the bound, not in `g`.
    have hbound : c * t ≤ (g t)⁻¹ := by
      by_contra! h
      have hgap : 0 < t - (g t)⁻¹ / c := by
        rw [sub_pos, div_lt_iff₀ hc, mul_comm t c]
        exact h
      obtain ⟨s, hs, hs'⟩ := exists_between hgap
      have hst := hs'.trans_le (sub_le_self t (div_nonneg (inv_nonneg.mpr hgt.le) hc.le))
      have hlt : (g t)⁻¹ / c < t - s := by linarith only [hs']
      rw [div_lt_iff₀ hc, mul_comm (t - s) c] at hlt
      exact (not_lt_of_ge (hcompare s hs hst)) hlt
    exact (le_inv_comm₀ hgt (mul_pos hc ht)).mpr hbound
  · exact (not_lt.mp hgt).trans (inv_nonneg.mpr (mul_nonneg hc.le ht.le))

section EnsembleKalman

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

-- The wanted placeholder did not include these unused section instances in its type.
omit [CompleteSpace X] [FiniteDimensional ℝ Y] in
/-- **Ensemble collapse for continuous-time ensemble Kalman inversion.** Let `A : X → Y` be
bounded linear, `Γ` a positive invertible covariance on `Y` with
`⟨a, b⟩_Γ = ⟨a, Γ⁻¹ b⟩`, and data `y = A u†` without noise. If the ensemble
`u⁽¹⁾(t), …, u⁽ᴶ⁾(t)` solves, for `t > 0`, the continuous-time EKI equations
`du⁽ʲ⁾/dt = (1/J) Σₖ ⟨A(u⁽ᵏ⁾ - ū), y - A u⁽ʲ⁾⟩_Γ (u⁽ᵏ⁾ - ū)`,
then for every `t > 0` every entry `E_{lj}(t) = ⟨A e⁽ˡ⁾, A e⁽ʲ⁾⟩_Γ` of the spread matrix, with
`e⁽ʲ⁾ = u⁽ʲ⁾ - ū`, satisfies `|E_{lj}(t)| ≤ J / (2t)` (Schillings and Stuart, *Analysis of the
ensemble Kalman filter for inverse problems*, SIAM J. Numer. Anal. 55 (2017), arXiv:1602.02020,
equation (8) and Theorem 3). The theorem states `‖E(t)‖ = O(J t⁻¹)`; the explicit bound is what
its proof gives: `E` solves `dE/dt = -(2/J) E²`, so its eigenvalues are
`(2(t - s)/J + 1/λ(s))⁻¹ ≤ J/(2(t - s))` for `0 < s < t` (or `0`), and the entries of a positive
semidefinite matrix are bounded by its largest eigenvalue. -/
theorem eki_ensemble_collapse {J : ℕ} (A : X →L[ℝ] Y) (Γ : Y ≃L[ℝ] Y)
    (hΓ : (Γ : Y →L[ℝ] Y).IsPositive) (u_true : X) (u : ℝ → Fin J → X)
    (hode : ∀ t > 0, ∀ j, HasDerivAt (fun s ↦ u s j)
      ((J : ℝ)⁻¹ • ∑ k, ⟪A (u t k - ensembleMean (u t)), Γ.symm (A u_true - A (u t j))⟫_ℝ •
        (u t k - ensembleMean (u t))) t)
    (l j : Fin J) {t : ℝ} (ht : 0 < t) :
    |⟪A (u t l - ensembleMean (u t)), Γ.symm (A (u t j - ensembleMean (u t)))⟫_ℝ| ≤
      (J : ℝ) / (2 * t) := by
  have hJ : 0 < (J : ℝ) := by exact_mod_cast l.pos
  let B : Y → Y → ℝ := fun x y ↦ ⟪x, Γ.symm y⟫_ℝ
  have hΓinv : (Γ.symm : Y →L[ℝ] Y).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
      (LinearMap.IsPositive.toLinearMap_symm (T := Γ.toLinearEquiv) hΓ.toLinearMap)
  have hsym (x y : Y) : B x y = B y x :=
    (hΓinv.inner_left_eq_inner_right x y).symm.trans (real_inner_comm _ _)
  have hnonneg (x : Y) : 0 ≤ B x x := hΓinv.inner_nonneg_right x
  let v : ℝ → Fin J → Y := fun s i ↦ A (u s i - ensembleMean (u s))
  let Q : ℝ → Y →ₗ[ℝ] Y := fun s ↦
    (outputCov (fun x ↦ A x) (u s)).comp Γ.symm.toLinearEquiv.toLinearMap
  have hmean (s : ℝ) : ensembleMean (fun i ↦ A (u s i)) = A (ensembleMean (u s)) := by
    simp [ensembleMean, map_sum]
  have hQ (s : ℝ) (z : Y) : Q s z = (J : ℝ)⁻¹ • ∑ k, B (v s k) z • v s k := by
    change (J : ℝ)⁻¹ • ∑ k, ⟪A (u s k) - ensembleMean (fun i ↦ A (u s i)), Γ.symm z⟫_ℝ •
      (A (u s k) - ensembleMean (fun i ↦ A (u s i))) = _
    simp only [hmean, B, v, map_sub]
  have hcenter (s : ℝ) : ∑ i, v s i = 0 := by
    simp only [v, map_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [← hmean s]
    simp only [ensembleMean, smul_smul, mul_inv_cancel₀ hJ.ne', one_smul, sub_self]
  -- At each time, the derivative of the mean is the common forcing term.
  let f : ℝ → Y := fun s ↦ Q s (A u_true - A (ensembleMean (u s)))
  have hobs (s : ℝ) (hs : 0 < s) (i : Fin J) :
      HasDerivAt (fun r ↦ A (u r i)) (f s - Q s (v s i)) s := by
    have h := A.hasFDerivAt.comp_hasDerivAt s (hode s hs i)
    have hres : A u_true - A (u s i) = (A u_true - A (ensembleMean (u s))) - v s i := by
      change A u_true - A (u s i) = _ - A (u s i - ensembleMean (u s))
      rw [map_sub]
      abel
    simp only [map_smul, map_sum] at h
    change HasDerivAt (fun r ↦ A (u r i))
      ((J : ℝ)⁻¹ • ∑ k, B (v s k) (A u_true - A (u s i)) • v s k) s at h
    rw [← hQ, hres, map_sub] at h
    exact h
  have hm (s : ℝ) (hs : 0 < s) : HasDerivAt (fun r ↦ A (ensembleMean (u r))) (f s) s := by
    have hsum : ∑ i, Q s (v s i) = 0 := by rw [← map_sum, hcenter, map_zero]
    have h := (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ hobs s hs i)).fun_const_smul (J : ℝ)⁻¹
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hJ.ne', one_smul] at h
    change HasDerivAt (fun r ↦ ensembleMean (fun i ↦ A (u r i))) (f s) s at h
    simpa only [hmean] using h
  have hv (s : ℝ) (hs : 0 < s) (i : Fin J) : HasDerivAt (fun r ↦ v r i) (-Q s (v s i)) s := by
    simpa only [v, map_sub, sub_sub_cancel_left] using (hobs s hs i).fun_sub (hm s hs)
  let E : ℝ → Fin J → Fin J → ℝ := fun s i k ↦ B (v s i) (v s k)
  have hEsymm (s : ℝ) (i k : Fin J) : E s i k = E s k i := hsym _ _
  have hcontract (s : ℝ) (i k : Fin J) : B (v s i) (Q s (v s k)) =
      (J : ℝ)⁻¹ * ∑ a, E s i a * E s a k := by
    rw [hQ]
    simp only [B, map_smul, map_sum, real_inner_smul_right, inner_sum, E]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  -- This is the spread equation `E' = -(2/J) E²`, entry by entry.
  have hE (s : ℝ) (hs : 0 < s) (i k : Fin J) : HasDerivAt (fun r ↦ E r i k)
      (-(2 / (J : ℝ)) * ∑ a, E s i a * E s a k) s := by
    have hΓv := (Γ.symm : Y →L[ℝ] Y).hasFDerivAt.comp_hasDerivAt s (hv s hs k)
    have h := (hv s hs i).inner ℝ hΓv
    change HasDerivAt (fun r ↦ E r i k)
      (B (v s i) (-Q s (v s k)) + B (-Q s (v s i)) (v s k)) s at h
    have hneg (x z : Y) : B x (-z) = -B x z := by simp [B]
    have hsum : ∑ a, E s k a * E s a i = ∑ a, E s i a * E s a k := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hEsymm s k a, hEsymm s a i, mul_comm]
    rw [hsym (-Q s (v s i)) (v s k), hneg, hneg, hcontract, hcontract, hsum] at h
    convert h using 1
    ring
  have hdiag (i : Fin J) : E t i i ≤ (J : ℝ) / (2 * t) := by
    have hc : 0 < 2 / (J : ℝ) := div_pos (by norm_num) hJ
    have hdecay (s : ℝ) (_hs : 0 < s) :
        -(2 / (J : ℝ)) * (∑ a, E s i a * E s a i) ≤ -(2 / (J : ℝ)) * (E s i i) ^ 2 := by
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hc.le)
      rw [pow_two]
      refine Finset.single_le_sum (f := fun a ↦ E s i a * E s a i) ?_ (Finset.mem_univ i)
      intro a _
      rw [hEsymm s a i]
      exact mul_self_nonneg _
    have hb := le_inv_mul_of_deriv_le_neg_sq hc (fun s hs ↦ hE s hs i i) hdecay ht
    rwa [div_mul_eq_mul_div, inv_div] at hb
  have hentry (x y : Y) : |B x y| ≤ (B x x + B y y) / 2 := by
    have hadd := hnonneg (x + y)
    have hsub := hnonneg (x - y)
    simp only [B, map_add, inner_add_left, inner_add_right] at hadd
    simp only [B, map_sub, inner_sub_left, inner_sub_right] at hsub
    have hxy := hsym x y
    dsimp only [B] at hxy ⊢
    exact abs_le.mpr ⟨by linarith only [hadd, hxy], by linarith only [hsub, hxy]⟩
  change |E t l j| ≤ (J : ℝ) / (2 * t)
  calc
    |E t l j| ≤ (E t l l + E t j j) / 2 := hentry _ _
    _ ≤ (J : ℝ) / (2 * t) := by linarith only [hdiag l, hdiag j]

end EnsembleKalman

end MathlibExt.Probability.EnsembleKalmanWanted
