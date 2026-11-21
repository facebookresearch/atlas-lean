/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Bloch's theorem (universal schlicht disc)
-/

namespace MathlibExt.Analysis.Complex.BlochWanted

/--
**Bloch's theorem.** There is a constant $B > 0$ with the following property. Let
$f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$
with $f'(0) = 1$. Then there are an open connected set $V \subseteq \mathbb{D}$ and a point
$w \in \mathbb{C}$ such that $f$ is injective on $V$ and $f(V)$ is the open disc
$\{\zeta : |\zeta - w| < B\}$.

Source: A. Bloch, Les théorèmes de M. Valiron sur les fonctions entières et la
théorie de l'uniformisation, Ann. Fac. Sci. Toulouse 17 (1925), 1–22, DOI 10.5802/afst.335; see
Ahlfors, Complex Analysis, Univalent Functions; Lean is universal B > 0 exact schlicht disc
f '' V = ball w B for open connected V, stronger than Landau.

Proves `Wanted` entry `bloch`.
-/
theorem bloch
    : ∃ B : ℝ, 0 < B ∧
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) → deriv f 0 = 1 →
        ∃ V : Set ℂ, ∃ w : ℂ,
          IsOpen V ∧ V ⊆ Metric.ball (0 : ℂ) 1 ∧ IsConnected V ∧
            Set.InjOn f V ∧ f '' V = Metric.ball w B := by
  refine ⟨1 / 128, by norm_num, fun f hf hf0 => ?_⟩
  -- Setup: f' is differentiable (hence continuous) on the unit disc.
  have hUopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hfd : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ f z :=
    fun z hz => hf.differentiableAt (hUopen.mem_nhds hz)
  have hf' : DifferentiableOn ℂ (deriv f) (Metric.ball (0 : ℂ) 1) := hf.deriv hUopen
  have hf'cont : ContinuousOn (deriv f) (Metric.ball (0 : ℂ) 1) := hf'.continuousOn
  have hfd' : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ (deriv f) z :=
    fun z hz => hf'.differentiableAt (hUopen.mem_nhds hz)
  -- Step 1: maximise phi(z) = (1/2 - |z|) * |f'(z)| on the closed disc of radius 1/2.
  have hKsub : Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have h0K : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall, dist_self]; norm_num
  have hKne : (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)).Nonempty := ⟨0, h0K⟩
  have hKcompact : IsCompact (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
    isCompact_closedBall _ _
  have hφcont : ContinuousOn (fun z : ℂ => ((1 / 2 : ℝ) - ‖z‖) * ‖deriv f z‖)
      (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const.sub continuous_norm.continuousOn
    · exact (hf'cont.mono hKsub).norm
  obtain ⟨a, haK, haMax⟩ := hKcompact.exists_isMaxOn hKne hφcont
  have hφ0 : ((1 / 2 : ℝ) - ‖(0 : ℂ)‖) * ‖deriv f 0‖ = 1 / 2 := by
    rw [hf0]; simp
  have hmax : (1 / 2 : ℝ) ≤ ((1 / 2 : ℝ) - ‖a‖) * ‖deriv f a‖ := by
    have h := (isMaxOn_iff.mp haMax) _ h0K
    rwa [hφ0] at h
  have ha_norm : ‖a‖ ≤ 1 / 2 := by
    have h := haK
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact h
  set t : ℝ := ((1 / 2 : ℝ) - ‖a‖) / 2 with htdef
  set M : ℝ := ‖deriv f a‖ with hMdef
  have hδnn : (0 : ℝ) ≤ (1 / 2 : ℝ) - ‖a‖ := by linarith
  have hMnn0 : (0 : ℝ) ≤ M := by
    rw [hMdef]
    exact norm_nonneg _
  have hδpos : (0 : ℝ) < (1 / 2 : ℝ) - ‖a‖ := by
    by_contra hcon
    have hcon' : (1 / 2 : ℝ) - ‖a‖ ≤ 0 := le_of_not_gt hcon
    have h0 : (1 / 2 : ℝ) - ‖a‖ = 0 := le_antisymm hcon' hδnn
    rw [h0, zero_mul] at hmax
    norm_num at hmax
  have hMpos : 0 < M := by
    by_contra hcon
    have hcon' : M ≤ 0 := le_of_not_gt hcon
    have h0 : M = 0 := le_antisymm hcon' hMnn0
    rw [h0, mul_zero] at hmax
    norm_num at hmax
  have htpos : 0 < t := by
    rw [htdef]
    linarith
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have htne : t ≠ 0 := ne_of_gt htpos
  have htM : (1 / 4 : ℝ) ≤ t * M := by
    have heq : ((1 / 2 : ℝ) - ‖a‖) * M = 2 * (t * M) := by
      rw [htdef]; ring
    linarith
  have halt : ‖a‖ < 1 / 2 := by
    have h := htpos
    rw [htdef] at h
    linarith
  have hane : deriv f a ≠ 0 := by
    intro hcon
    have hM0 : M = 0 := by
      simp only [hMdef, hcon, norm_zero]
    linarith
  -- Step 2: derivative bound |f'(z)| <= 2M on closedBall a t.
  have hKt : ∀ z : ℂ, ‖z - a‖ ≤ t → z ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have htri : ‖z‖ ≤ ‖a‖ + ‖z - a‖ := by
      have h := norm_sub_norm_le z a
      linarith
    linarith
  have hbound : ∀ z ∈ Metric.closedBall a t, ‖deriv f z‖ ≤ 2 * M := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hzK : z ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := hKt z hz
    have hle := (isMaxOn_iff.mp haMax) _ hzK
    rw [← hMdef] at hle
    have hAle : t ≤ (1 / 2 : ℝ) - ‖z‖ := by
      have htri : ‖z‖ ≤ ‖a‖ + ‖z - a‖ := by
        have h := norm_sub_norm_le z a
        linarith
      linarith
    have hx : ((1 / 2 : ℝ) - ‖z‖) * ‖deriv f z‖ ≤ t * (2 * M) := by
      have hpa : ((1 / 2 : ℝ) - ‖a‖) * M = t * (2 * M) := by
        rw [htdef]; ring
      linarith
    have e1 : t * ‖deriv f z‖ ≤ ((1 / 2 : ℝ) - ‖z‖) * ‖deriv f z‖ :=
      mul_le_mul_of_nonneg_right hAle (norm_nonneg _)
    exact le_of_mul_le_mul_left (le_trans e1 hx) htpos
  -- Step 3: Cauchy estimate |f''(z)| <= 4M/t on ball a (t/2).
  have ht2pos : (0 : ℝ) < t / 2 := by linarith
  have ht2ne : t / 2 ≠ 0 := ne_of_gt ht2pos
  have hsub1 : ∀ z ∈ Metric.ball a (t / 2),
      Metric.closedBall z (t / 2) ⊆ Metric.closedBall a t := by
    intro z hz w hw
    rw [Metric.mem_closedBall] at hw ⊢
    have hza : dist z a < t / 2 := Metric.mem_ball.mp hz
    calc dist w a ≤ dist w z + dist z a := dist_triangle _ _ _
      _ ≤ t / 2 + t / 2 := add_le_add hw (le_of_lt hza)
      _ = t := by ring
  have hCauchy : ∀ z ∈ Metric.ball a (t / 2), ‖deriv (deriv f) z‖ ≤ 4 * M / t := by
    intro z hz
    have hdiff : DiffContOnCl ℂ (deriv f) (Metric.ball z (t / 2)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z ht2ne]
      refine hf'.mono (fun w hw => ?_)
      have hw' : ‖w - a‖ ≤ t := by
        have h1 : w ∈ Metric.closedBall a t := hsub1 z hz hw
        rwa [Metric.mem_closedBall, dist_eq_norm] at h1
      exact hKsub (hKt w hw')
    have hsph : ∀ w ∈ Metric.sphere z (t / 2), ‖deriv f w‖ ≤ 2 * M := by
      intro w hw
      exact hbound w (hsub1 z hz (Metric.sphere_subset_closedBall hw))
    have hle := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ht2pos hdiff hsph
    have hEq : (2 : ℝ) * M / (t / 2) = 4 * M / t := by
      field_simp
      ring
    rwa [hEq] at hle
  -- Step 4: f' is nearly constant on S = ball a rho, rho = t/8.
  set ρ : ℝ := t / 8 with hρdef
  set S : Set ℂ := Metric.ball a ρ with hSdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; linarith
  have hSsub : S ⊆ Metric.ball a (t / 2) := by
    rw [hSdef]
    exact Metric.ball_subset_ball (by rw [hρdef]; linarith)
  have hSconv : Convex ℝ S := by
    rw [hSdef]; exact convex_ball _ _
  have hSopen : IsOpen S := by
    rw [hSdef]; exact Metric.isOpen_ball
  have haS : a ∈ S := by
    rw [hSdef, Metric.mem_ball, dist_self]
    exact hρpos
  have hSU : S ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hza : ‖z - a‖ < ρ := by
      have h := hz
      rw [hSdef, Metric.mem_ball, dist_eq_norm] at h
      exact h
    have hzat : ‖z - a‖ ≤ t := by
      have hle : ρ ≤ t := by rw [hρdef]; linarith
      exact le_trans (le_of_lt hza) hle
    exact hKsub (hKt z hzat)
  have h4 : ∀ z ∈ S, ‖deriv f z - deriv f a‖ ≤ M / 2 := by
    intro z hz
    have hdiffS : ∀ x ∈ S, DifferentiableAt ℂ (deriv f) x :=
      fun x hx => hfd' x (hSU hx)
    have hbndS : ∀ x ∈ S, ‖deriv (deriv f) x‖ ≤ 4 * M / t :=
      fun x hx => hCauchy x (hSsub hx)
    have hle := Convex.norm_image_sub_le_of_norm_deriv_le hdiffS hbndS hSconv haS hz
    have hza : ‖z - a‖ ≤ ρ := le_of_lt (by
      have h := hz
      rw [hSdef, Metric.mem_ball, dist_eq_norm] at h
      exact h)
    have e1 : (4 * M / t) * ‖z - a‖ ≤ (4 * M / t) * ρ :=
      mul_le_mul_of_nonneg_left hza (div_nonneg (by linarith) htpos.le)
    have e2 : (4 * M / t) * ρ = M / 2 := by
      rw [hρdef]; field_simp; ring
    exact (le_trans hle e1).trans (le_of_eq e2)
  -- Step 5: f approximates the linear map L(z) = z * f'(a) on S.
  set u : ℂˣ := Units.mk0 (deriv f a) hane with hudef
  set L : ℂ ≃L[ℂ] ℂ := (ContinuousLinearEquiv.unitsEquivAut ℂ) u with hLdef
  have huval : (↑u : ℂ) = deriv f a := Units.val_mk0 hane
  have hLapply : ∀ x : ℂ, L x = x * deriv f a := by
    intro x
    simp only [hLdef, ContinuousLinearEquiv.unitsEquivAut_apply, huval]
  have hLsymm : ∀ y : ℂ, L.symm y = y * (↑u⁻¹ : ℂ) := by
    intro y
    have h : L.symm y * deriv f a = y := by
      have h2 : L (L.symm y) = y := by simp
      rwa [hLapply] at h2
    have hurel : (↑u : ℂ) * (↑u⁻¹ : ℂ) = 1 := Units.mul_inv u
    calc L.symm y = (L.symm y * deriv f a) * (↑u⁻¹ : ℂ) := by
            rw [mul_assoc, ← huval, hurel, mul_one]
      _ = y * (↑u⁻¹ : ℂ) := by rw [h]
  have hMinv : ‖(↑u⁻¹ : ℂ)‖ = M⁻¹ := by
    simp only [Units.val_inv_eq_inv_val, norm_inv, huval, hMdef]
  have hM0le : (0 : ℝ) ≤ M⁻¹ := inv_nonneg.mpr hMnn
  have hop : ‖(↑L.symm : ℂ →L[ℂ] ℂ)‖ ≤ M⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hM0le ?_
    intro y
    rw [ContinuousLinearEquiv.coe_coe, hLsymm y, norm_mul, hMinv, mul_comm]
  set n : NNReal := ‖(↑L.symm : ℂ →L[ℂ] ℂ)‖₊ with hndef
  have hleR0 : (n : ℝ) ≤ M⁻¹ := by
    rw [hndef, coe_nnnorm]
    exact hop
  have hnne : n ≠ 0 := by
    rw [hndef, ne_eq, nnnorm_eq_zero]
    intro hcon
    have h1 : L.symm (L (1 : ℂ)) = (1 : ℂ) := by simp
    have h2 : L.symm (L (1 : ℂ)) = 0 := by
      have hcc := congrArg (fun g : ℂ →L[ℂ] ℂ => g (L (1 : ℂ))) hcon
      simp only [ContinuousLinearEquiv.coe_coe, zero_apply] at hcc
      exact hcc
    rw [h1] at h2
    exact one_ne_zero h2
  set c : NNReal := NNReal.mk (M / 2) (by linarith) with hcdef
  have hcside : c < n⁻¹ := by
    have hnR : (0 : ℝ) < (n : ℝ) :=
      NNReal.coe_lt_coe.mpr (lt_of_le_of_ne zero_le (Ne.symm hnne))
    have hleR : (n : ℝ) ≤ M⁻¹ := hleR0
    have hinvR : M ≤ (n : ℝ)⁻¹ := by
      have h := (inv_le_inv₀ (inv_pos.mpr hMpos) hnR).mpr hleR
      rwa [inv_inv] at h
    rw [← NNReal.coe_lt_coe, NNReal.coe_inv]
    simp only [hcdef, NNReal.coe_mk]
    linarith
  have hderiv_h : ∀ x ∈ S, HasDerivAt (f - ⇑L) (deriv f x - deriv f a) x := by
    intro x hx
    have h1 : HasDerivAt f (deriv f x) x := (hfd x (hSU hx)).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z * deriv f a) (1 * deriv f a) x :=
      (hasDerivAt_id x).mul_const _
    rw [one_mul] at h2
    have hfun : (fun z : ℂ => z * deriv f a) = ⇑L := by
      funext z
      exact (hLapply z).symm
    rw [hfun] at h2
    exact h1.sub h2
  have hderiv_eq : ∀ x ∈ S, deriv (f - ⇑L) x = deriv f x - deriv f a :=
    fun x hx => (hderiv_h x hx).deriv
  have hdiffh : ∀ x ∈ S, DifferentiableAt ℂ (f - ⇑L) x :=
    fun x hx => (hderiv_h x hx).differentiableAt
  have hcR : (c : ℝ) = M / 2 := by
    simp only [hcdef, NNReal.coe_mk]
  have hbndh : ∀ x ∈ S, ‖deriv (f - ⇑L) x‖₊ ≤ c := by
    intro x hx
    rw [hderiv_eq x hx, ← NNReal.coe_le_coe, coe_nnnorm, hcR]
    exact h4 x hx
  have hlip : LipschitzOnWith c (f - ⇑L) S :=
    hSconv.lipschitzOnWith_of_nnnorm_deriv_le hdiffh hbndh
  have happrox : ApproximatesLinearOn f (↑L : ℂ →L[ℂ] ℂ) S c := by
    rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith,
      ContinuousLinearEquiv.coe_coe]
    exact hlip
  -- Step 6: injectivity, image disc of radius >= 1/128, partial homeomorphism.
  have hside : Subsingleton ℂ ∨ c < ‖(↑L.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
    rw [← hndef]
    exact Or.inr hcside
  have hinj : Set.InjOn f S := happrox.injOn hside
  let R : (↑L : ℂ →L[ℂ] ℂ).NonlinearRightInverse :=
    { toFun := fun y => y * (↑u⁻¹ : ℂ),
      nnnorm := NNReal.mk (M⁻¹) (inv_nonneg.mpr hMnn),
      bound' := by
        intro y
        simp only [NNReal.coe_mk]
        rw [norm_mul, hMinv, mul_comm]
      right_inv' := by
        intro y
        change (↑L : ℂ →L[ℂ] ℂ) (y * (↑u⁻¹ : ℂ)) = y
        have hurel : (↑u : ℂ) * (↑u⁻¹ : ℂ) = 1 := Units.mul_inv u
        rw [ContinuousLinearEquiv.coe_coe, hLapply]
        calc (y * (↑u⁻¹ : ℂ)) * deriv f a = y * ((↑u⁻¹ : ℂ) * ↑u) := by
                rw [mul_assoc, ← huval]
          _ = y := by rw [mul_comm (↑u⁻¹ : ℂ) (↑u : ℂ), hurel, mul_one] }
  have hRnn : ((R.nnnorm : NNReal) : ℝ) = M⁻¹ := rfl
  set ε : ℝ := ρ / 2 with hεdef
  have hεnn : (0 : ℝ) ≤ ε := by
    rw [hεdef]; linarith
  have hball_sub : Metric.closedBall a ε ⊆ S := by
    have hερ : ε < ρ := by
      rw [hεdef]; linarith
    rw [hSdef]
    exact Metric.closedBall_subset_ball hερ
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse R hεnn hball_sub
  have hrad : (1 / 128 : ℝ) ≤ ((↑R.nnnorm)⁻¹ - ↑c) * ε := by
    have heq : ((M⁻¹)⁻¹ - M / 2) * ((t / 8) / 2) = (t * M) / 32 := by
      rw [inv_inv]; ring
    rw [hRnn, hcR, hεdef, hρdef, heq]
    linarith
  have himg : Metric.closedBall (f a) (1 / 128) ⊆ f '' S := by
    have hsub : Metric.closedBall (f a) (1 / 128) ⊆
        Metric.closedBall (f a) (((↑R.nnnorm)⁻¹ - ↑c) * ε) :=
      Metric.closedBall_subset_closedBall hrad
    intro y hy
    obtain ⟨x, hx, hfx⟩ := hsurj (hsub hy)
    exact ⟨x, hball_sub hx, hfx⟩
  have hball_img : Metric.ball (f a) (1 / 128) ⊆ f '' S :=
    fun y hy => himg (Metric.ball_subset_closedBall hy)
  set e : OpenPartialHomeomorph ℂ ℂ :=
    ApproximatesLinearOn.toOpenPartialHomeomorph f S happrox hside hSopen with hedef
  have he_coe : ⇑e = f :=
    ApproximatesLinearOn.toOpenPartialHomeomorph_coe f S happrox hside hSopen
  have he_src : e.source = S :=
    ApproximatesLinearOn.toOpenPartialHomeomorph_source f S happrox hside hSopen
  have he_tgt : e.target = f '' S :=
    ApproximatesLinearOn.toOpenPartialHomeomorph_target f S happrox hside hSopen
  -- Step 7: V is the preimage of the disc under the partial homeomorphism.
  have hBpos : (0 : ℝ) < 1 / 128 := by norm_num
  have hbt : Metric.ball (f a) (1 / 128) ⊆ e.target := by
    rw [he_tgt]
    exact hball_img
  have hVeq : e.symm '' Metric.ball (f a) (1 / 128)
      = e.source ∩ f ⁻¹' Metric.ball (f a) (1 / 128) := by
    rw [e.symm_image_eq_source_inter_preimage hbt, he_coe]
  have hVS : e.symm '' Metric.ball (f a) (1 / 128) ⊆ S := by
    rw [hVeq, he_src]
    exact Set.inter_subset_left
  have hVopen : IsOpen (e.symm '' Metric.ball (f a) (1 / 128)) :=
    e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hbt
  have hconn : IsConnected (e.symm '' Metric.ball (f a) (1 / 128)) :=
    (Metric.isConnected_ball hBpos).image _ (e.continuousOn_symm.mono hbt)
  have hinjV : Set.InjOn f (e.symm '' Metric.ball (f a) (1 / 128)) :=
    Set.InjOn.mono hVS hinj
  have himgV : f '' (e.symm '' Metric.ball (f a) (1 / 128))
      = Metric.ball (f a) (1 / 128) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, hxV, hfx⟩ := hy
      have hx2 : x ∈ e.source ∩ f ⁻¹' Metric.ball (f a) (1 / 128) := by
        rw [← hVeq]
        exact hxV
      have hxpre : f x ∈ Metric.ball (f a) (1 / 128) := hx2.2
      rw [← hfx]
      exact hxpre
    · intro z hz
      refine ⟨e.symm z, ⟨z, hz, rfl⟩, ?_⟩
      have h1 : ⇑e (⇑e.symm z) = z := e.right_inv (hbt hz)
      have h2 : f (⇑e.symm z) = z := by
        rw [← he_coe]
        exact h1
      exact h2
  exact ⟨e.symm '' Metric.ball (f a) (1 / 128), f a, hVopen,
    (fun z hz => hSU (hVS hz)), hconn, hinjV, himgV⟩

end MathlibExt.Analysis.Complex.BlochWanted
