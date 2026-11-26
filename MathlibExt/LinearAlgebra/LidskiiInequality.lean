/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/LinearAlgebra/LidskiiInequality.lean` (leanprover/lean-eval), commit
38361be884302c7edce1908c4aef8296eb2cb27e, manifest
`manifests/problems/lidskii_inequality.toml` (revision 1, submitted by Kim Morrison, archived).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use the adapted
portions except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the
License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the License for the specific language governing permissions
and limitations under the License. lean-eval ships no `NOTICE` file.

The adapted portions are the statement of `lidskii_inequality` and three parts of the module
documentation, unchanged from the former wanted module
`WantedExt/LinearAlgebra/LidskiiInequalityWanted.lean`: the title, the paragraph citing §99
of Knill's *Some Fundamental Theorems in Mathematics*, and the informal statement with its
displayed inequality.

Modification notice (Apache License 2.0, Section 4). ATLAS placed the statement in the
`MathlibExt.LinearAlgebra.LidskiiInequalityWanted` namespace as a wanted declaration and
subsequently moved it here with a proof. ATLAS dropped the last paragraph of the source's
module documentation, which described what mathlib and other proof assistants lacked.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import MathlibExt.Analysis.InnerProductSpace.CourantFischer
import MathlibExt.Analysis.InnerProductSpace.PeierlsKlein

/-!
# Lidskii's inequality

`lidskii_inequality` bounds the ℓᵖ displacement of the ordered eigenvalues of two
Hermitian matrices by the ℓᵖ norm of the spectrum of their difference.

§99 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (an
additional statement of the section on spectral perturbation; the boxed
main theorem `lidskii_last` follows as the `p = 1` case combined with an
entrywise bound).

For two self-adjoint complex `n × n` matrices `A, B` with eigenvalues
sorted in the same order, the `ℓ^p` displacement of the eigenvalues is
bounded by the `ℓ^p` norm of the eigenvalues of `C := B − A`, for every
real `p ≥ 1`:

  `∑ⱼ |αⱼ − βⱼ|^p ≤ ∑ⱼ |γⱼ|^p`.
-/

namespace MathlibExt.LinearAlgebra.LidskiiInequalityWanted.LinearAlgebra

open Filter Matrix Set WithLp
open scoped ENNReal InnerProductSpace Topology

open MathlibExt.Analysis.InnerProductSpace.CourantFischer

section Operators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {n : ℕ}

/-- Comparing the Rayleigh quotients in the Courant–Fischer principle gives the
operator norm bound in one direction. -/
private theorem eigenvalues_sub_le_norm (hn : Module.finrank ℂ E = n)
    {S T : E →L[ℂ] E} (hS : S.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric)
    (i : Fin n) :
    hS.eigenvalues hn i - hT.eigenvalues hn i ≤ ‖S - T‖ := by
  obtain ⟨W, hW, htail, _⟩ := exists_tail_submodule hT hn i.isLt
  obtain ⟨x, hxW, hx, hhead⟩ := exists_unit_ge_of_submodule hS hn i.isLt W hW
  refine (sub_le_sub hhead (htail x hxW hx)).trans ?_
  change (⟪S x, x⟫_ℂ).re - (⟪T x, x⟫_ℂ).re ≤ _
  rw [← Complex.sub_re, ← inner_sub_left]
  calc
    _ ≤ ‖S x - T x‖ * ‖x‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖S - T‖ := by
      change ‖(S - T) x‖ * ‖x‖ ≤ _
      simpa only [hx, mul_one] using (S - T).le_opNorm x

private theorem continuous_eigenvalues (hn : Module.finrank ℂ E = n)
    {M : ℝ → E →L[ℂ] E} (hM : ∀ t, (M t).toLinearMap.IsSymmetric)
    (hMcont : Continuous M) (i : Fin n) :
    Continuous (fun t => (hM t).eigenvalues hn i) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  apply tendsto_iff_dist_tendsto_zero.2
  refine squeeze_zero (fun _ => dist_nonneg) (g := fun r => ‖M r - M s‖) (fun r => ?_) ?_
  · rw [Real.dist_eq, abs_le]
    constructor
    · have h := eigenvalues_sub_le_norm hn (hM s) (hM r) i
      rw [norm_sub_rev] at h
      linarith
    · exact eigenvalues_sub_le_norm hn (hM r) (hM s) i
  · simpa using ((hMcont.sub (continuous_const (y := M s))).norm.continuousAt (x := s)).tendsto

/-- Along a sequence approaching a point from the right, the eigenbases have a convergent
subsequence. The ordered eigenvalue slopes on that subsequence converge to the diagonal of the
perturbation in the limiting basis. -/
private theorem exists_tendsto_eigenvalue_slopes (hn : Module.finrank ℂ E = n)
    (A C : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric)
    (t : ℝ) :
    let M (s : ℝ) := A + (s : ℂ) • C
    let hM (s : ℝ) : (M s).toLinearMap.IsSymmetric :=
      hA.add (hC.smul (Complex.conj_ofReal s))
    ∃ (u : ℕ → ℝ) (b : OrthonormalBasis (Fin n) ℂ E),
      Tendsto u atTop (𝓝[>] t) ∧
      ∀ i, Tendsto (slope (fun s => (hM s).eigenvalues hn i) t ∘ u) atTop
        (𝓝 (⟪b i, C (b i)⟫_ℂ).re) := by
  intro M hM
  let μ (s : ℝ) := (hM s).eigenvalues hn
  let e (s : ℝ) := (hM s).eigenvectorBasis hn
  have hMcont : Continuous M := by dsimp [M]; fun_prop
  have hμ := continuous_eigenvalues hn hM hMcont
  let v (m : ℕ) := t + 1 / ((m : ℝ) + 1)
  have hv_gt (m : ℕ) : t < v m := by dsimp [v]; exact lt_add_of_pos_right _ (by positivity)
  have hv : Tendsto v atTop (𝓝[>] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hv_gt⟩
    simpa [v] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add t
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hcompact : IsCompact (Set.pi univ (fun _ : Fin n => Metric.sphere (0 : E) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_sphere _ _)
  obtain ⟨w, _, σ, hσ, hw⟩ := hcompact.tendsto_subseq (x := fun m i => e (v m) i)
    (fun m i _ => by simp)
  let u := v ∘ σ
  have hu_gt (m : ℕ) : t < u m := hv_gt (σ m)
  have hu : Tendsto u atTop (𝓝[>] t) := hv.comp hσ.tendsto_atTop
  have hu' : Tendsto u atTop (𝓝 t) := hu.mono_right nhdsWithin_le_nhds
  have he (i : Fin n) : Tendsto (fun m => e (u m) i) atTop (𝓝 (w i)) :=
    tendsto_pi_nhds.1 hw i
  have horth : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    apply tendsto_nhds_unique ((he i).inner (he j))
    refine tendsto_const_nhds.congr fun m => ?_
    exact (orthonormal_iff_ite.mp (e (u m)).orthonormal i j).symm
  let b := OrthonormalBasis.mk horth
    (horth.linearIndependent.span_eq_top_of_card_eq_finrank' (by simpa using hn.symm)).ge
  have hb : ⇑b = w := OrthonormalBasis.coe_mk ..
  have heig (s : ℝ) (i : Fin n) : M s (e s i) = (μ s i : ℂ) • e s i :=
    (hM s).apply_eigenvectorBasis hn i
  have hweigen (i : Fin n) : M t (w i) = (μ t i : ℂ) • w i := by
    have hL : Tendsto (fun m => M (u m) (e (u m) i)) atTop (𝓝 (M t (w i))) :=
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
        ((hMcont.continuousAt.tendsto.comp hu').prodMk_nhds (he i))
    have hR : Tendsto (fun m => (μ (u m) i : ℂ) • e (u m) i) atTop
        (𝓝 ((μ t i : ℂ) • w i)) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((hμ i).continuousAt.tendsto.comp hu')).smul (he i)
    exact tendsto_nhds_unique hL (hR.congr fun m => (heig (u m) i).symm)
  refine ⟨u, b, hu, fun i => ?_⟩
  rw [show b i = w i from congrFun hb i]
  have hd : Tendsto (fun m => (⟪w i, e (u m) i⟫_ℂ).re) atTop (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := w i)).inner (he i))
    simpa [Function.comp_def, horth.norm_eq_one i] using h
  have hc : Tendsto (fun m => (⟪w i, C (e (u m) i)⟫_ℂ).re) atTop
      (𝓝 (⟪w i, C (w i)⟫_ℂ).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner (C.continuous.continuousAt.tendsto.comp (he i)))
  have hq := hc.div hd one_ne_zero
  rw [div_one] at hq
  apply hq.congr'
  filter_upwards [hd.eventually_ne one_ne_zero] with m hm
  have hdiff : M (u m) (e (u m) i) - M t (e (u m) i) =
      ((u m - t : ℝ) : ℂ) • C (e (u m) i) := by
    simp only [M, add_apply, smul_apply,
      Complex.ofReal_sub, sub_smul]
    abel
  have heq : ((μ (u m) i - μ t i : ℝ) : ℂ) * ⟪w i, e (u m) i⟫_ℂ =
      ((u m - t : ℝ) : ℂ) * ⟪w i, C (e (u m) i)⟫_ℂ := by
    have hsym : ⟪w i, M t (e (u m) i)⟫_ℂ = ⟪M t (w i), e (u m) i⟫_ℂ :=
      ((hM t) (w i) (e (u m) i)).symm
    calc
      _ = ⟪w i, M (u m) (e (u m) i) - M t (e (u m) i)⟫_ℂ := by
        rw [inner_sub_right, heig, inner_smul_right, hsym, hweigen, inner_smul_left,
          Complex.conj_ofReal, Complex.ofReal_sub, sub_mul]
      _ = _ := by rw [hdiff, inner_smul_right]
  have hr := congrArg Complex.re heq
  simp only [Complex.re_ofReal_mul] at hr
  change (⟪w i, C (e (u m) i)⟫_ℂ).re / (⟪w i, e (u m) i⟫_ℂ).re =
    slope (fun s => μ s i) t (u m)
  rw [slope_def_field, div_eq_div_iff hm (sub_ne_zero.mpr (hu_gt m).ne')]
  linarith

private theorem sum_rpow_diagonal_le (hn : Module.finrank ℂ E = n) (C : E →L[ℂ] E)
    (hC : C.toLinearMap.IsSymmetric) (b : OrthonormalBasis (Fin n) ℂ E)
    {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, |(⟪b i, C (b i)⟫_ℂ).re| ^ p ≤ ∑ j, |hC.eigenvalues hn j| ^ p := by
  have hnorm : ConvexOn ℝ univ (norm : ℝ → ℝ) := convexOn_univ_norm
  have hsubset : norm '' (univ : Set ℝ) ⊆ Ici 0 := by
    rintro _ ⟨x, _, rfl⟩
    exact norm_nonneg x
  have hrange : norm '' (univ : Set ℝ) = Ici 0 :=
    hsubset.antisymm (fun x hx => ⟨x, mem_univ _, Real.norm_of_nonneg hx⟩)
  have hf : ConvexOn ℝ univ (fun x : ℝ => |x| ^ p) := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      ((convexOn_rpow hp).subset hsubset (hrange ▸ convex_Ici (0 : ℝ))).comp hnorm
        (fun _ hx _ _ hxy => Real.rpow_le_rpow (hsubset hx) hxy (by positivity))
  exact MathlibExt.Analysis.InnerProductSpace.PeierlsKlein.peierls_inequality
    hn hC hf (fun _ => mem_univ _) b

private theorem affine_eigenvalues_rpow_le (hn : Module.finrank ℂ E = n)
    (A C : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric)
    {p : ℝ} (hp : 1 ≤ p) :
    let hB : (A + C).toLinearMap.IsSymmetric := hA.add hC
    ∑ i, |hA.eigenvalues hn i - hB.eigenvalues hn i| ^ p ≤
      ∑ j, |hC.eigenvalues hn j| ^ p := by
  intro hB
  let M (t : ℝ) := A + (t : ℂ) • C
  let hM (t : ℝ) : (M t).toLinearMap.IsSymmetric := hA.add (hC.smul (Complex.conj_ofReal t))
  let μ (t : ℝ) := (hM t).eigenvalues hn
  let q := ENNReal.ofReal p
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq : q.toReal = p := ENNReal.toReal_ofReal hp'.le
  let : Fact (1 ≤ q) := ⟨by simpa [q] using ENNReal.ofReal_le_ofReal hp⟩
  have hnorm (v : Fin n → ℝ) : ‖toLp q v‖ = (∑ i, |v i| ^ p) ^ (1 / p) := by
    rw [PiLp.norm_eq_sum (by rwa [hq]), hq]
    rfl
  let K := ‖toLp q (hC.eigenvalues hn)‖
  let F (t : ℝ) := toLp q (μ t - μ 0)
  have hMcont : Continuous M := by dsimp [M]; fun_prop
  have hμ := continuous_eigenvalues hn hM hMcont
  have hF : Continuous F :=
    (PiLp.continuous_toLp q (fun _ : Fin n => ℝ)).comp
      ((continuous_pi hμ).sub continuous_const)
  have hbound : ∀ ⦃t⦄, t ∈ Icc (0 : ℝ) 1 → ‖F t‖ ≤ K * t := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hF.norm.continuousOn
      (B' := fun _ => K)
    · simp [F]
    · exact (continuous_const.mul continuous_id).continuousOn
    · intro t _
      exact ((hasDerivAt_id t).const_mul K).hasDerivWithinAt.congr_deriv (mul_one K)
    · intro t _ r hr
      obtain ⟨u, b, hu, hs⟩ := exists_tendsto_eigenvalue_slopes hn A C hA hC t
      let d (i : Fin n) := (⟪b i, C (b i)⟫_ℂ).re
      have hd : ‖toLp q d‖ ≤ K := by
        rw [hnorm, show K = ‖toLp q (hC.eigenvalues hn)‖ from rfl, hnorm]
        exact Real.rpow_le_rpow (by positivity) (sum_rpow_diagonal_le hn C hC b hp)
          (by positivity)
      have htend : Tendsto (fun m => toLp q (fun i => slope (fun s => μ s i) t (u m)))
          atTop (𝓝 (toLp q d)) :=
        (PiLp.continuous_toLp q (fun _ : Fin n => ℝ)).continuousAt.tendsto.comp
          (tendsto_pi_nhds.2 hs)
      have hsmall := htend.norm.eventually (gt_mem_nhds (hd.trans_lt hr))
      have hu_gt := (tendsto_nhdsWithin_iff.1 hu).2
      apply hu.frequently
      apply Eventually.frequently
      filter_upwards [hsmall, hu_gt] with m hm htm
      have hpos : 0 < u m - t := sub_pos.mpr htm
      have he : toLp q (fun i => slope (fun s => μ s i) t (u m)) =
          (u m - t)⁻¹ • (F (u m) - F t) := by
        ext i
        simp [F, slope_def_field, div_eq_inv_mul]
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
        ← div_eq_inv_mul] at hm
      rw [slope_def_field]
      exact (div_le_div_of_nonneg_right (norm_sub_norm_le _ _) hpos.le).trans_lt hm
  have h1 := hbound (right_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  rw [mul_one] at h1
  have hpow := Real.rpow_le_rpow (norm_nonneg _) h1 hp'.le
  rw [show F 1 = toLp q (μ 1 - μ 0) from rfl, hnorm,
    show K = ‖toLp q (hC.eigenvalues hn)‖ from rfl, hnorm,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hp'.ne', Real.rpow_one, Real.rpow_one] at hpow
  have hμ₀ : μ 0 = hA.eigenvalues hn := by
    unfold μ
    congr 1
    simp [M]
  have hμ₁ : μ 1 = hB.eigenvalues hn := by
    unfold μ
    congr 1
    simp [M]
  rw [hμ₀, hμ₁] at hpow
  simpa only [Pi.sub_apply, abs_sub_comm] using hpow

end Operators

set_option linter.dupNamespace false in
/-- **Lidskii's inequality.** Let $A$ and $B$ be Hermitian complex square matrices indexed by a
finite set with $N$ elements. List the eigenvalues of $A$, of $B$ and of $B - A$, each with
multiplicity and in decreasing order, as $\alpha_1 \ge \dots \ge \alpha_N$,
$\beta_1 \ge \dots \ge \beta_N$ and $\gamma_1 \ge \dots \ge \gamma_N$. Then for every real
$p \ge 1$,
$$\sum_{j=1}^N |\alpha_j - \beta_j|^p \le \sum_{j=1}^N |\gamma_j|^p.$$

Source: V. B. Lidskii, On the proper values of a sum and product of symmetric matrices, Dokl. Akad.
Nauk SSSR 75 (1950), 769-772. Listed as an additional statement of §99 in O. Knill, Some Fundamental
Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `lidskii_inequality`. -/
public theorem lidskii_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {p : ℝ} (_hp : 1 ≤ p) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ^ p ≤
      ∑ j, |(hB.sub hA).eigenvalues₀ j| ^ p := by
  let A' := A.toEuclideanLin.toContinuousLinearMap
  let C' := (B - A).toEuclideanLin.toContinuousLinearMap
  have hA' : A'.toLinearMap.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have hC' : C'.toLinearMap.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr (hB.sub hA)
  have hB' : (A' + C').toLinearMap = B.toEuclideanLin := by
    change A.toEuclideanLin + (B - A).toEuclideanLin = _
    rw [map_sub]
    abel
  have h := affine_eigenvalues_rpow_le finrank_euclideanSpace A' C' hA' hC' _hp
  change (∑ j, |hA.eigenvalues₀ j -
    (hA'.add hC').eigenvalues finrank_euclideanSpace j| ^ p) ≤
      ∑ j, |(hB.sub hA).eigenvalues₀ j| ^ p at h
  have he : (hA'.add hC').eigenvalues finrank_euclideanSpace = hB.eigenvalues₀ := by
    unfold Matrix.IsHermitian.eigenvalues₀
    congr
  rw [he] at h
  exact h

end MathlibExt.LinearAlgebra.LidskiiInequalityWanted.LinearAlgebra
