/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_72.lean` (openbmb/ma-proofbench, commit 31bab4c):
Copyright (c) 2026 OpenBMB. Licensed under the MIT License.
Authors: L. Pu et al. (MA-ProofBench).
The coordinate definitions and the theorem statement are adapted from this source.
The statement includes the additional hypothesis that the extension is bounded.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.InnerProductSpace.InvNormHarmonic
import MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

/-!
# Decay of bounded harmonic extensions in the lower half-space

A bounded harmonic extension of Schwartz boundary data in three dimensions decays uniformly
with depth. The proof compares both signs of the extension with a multiple of the reciprocal
distance to a pole one unit above the boundary.
-/

@[expose] public section

namespace MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimateWanted

/-- **The Euclidean plane.** The Euclidean plane $\mathbb{R}^2$ is the space of pairs of real
numbers with the Euclidean inner product and norm. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)
/-- **Euclidean three-space.** Euclidean three-space $\mathbb{R}^3$ is the space of triples of
real numbers with the Euclidean inner product and norm. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **Closed lower half-space.** The closed lower half-space is the set of points
$(p_1, p_2, p_3)$ of Euclidean three-space $\mathbb{R}^3$ with $p_3 \le 0$. -/
abbrev LowerHalfSpace : Set R3 := {p : R3 | p 2 ≤ 0}
/-- **Open lower half-space.** The open lower half-space is the set of points $(p_1, p_2, p_3)$
of Euclidean three-space $\mathbb{R}^3$ with $p_3 < 0$. -/
abbrev OpenLowerHalfSpace : Set R3 := {p : R3 | p 2 < 0}

/-- **Appending a third coordinate.** For a point $x = (x_1, x_2)$ of the Euclidean plane
$\mathbb{R}^2$ and a real number $z$, this is the point $(x_1, x_2, z)$ of Euclidean three-space
$\mathbb{R}^3$. -/
noncomputable def point3 (x : R2) (z : ℝ) : R3 :=
  EuclideanSpace.single (0 : Fin 3) (x 0) +
    EuclideanSpace.single (1 : Fin 3) (x 1) +
      EuclideanSpace.single (2 : Fin 3) z

open InnerProductSpace Laplacian Set Topology Metric
open MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

private noncomputable def pole (r : ℝ) : R3 := EuclideanSpace.single (2 : Fin 3) r

private noncomputable def kernel (r : ℝ) (p : R3) : ℝ := ‖p - pole r‖⁻¹

private theorem depth_le_norm_sub (r : ℝ) (p : R3) : r - p 2 ≤ ‖p - pole r‖ := by
  have h := PiLp.norm_apply_le (p - pole r) (2 : Fin 3)
  exact (le_abs_self (r - p 2)).trans (by simpa [pole, Real.norm_eq_abs, abs_sub_comm] using h)

private theorem kernel_harmonic {r : ℝ} (hr : 0 < r) {p : R3} (hp : p ∈ LowerHalfSpace) :
    HarmonicAt (kernel r) p := by
  have hpos : 0 < ‖p - pole r‖ := lt_of_lt_of_le (sub_pos.mpr (lt_of_le_of_lt hp hr))
    (depth_le_norm_sub r p)
  have hdiff : ContDiffAt ℝ 2 (fun q : R3 => q - pole r) p := by fun_prop
  refine ⟨(hdiff.norm ℝ (norm_pos_iff.mp hpos)).inv hpos.ne', ?_⟩
  have hne : ∀ᶠ q in 𝓝 p, q - pole r ≠ 0 :=
    (isOpen_ne.preimage (continuous_id.sub continuous_const)).mem_nhds (norm_pos_iff.mp hpos)
  filter_upwards [hne] with q hq
  change Δ (fun y : R3 => ‖y - pole r‖⁻¹) q = 0
  rw [← MathlibExt.Analysis.laplacian_inv_norm_eq_zero hq]
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_sub (f := fun y : R3 => ‖y‖⁻¹)]

-- Truncate the half-space by the ball of radius 2R centered at height R. The harmonic
-- correction 2M (1 - R / ‖p - pole R‖) dominates M on the sphere and tends to zero at p.
private theorem nonpos_of_boundary_nonpos {w : R3 → ℝ}
    (hw : HarmonicOnNhd w OpenLowerHalfSpace) (hc : ContinuousOn w LowerHalfSpace)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p ∈ LowerHalfSpace, w p ≤ M)
    (hplane : ∀ p : R3, p 2 = 0 → w p ≤ 0) (p : R3) (hp : p ∈ LowerHalfSpace) :
    w p ≤ 0 := by
  by_cases hp0 : p 2 = 0
  · exact hplane p hp0
  have hpneg : p 2 < 0 := lt_of_le_of_ne hp hp0
  by_contra! hpos
  obtain ⟨R, hR⟩ := exists_gt (max ‖p‖ (2 * M * ‖p‖ / w p))
  have hpR := (le_max_left _ _).trans_lt hR
  have hRpos := (norm_nonneg p).trans_lt hpR
  have hgap := (div_lt_iff₀ hpos).mp ((le_max_right _ _).trans_lt hR)
  have hnorm : ‖p - pole R‖ ≤ ‖p‖ + R := by
    simpa [pole, Real.norm_eq_abs, abs_of_pos hRpos] using norm_sub_le p (pole R)
  let U := ball (pole R) (2 * R) ∩ OpenLowerHalfSpace
  have hzcont : Continuous (fun y : R3 => y 2) := PiLp.continuous_apply _ _ _
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt hzcont continuous_const)
  have hpU : p ∈ U := ⟨by rw [mem_ball, dist_eq_norm]; linarith, hpneg⟩
  have hcl : closure U ⊆ LowerHalfSpace :=
    closure_minimal (fun y (hy : y ∈ U) => (show y 2 < 0 from hy.2).le)
      (isClosed_le hzcont continuous_const)
  let v : R3 → ℝ := w + (2 * M * R) • kernel R
  have hk (y : R3) (hy : y ∈ LowerHalfSpace) := kernel_harmonic hRpos hy
  have hvc : ContinuousOn v (closure U) := (hc.mono hcl).add
    (continuousOn_const.smul fun y hy => (hk y (hcl hy)).1.continuousAt.continuousWithinAt)
  have hvh : HarmonicOnNhd v U := fun y hy =>
    (hw y hy.2).add ((hk y (show y 2 < 0 from hy.2).le).const_smul (c := 2 * M * R))
  obtain ⟨y, hy, hmax⟩ := exists_mem_frontier_isMaxOn_of_harmonicOnNhd hU
    (isBounded_ball.subset inter_subset_left) ⟨p, hpU⟩ hvc hvh
  have hycl := hcl (frontier_subset_closure hy)
  have hd (q : R3) (hq : q ∈ LowerHalfSpace) : R ≤ ‖q - pole R‖ :=
    (le_sub_iff_add_le.mpr (add_le_of_nonpos_right hq)).trans (depth_le_norm_sub R q)
  have hvy : v y ≤ 2 * M := by
    change w y + 2 * M * R * ‖y - pole R‖⁻¹ ≤ 2 * M
    rw [← div_eq_mul_inv, ← le_sub_iff_add_le', div_le_iff₀ (hRpos.trans_le (hd y hycl))]
    by_cases hy0 : y 2 = 0
    · have h := hplane y hy0
      nlinarith [mul_le_mul_of_nonneg_left (hd y hycl) (show 0 ≤ 2 * M by positivity),
        mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg (y - pole R))]
    · have hys : 2 * R ≤ ‖y - pole R‖ := by
        by_contra! hlt
        have : y ∈ U := ⟨by rwa [mem_ball, dist_eq_norm], lt_of_le_of_ne hycl hy0⟩
        exact hy.2 (hU.interior_eq.symm ▸ this)
      nlinarith [mul_le_mul_of_nonneg_left hys hM,
        mul_le_mul_of_nonneg_right (hb y hycl) (norm_nonneg (y - pole R))]
  have hcomp : v p ≤ 2 * M := (hmax (subset_closure hpU)).trans hvy
  change w p + 2 * M * R * ‖p - pole R‖⁻¹ ≤ 2 * M at hcomp
  rw [← div_eq_mul_inv, ← le_sub_iff_add_le', div_le_iff₀ (hRpos.trans_le (hd p hp))] at hcomp
  nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * M by positivity),
    mul_le_mul_of_nonneg_left (hd p hp) hpos.le]

private theorem point3_height (x : R2) (z : ℝ) : point3 x z 2 = z := by
  simp [point3]

private theorem exists_point3_of_height_zero {p : R3} (hp : p 2 = 0) :
    ∃ x : R2, point3 x 0 = p := by
  refine ⟨WithLp.toLp 2 ![p 0, p 1], ?_⟩
  ext i
  fin_cases i <;> simp [point3, hp]

private theorem boundary_distance_le (x : R2) : ‖point3 x 0 - pole 1‖ ≤ 2 * ‖x‖ + 1 := by
  have hz : EuclideanSpace.single (2 : Fin 3) (0 : ℝ) = 0 :=
    (PiLp.single_eq_zero_iff 2 (2 : Fin 3)).mpr rfl
  have h : ‖point3 x 0‖ ≤ ‖x 0‖ + ‖x 1‖ := by
    simpa [point3, hz] using
      norm_add_le (EuclideanSpace.single (0 : Fin 3) (x 0))
        (EuclideanSpace.single (1 : Fin 3) (x 1))
  have := norm_sub_le (point3 x 0) (pole 1)
  rw [show ‖pole 1‖ = 1 by simp [pole]] at this
  linarith [PiLp.norm_apply_le x (0 : Fin 2), PiLp.norm_apply_le x (1 : Fin 2)]

-- The zeroth and first Schwartz seminorms control the trace times its distance to the pole.
private theorem exists_boundary_majorant (φ : SchwartzMap R2 ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |φ x| ≤ C * kernel 1 (point3 x 0) := by
  let C := SchwartzMap.seminorm ℝ 0 0 φ + 2 * SchwartzMap.seminorm ℝ 1 0 φ + 1
  refine ⟨C, by dsimp [C]; positivity, fun x => ?_⟩
  have hd := depth_le_norm_sub 1 (point3 x 0)
  rw [point3_height, sub_zero] at hd
  change |φ x| ≤ C * ‖point3 x 0 - pole 1‖⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (zero_lt_one.trans_le hd)]
  have h₀ := φ.norm_le_seminorm ℝ x
  have h₁ := φ.norm_pow_mul_le_seminorm ℝ 1 x
  simp only [pow_one, Real.norm_eq_abs] at h₀ h₁
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left (boundary_distance_le x) (abs_nonneg (φ x))]

-- Boundedness already suffices for comparison, so the stated decay hypothesis is redundant.
set_option linter.unusedVariables false in
/-- **Decay of bounded harmonic extensions of Schwartz data in a half-space.** Write a point of
$\mathbb{R}^3$ as $(x, z)$ with $x = (x_1, x_2) \in \mathbb{R}^2$ and $z \in \mathbb{R}$. Let
$\phi : \mathbb{R}^2 \to \mathbb{R}$ be a Schwartz function and let
$u : \mathbb{R}^3 \to \mathbb{R}$ be harmonic at every point of the open lower half-space
$\{(x, z) : z < 0\}$, continuous on the closed lower half-space $\{(x, z) : z \le 0\}$ and bounded
there, with $u(x, 0) = \phi(x)$ for every $x \in \mathbb{R}^2$. Suppose that $u(x, z) \to 0$ as
$z \to -\infty$ uniformly in $x$: for every $\varepsilon > 0$ there is $z_0$ such that
$|u(x, z)| < \varepsilon$ for all $z \le z_0$ and all $x \in \mathbb{R}^2$. Then there is a
constant $C > 0$ such that $|u(x, z)| \le C (1 + |z|)^{-1}$ for all $z \le 0$ and all
$x \in \mathbb{R}^2$.

Boundedness of $u$ is not among the hypotheses of the source problem, but the bound fails without
it: adding to the Poisson extension of $\phi$ the harmonic function $\operatorname{Im} G(x_1 + iz)$
built from Newman's entire function $G$, which vanishes on $z = 0$ and as $z \to -\infty$ but is
unbounded near the boundary, gives a counterexample.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_72.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem exists_abs_le_inv_one_add_abs_of_harmonic_lowerHalfSpace
  (φ : SchwartzMap R2 ℝ)
  (u : R3 → ℝ)
  (hu_harmonic : InnerProductSpace.HarmonicOnNhd u OpenLowerHalfSpace)
  (hu_cont : ContinuousOn u LowerHalfSpace)
  (hu_bdd : ∃ M : ℝ, ∀ p ∈ LowerHalfSpace, |u p| ≤ M)
  (hu_boundary : ∀ x : R2, u (point3 x 0) = φ x)
  (hu_decay :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z : ℝ in Filter.atBot, ∀ x : R2, |u (point3 x z)| < ε) :
  ∃ C : ℝ, 0 < C ∧
    ∀ z : ℝ, z ≤ 0 →
      ∀ x : R2, |u (point3 x z)| ≤ C * (1 + |z|)⁻¹ := by
  obtain ⟨C, hC, htrace⟩ := exists_boundary_majorant φ
  obtain ⟨M, hM⟩ := hu_bdd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by simp [LowerHalfSpace]))
  let B : R3 → ℝ := C • kernel 1
  have hB (p : R3) (hp : p ∈ LowerHalfSpace) : HarmonicAt B p :=
    (kernel_harmonic zero_lt_one hp).const_smul
  have hB0 (p : R3) : 0 ≤ B p := mul_nonneg hC.le (inv_nonneg.mpr (norm_nonneg _))
  have hplane (p : R3) (hp : p 2 = 0) : |u p| ≤ B p := by
    obtain ⟨x, rfl⟩ := exists_point3_of_height_zero hp
    rw [hu_boundary]
    exact htrace x
  have compare {f : R3 → ℝ} (hf : HarmonicOnNhd f OpenLowerHalfSpace)
      (hc : ContinuousOn f LowerHalfSpace) (hle : ∀ p, f p ≤ |u p|) (p : R3)
      (hp : p ∈ LowerHalfSpace) : f p ≤ B p := by
    apply sub_nonpos.mp
    apply nonpos_of_boundary_nonpos (w := f - B) _ _ hM0 _ _ p hp
    · exact fun y hy => (hf y hy).sub (hB y (show y 2 < 0 from hy).le)
    · exact hc.sub fun y hy => (hB y hy).1.continuousAt.continuousWithinAt
    · exact fun y hy => (sub_le_self _ (hB0 y)).trans ((hle y).trans (hM y hy))
    · exact fun y hy => sub_nonpos.mpr ((hle y).trans (hplane y hy))
  refine ⟨C, hC, fun z hz x => ?_⟩
  let p := point3 x z
  have hp : p ∈ LowerHalfSpace := (point3_height x z).trans_le hz
  have habs : |u p| ≤ B p := abs_le.mpr
    ⟨neg_le.mp (compare hu_harmonic.neg hu_cont.neg (fun y => neg_le_abs _) p hp),
      compare hu_harmonic hu_cont (fun y => le_abs_self _) p hp⟩
  have hd := depth_le_norm_sub 1 p
  rw [show p 2 = z from point3_height x z, sub_eq_add_neg, ← abs_of_nonpos hz] at hd
  exact habs.trans (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hd) hC.le)

end MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimateWanted
