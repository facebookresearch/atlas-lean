/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# |x|^(2-m) is harmonic away from the origin in R^m

The following OpenBMB notice applies to the adapted Newtonian-kernel statement and its
documentation.

Copyright (c) 2026 OpenBMB

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

Attribution and modification notice: the Newtonian-kernel statement is adapted from
openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_81.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_81 … := by sorry` into the Batteries `theorem_wanted`
`harmonicOnNhd_one_div_norm_pow_sub_two`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.NormPowTwoSubDimHarmonicWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This change supplies a proof using the generalized three-dimensional calculation.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Newtonian kernel is harmonic away from the origin

For `m > 2`, the Newtonian kernel `x ↦ 1 / ‖x‖ ^ (m - 2)` on `EuclideanSpace ℝ (Fin m)` is
twice continuously differentiable with vanishing flat Laplacian `Δ` near every nonzero point:
it is harmonic on `{0}ᶜ`.

## i. Overview

Write the kernel as `(‖y‖ ^ 2) ^ r` with `r = -(m - 2) / 2`, that is as `g ∘ h` with
`g s = s ^ r` and `h y = ‖y‖ ^ 2`. Expanding `Δ` over the standard orthonormal basis and
computing each second directional derivative by Faà di Bruno along the line `t ↦ x + t • v`
gives, for each basis vector `v`,
`(r * (r - 1) * (h x) ^ (r - 2)) * (2 * ⟪x, v⟫) ^ 2
+ (r * (h x) ^ (r - 1)) * (2 * ⟪v, v⟫)`. Summing over the basis with
`∑ v, ⟪x, v⟫ ^ 2 = ‖x‖ ^ 2` leaves `(4 * r * (r - 1) + 2 * m * r) * (h x) ^ (r - 1)`, whose
coefficient vanishes for `r = -(m - 2) / 2`.

## ii. Key results

- `harmonicOnNhd_one_div_norm_pow_sub_two`, in namespace
  `MathlibExt.Analysis.Calculus.NormPowTwoSubDimHarmonicWanted`: the Newtonian kernel is
  harmonic on the complement of the origin.

## iii. References

- `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`,
  `iteratedDeriv_vcomp_two`, `iteratedDeriv_comp_two` (Mathlib).
-/

@[expose] public section

open Laplacian
open scoped RealInnerProductSpace Topology

namespace MathlibExt.Analysis

-- The Laplacian of a real power of `‖y‖ ^ 2` away from the origin, in every dimension.
private theorem laplacian_rpow_norm_sq {m : ℕ} (r : ℝ)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ≠ 0) :
    Δ (fun y : EuclideanSpace ℝ (Fin m) => (‖y‖ ^ (2 : ℕ)) ^ r) x =
      (4 * r * (r - 1) + (m : ℝ) * (2 * r)) * (‖x‖ ^ (2 : ℕ)) ^ (r - 1) := by
  set h : EuclideanSpace ℝ (Fin m) → ℝ := fun y => ‖y‖ ^ 2 with hh_def
  set g : ℝ → ℝ := fun s => s ^ r with hg_def
  set F : EuclideanSpace ℝ (Fin m) → ℝ := g ∘ h
  set e := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin m))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx2 : h x ≠ 0 := by
    have h1 : (‖x‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hxpos)
    simpa [hh_def] using h1
  have hx2pos : 0 < h x := by
    have h1 : (0 : ℝ) < (‖x‖ : ℝ) ^ 2 := by positivity
    simpa [hh_def] using h1
  have hΔ := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (E := EuclideanSpace ℝ (Fin m)) (F := ℝ) F e
  have hΔx : Δ F x = ∑ i, iteratedFDeriv ℝ 2 F x ![e i, e i] := congrFun hΔ x
  change Δ F x = _
  rw [hΔx]
  have hterm : ∀ v : EuclideanSpace ℝ (Fin m),
      iteratedFDeriv ℝ 2 F x (fun _ : Fin 2 => v) =
        (r * (r - 1) * (h x) ^ (r - 2)) * (2 * ⟪x, v⟫) ^ 2 +
        (r * (h x) ^ (r - 1)) * (2 * ⟪v, v⟫) := by
    intro v
    have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
      have h0 := HasDerivAt.add (hasDerivAt_const t x)
        (HasDerivAt.smul_const (hasDerivAt_id t) v)
      have hval : (0 : EuclideanSpace ℝ (Fin m)) + (1 : ℝ) • v = v := by simp
      rw [hval] at h0
      exact HasDerivAt.congr_of_eventuallyEq h0
        (Filter.Eventually.of_forall fun s => rfl)
    have hγ0 : (fun s : ℝ => x + s • v) 0 = x := by simp
    have hγ0' : x + (0 : ℝ) • v = x := hγ0
    have hderivγ : deriv (fun s : ℝ => x + s • v) 0 = v :=
      HasDerivAt.deriv (hγ 0)
    have hiterγ : iteratedDeriv 2 (fun s : ℝ => x + s • v) 0 = 0 := by
      have h1 : iteratedDeriv 1 (fun s : ℝ => x + s • v)
          = deriv (fun s : ℝ => x + s • v) := iteratedDeriv_one
      have h2 : iteratedDeriv 2 (fun s : ℝ => x + s • v)
          = deriv (deriv (fun s : ℝ => x + s • v)) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]
      have h3 : deriv (fun s : ℝ => x + s • v) = fun _ => v :=
        funext fun t => HasDerivAt.deriv (hγ t)
      rw [h2, h3]
      simp
    have hγ2 : ∀ t : ℝ, ContDiffAt ℝ 2 (fun s : ℝ => x + s • v) t :=
      fun t => by fun_prop
    have hF2 : ContDiffAt ℝ 2 F ((fun s : ℝ => x + s • v) 0) := by
      rw [hγ0]
      have hg : ContDiffAt ℝ 2 g (h x) := Real.contDiffAt_rpow_const_of_ne hx2
      have hh : ContDiffAt ℝ 2 h x := (contDiff_norm_sq ℝ).contDiffAt
      exact ContDiffAt.comp x hg hh
    have hhi0 : (h ∘ (fun s : ℝ => x + s • v)) 0 = h x := by
      change h ((fun s : ℝ => x + s • v) 0) = h x
      rw [hγ0]
    have hcg : ContDiffAt ℝ 2 g ((h ∘ (fun s : ℝ => x + s • v)) 0) := by
      rw [hhi0]
      exact Real.contDiffAt_rpow_const_of_ne hx2
    have hch : ContDiffAt ℝ 2 (h ∘ (fun s : ℝ => x + s • v)) 0 :=
      ContDiffAt.comp 0 (contDiff_norm_sq ℝ).contDiffAt (hγ2 0)
    have hderivg : deriv g (h x) = r * (h x) ^ (r - 1) := by
      have h0 := Real.hasDerivAt_rpow_const (x := h x) (p := r) (Or.inl hx2)
      exact HasDerivAt.deriv h0
    have hiter2g : iteratedDeriv 2 g (h x) = r * (r - 1) * (h x) ^ (r - 2) := by
      have hpoch : (descPochhammer ℝ 2).eval r = r * (r - 1) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, descPochhammer_succ_right,
          descPochhammer_one]
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_one]
      have hiter : iteratedDeriv 2 g (h x)
          = (descPochhammer ℝ 2).eval r * (h x) ^ (r - 2) := by
        rw [iteratedDeriv_eq_iterate]
        exact Real.iter_deriv_rpow_const r (h x) 2
      rw [hiter, hpoch]
    have hderivhi : deriv (h ∘ (fun s : ℝ => x + s • v)) 0 = 2 * ⟪x, v⟫ := by
      have h0 : ∀ t : ℝ, deriv (h ∘ (fun s : ℝ => x + s • v)) t
          = 2 * ⟪x + t • v, v⟫ :=
        fun t => HasDerivAt.deriv (HasDerivAt.norm_sq (hγ t))
      have h00 := h0 0
      simp only [zero_smul, add_zero] at h00
      exact h00
    have hiter2hi : iteratedDeriv 2 (h ∘ (fun s : ℝ => x + s • v)) 0
        = 2 * ⟪v, v⟫ := by
      have h1 : iteratedDeriv 1 (h ∘ (fun s : ℝ => x + s • v))
          = deriv (h ∘ (fun s : ℝ => x + s • v)) := iteratedDeriv_one
      have h2 : iteratedDeriv 2 (h ∘ (fun s : ℝ => x + s • v))
          = deriv (deriv (h ∘ (fun s : ℝ => x + s • v))) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]
      have hder : ∀ t : ℝ, deriv (h ∘ (fun s : ℝ => x + s • v)) t
          = 2 * ⟪x + t • v, v⟫ :=
        fun t => HasDerivAt.deriv (HasDerivAt.norm_sq (hγ t))
      have hfun : deriv (h ∘ (fun s : ℝ => x + s • v))
          = fun t : ℝ => 2 * ⟪x + t • v, v⟫ := funext hder
      have hexp : (fun t : ℝ => 2 * ⟪x + t • v, v⟫)
          = fun t : ℝ => 2 * (⟪x, v⟫ + t * ⟪v, v⟫) := by
        funext t
        show (2 : ℝ) * ⟪x + t • v, v⟫ = 2 * (⟪x, v⟫ + t * ⟪v, v⟫)
        rw [inner_add_left, real_inner_smul_left]
      have hlin : HasDerivAt (fun t : ℝ => 2 * (⟪x, v⟫ + t * ⟪v, v⟫))
          (2 * ⟪v, v⟫) 0 := by
        have h0 := HasDerivAt.const_mul 2
          (HasDerivAt.add (hasDerivAt_const 0 ⟪x, v⟫)
            (HasDerivAt.mul_const (hasDerivAt_id 0) ⟪v, v⟫))
        have hval : (2 : ℝ) * (0 + 1 * ⟪v, v⟫) = 2 * ⟪v, v⟫ := by ring
        rw [hval] at h0
        exact HasDerivAt.congr_of_eventuallyEq h0
          (Filter.Eventually.of_forall fun s => rfl)
      rw [h2, hfun, hexp]
      exact HasDerivAt.deriv hlin
    have hvcomp := iteratedDeriv_vcomp_two hF2 (hγ2 0)
    rw [hγ0'] at hvcomp
    have hFγ : F ∘ (fun s : ℝ => x + s • v)
        = g ∘ (h ∘ (fun s : ℝ => x + s • v)) := rfl
    rw [hFγ] at hvcomp
    have hcomp := iteratedDeriv_comp_two hcg hch
    rw [hcomp, hhi0, hderivγ, hiterγ, hderivg, hiter2g, hderivhi,
      hiter2hi] at hvcomp
    simp only [map_zero, add_zero] at hvcomp
    exact hvcomp.symm
  have hcons : ∀ v : EuclideanSpace ℝ (Fin m), ![v, v] = (fun _ : Fin 2 => v) := by
    intro v
    funext j
    fin_cases j <;> simp
  simp_rw [hcons, hterm, OrthonormalBasis.inner_eq_one e]
  have hreshape : ∀ c : ℝ, (r * (r - 1) * (h x) ^ (r - 2)) * (2 * c) ^ 2
      + (r * (h x) ^ (r - 1)) * (2 * 1)
      = (4 * (r * (r - 1) * (h x) ^ (r - 2))) * c ^ 2
        + 2 * (r * (h x) ^ (r - 1)) := by
    intro c; ring
  simp_rw [hreshape]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, OrthonormalBasis.sum_sq_inner_left,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_euclideanSpace_fin]
  have hpow : (h x) ^ (r - 2) * (h x) = (h x) ^ (r - 1) := by
    have h1 : (h x) ^ (r - 2) * (h x) ^ (1 : ℝ) = (h x) ^ (r - 1) := by
      rw [← Real.rpow_add hx2pos]
      congr 1
      ring
    simpa [Real.rpow_one] using h1
  have hhx : (‖x‖ : ℝ) ^ 2 = h x := rfl
  rw [hhx, nsmul_eq_mul]
  linear_combination (4 * r * (r - 1)) * hpow

private theorem one_div_norm_pow_eq_radial {m : ℕ} :
    (fun x : EuclideanSpace ℝ (Fin m) => 1 / ‖x‖ ^ (m - 2)) =
      fun x => (‖x‖ ^ (2 : ℕ)) ^ (-((m - 2 : ℕ) : ℝ) / 2) := by
  funext x
  rw [one_div, ← Real.rpow_natCast ‖x‖ (m - 2), ← Real.rpow_neg (norm_nonneg x),
    ← Real.rpow_natCast_mul (norm_nonneg x) 2]
  congr 1
  ring

namespace Calculus.NormPowTwoSubDimHarmonicWanted

/-- **The Newtonian kernel is harmonic away from the origin.** Let $m > 2$ be a natural number.
The function $x \mapsto 1/|x|^{m-2}$ on the Euclidean space $\mathbb{R}^m$, where $|x|$ is the
Euclidean norm, is harmonic on $\mathbb{R}^m \setminus \{0\}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_81.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem harmonicOnNhd_one_div_norm_pow_sub_two
    {m : ℕ} (hm : 2 < m) : InnerProductSpace.HarmonicOnNhd
  (fun x : EuclideanSpace ℝ (Fin m) => 1 / ‖x‖ ^ (m - 2)) ({0}ᶜ) := by
  rw [one_div_norm_pow_eq_radial]
  intro x hx
  have hne : x ≠ 0 := by simpa using hx
  let r : ℝ := -((m - 2 : ℕ) : ℝ) / 2
  have hcoeff : (4 : ℝ) * r * (r - 1) + (m : ℝ) * (2 * r) = 0 := by
    have hcast : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
      rw [Nat.cast_sub hm.le, Nat.cast_ofNat]
    dsimp only [r]
    rw [hcast]
    ring
  change InnerProductSpace.HarmonicAt (fun y : EuclideanSpace ℝ (Fin m) =>
    (‖y‖ ^ (2 : ℕ)) ^ r) x
  refine ⟨?_, ?_⟩
  · have hx2 : ‖x‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
    exact (Real.contDiffAt_rpow_const_of_ne hx2).comp x (contDiff_norm_sq ℝ).contDiffAt
  · have hv : ∀ᶠ y in 𝓝 x, y ≠ 0 := isOpen_ne.mem_nhds hne
    filter_upwards [hv] with y hy
    rw [Pi.zero_apply, laplacian_rpow_norm_sq r hy, hcoeff, zero_mul]

end Calculus.NormPowTwoSubDimHarmonicWanted

end MathlibExt.Analysis
