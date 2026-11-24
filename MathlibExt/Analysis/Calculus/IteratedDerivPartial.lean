/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Iterated derivatives in the second scalar coordinate

For a scalar function of two real variables, an iterated ordinary derivative in
its second coordinate is the joint iterated Fréchet derivative evaluated on copies
of the unit vector `(0,1)`. This gives a pointwise operator-norm bound without a
factorial, including derivative order zero. A jointly smooth function has jointly
smooth second-coordinate derivatives of every order.

The proofs specialize the affine chain rule and multilinear evaluation already
available in Mathlib. The finite-order formulas need only joint Cn regularity.
-/

@[expose] public section

open scoped ContDiff

namespace ContDiff

/-- An actual nth derivative in the second coordinate is the joint nth Fréchet
 derivative evaluated on n copies of `(0,1)`. Finite joint Cn regularity suffices. -/
theorem iteratedDeriv_snd_eq_iteratedFDeriv {q : ℝ → ℝ → ℝ} {n : ℕ}
    (hq : ContDiff ℝ n (Function.uncurry q)) (p : ℝ × ℝ) :
    iteratedDeriv n (q p.1) p.2 =
      iteratedFDeriv ℝ n (Function.uncurry q) p (fun _ => ((0,1) : ℝ × ℝ)) := by
  let L : ℝ →L[ℝ] ℝ × ℝ := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  let F := fun z : ℝ × ℝ => Function.uncurry q ((p.1,0)+z)
  have hF : ContDiff ℝ n F := hq.comp (contDiff_const.add contDiff_id)
  have he : q p.1 = F ∘ L := by
    funext x
    simp [F, L]
  rw [he, iteratedDeriv_eq_iteratedFDeriv,
    L.iteratedFDeriv_comp_right hF p.2 (i := n) (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  dsimp only [F]
  rw [iteratedFDeriv_comp_add_left]
  simp [L]

/-- The nth second-coordinate derivative is bounded by the joint nth derivative's
operator norm. Unit directions introduce no factorial or extra multiplicative factor. -/
theorem norm_iteratedDeriv_snd_le {q : ℝ → ℝ → ℝ} {n : ℕ}
    (hq : ContDiff ℝ n (Function.uncurry q)) (p : ℝ × ℝ) :
    ‖iteratedDeriv n (q p.1) p.2‖ ≤ ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ := by
  rw [hq.iteratedDeriv_snd_eq_iteratedFDeriv p]
  simpa using (iteratedFDeriv ℝ n (Function.uncurry q) p).le_opNorm
    (fun _ => ((0,1) : ℝ × ℝ))

/-- Every second-coordinate iterated derivative of a jointly smooth scalar function
is jointly smooth in both coordinates. -/
theorem contDiff_iteratedDeriv_snd {q : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ ∞ (Function.uncurry q)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (q p.1) p.2) := by
  simp_rw [(hq.of_le (by simp : (n : WithTop ℕ∞) ≤ ∞)).iteratedDeriv_snd_eq_iteratedFDeriv]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) ℝ
    (fun _ => (0,1))).contDiff.comp (hq.iteratedFDeriv_right (by simp))

end ContDiff
