/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Data.Fin.VecNotation

/-!
# Symmetry of the first two derivative directions

Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^(n+2).
The (n+2)-th Fréchet derivative at x is unchanged when its first two directions
are exchanged, with any ordered tail of n directions retained. A fixed-tail
evaluation reduces these two directions to the second derivative of an
F-valued C² map.

This finite-smoothness symmetry is used for the elementary differentials in
Ketcheson–Ranocha, *Computing with B-series*, arXiv:2111.11680v2, equations 11–12.
-/

@[expose] public section

open scoped ContDiff

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {n : ℕ}

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^(n+2).
For a fixed family m : Fin n → E, the map y ↦ D^n f(y)(m) is C². -/
private theorem contDiff_two_iteratedFDeriv_apply
    (hf : ContDiff ℝ (n + 2 : ℕ) f) (m : Fin n → E) :
    ContDiff ℝ 2 (fun y ↦ iteratedFDeriv ℝ n f y m) := by
  have horder : (2 : ℕ∞ω) + n ≤ (n + 2 : ℕ) := by
    norm_cast
    omega
  have hD : ContDiff ℝ 2 (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right horder
  exact ContDiff.continuousLinearMap_comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F m) hD

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^(n+2).
For x,a,b : E and m : Fin n → E, put g(y) = D^n f(y)(m).
Then D^(n+2) f(x)(a,b,m) equals D²g(x)(a,b). -/
theorem ContDiff.iteratedFDeriv_cons_cons_eq_fderiv_fderiv
    (hf : ContDiff ℝ (n + 2 : ℕ) f) (x a b : E) (m : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b m)) =
      fderiv ℝ (fderiv ℝ (fun y ↦ iteratedFDeriv ℝ n f y m)) x a b := by
  let g : E → F := fun y ↦ iteratedFDeriv ℝ n f y m
  have hG : ContDiff ℝ 2 g := contDiff_two_iteratedFDeriv_apply hf m
  have hn : (n : ℕ∞ω) < (n + 2 : ℕ) := by norm_cast; omega
  have hn1 : ((n + 1 : ℕ) : ℕ∞ω) < (n + 2 : ℕ) := by norm_cast; omega
  have hD : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    ContDiff.differentiable_iteratedFDeriv hn hf
  have hD1 : Differentiable ℝ (iteratedFDeriv ℝ (n + 1) f) :=
    ContDiff.differentiable_iteratedFDeriv hn1 hf
  have heq : (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.cons b m)) =
      (fun y ↦ fderiv ℝ g y b) := by
    funext y
    simpa only [Fin.tail_cons, Fin.cons_zero] using
      (hD y).iteratedFDeriv_succ_apply_left' (m := Fin.cons b m)
  have hG' : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  calc
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b m)) =
        fderiv ℝ (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.cons b m)) x a := by
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        (hD1 x).iteratedFDeriv_succ_apply_left' (m := Fin.cons a (Fin.cons b m))
    _ = fderiv ℝ (fun y ↦ fderiv ℝ g y b) x a := by rw [heq]
    _ = fderiv ℝ (fderiv ℝ g) x a b := by
      have h := congrArg (fun L : E →L[ℝ] F ↦ L a)
        (fderiv_clm_apply hG' (differentiableAt_const b))
      simpa using h

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^(n+2).
For all x,a,b : E and m : Fin n → E,
D^(n+2) f(x)(a,b,m) = D^(n+2) f(x)(b,a,m). Directions may repeat. -/
theorem ContDiff.iteratedFDeriv_cons_cons_swap
    (hf : ContDiff ℝ (n + 2 : ℕ) f) (x a b : E) (m : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b m)) =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons b (Fin.cons a m)) := by
  rw [hf.iteratedFDeriv_cons_cons_eq_fderiv_fderiv x a b m,
    hf.iteratedFDeriv_cons_cons_eq_fderiv_fderiv x b a m]
  exact ((contDiff_two_iteratedFDeriv_apply hf m).contDiffAt.isSymmSndFDerivAt (by simp)).eq a b

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^(n+2).
For x : E and m : Fin (n+2) → E, evaluation of D^(n+2) f(x) is unchanged
when m is composed with the transposition of positions 0 and 1. -/
theorem ContDiff.iteratedFDeriv_comp_swap_zero_one
    (hf : ContDiff ℝ (n + 2 : ℕ) f) (x : E) (m : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x (m ∘ Equiv.swap 0 1) =
      iteratedFDeriv ℝ (n + 2) f x m := by
  have hm : m = Fin.cons (m 0) (Fin.cons (m 1) (Fin.tail (Fin.tail m))) := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => cases i using Fin.cases <;> simp [Fin.tail]
  have hswap :
      Fin.cons (m 0) (Fin.cons (m 1) (Fin.tail (Fin.tail m))) ∘ Equiv.swap 0 1 =
        Fin.cons (m 1) (Fin.cons (m 0) (Fin.tail (Fin.tail m))) := by
    simpa only [Matrix.vecCons] using
      Matrix.cons_cons_comp_swap_zero_one (m 0) (m 1) (Fin.tail (Fin.tail m))
  calc
    iteratedFDeriv ℝ (n + 2) f x (m ∘ Equiv.swap 0 1) =
        iteratedFDeriv ℝ (n + 2) f x
          (Fin.cons (m 1) (Fin.cons (m 0) (Fin.tail (Fin.tail m)))) := by
      rw [← hswap, ← hm]
    _ = iteratedFDeriv ℝ (n + 2) f x
        (Fin.cons (m 0) (Fin.cons (m 1) (Fin.tail (Fin.tail m)))) :=
      hf.iteratedFDeriv_cons_cons_swap x (m 1) (m 0) (Fin.tail (Fin.tail m))
    _ = iteratedFDeriv ℝ (n + 2) f x m := by rw [← hm]

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^(n+2).
At each x : E, the continuous (n+2)-multilinear map D^(n+2) f(x) is unchanged
by exchanging its input positions 0 and 1. -/
theorem ContDiff.domDomCongr_iteratedFDeriv_swap_zero_one
    (hf : ContDiff ℝ (n + 2 : ℕ) f) (x : E) :
    (iteratedFDeriv ℝ (n + 2) f x).domDomCongr (Equiv.swap 0 1) =
      iteratedFDeriv ℝ (n + 2) f x := by
  ext m
  exact hf.iteratedFDeriv_comp_swap_zero_one x m
