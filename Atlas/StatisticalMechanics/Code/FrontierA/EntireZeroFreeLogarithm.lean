/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv









open Set

namespace StatMech.FrontierA

noncomputable section


theorem exists_entireLogarithm
    (f : Complex -> Complex)
    (hf : Differentiable Complex f)
    (hzero : forall z, f z ≠ 0) :
    exists g : Complex -> Complex,
      Differentiable Complex g /\ (forall z, Complex.exp (g z) = f z) := by
  have hlogDeriv : Differentiable Complex (logDeriv f) := by
    change Differentiable Complex (fun z => deriv f z / f z)
    exact differentiableOn_univ.mp
      ((hf.differentiableOn.deriv isOpen_univ).div hf.differentiableOn
        (fun z _ => hzero z))
  obtain ⟨g, hg0, hg⟩ :=
    hlogDeriv.isExactOn_univ.with_val_at (0 : Complex) 0
  have hg' : forall z, HasDerivAt g (logDeriv f z) z := by
    intro z
    exact hg z (mem_univ z)
  have hgDiff : Differentiable Complex g :=
    fun z => (hg' z).differentiableAt
  let q : Complex -> Complex := fun z => f z * Complex.exp (-g z)
  have hqDiff : Differentiable Complex q := by
    intro z
    exact ((hf z).hasDerivAt.mul
      ((Complex.hasDerivAt_exp (-g z)).comp z (hg' z).neg)).differentiableAt
  have hqDeriv : forall z, deriv q z = 0 := by
    intro z
    have hexp : HasDerivAt (fun w => Complex.exp (-g w))
        (Complex.exp (-g z) * (-logDeriv f z)) z :=
      (Complex.hasDerivAt_exp (-g z)).comp z (hg' z).neg
    have hmul := (hf z).hasDerivAt.mul hexp
    change HasDerivAt q
      (deriv f z * Complex.exp (-g z) +
        f z * (Complex.exp (-g z) * (-logDeriv f z))) z at hmul
    rw [hmul.deriv]
    rw [logDeriv_apply]
    field_simp [hzero z]
    ring
  have hqConst : forall z, q z = q 0 := by
    intro z
    exact is_const_of_deriv_eq_zero hqDiff hqDeriv z 0
  refine ⟨fun z => Complex.log (f 0) + g z, ?_, ?_⟩
  · intro z
    exact (differentiableAt_const (c := Complex.log (f 0))).add (hgDiff z)
  intro z
  have hfactor : f z = f 0 * Complex.exp (g z) := by
    have hconst := hqConst z
    change f z * Complex.exp (-g z) =
      f 0 * Complex.exp (-g 0) at hconst
    rw [hg0, neg_zero, Complex.exp_zero, mul_one] at hconst
    calc
      f z = (f z * Complex.exp (-g z)) * Complex.exp (g z) := by
        rw [mul_assoc, ← Complex.exp_add]
        simp
      _ = f 0 * Complex.exp (g z) := by rw [hconst]
  rw [Complex.exp_add, Complex.exp_log (hzero 0), hfactor]

end

end StatMech.FrontierA
