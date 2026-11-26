/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.ContinuousMap.Algebra
public import MathlibExt.Topology.ContinuousMap.SumRingEquiv
public import MathlibExt.Topology.ContinuousMap.SigmaRingEquiv
public import MathlibExt.Topology.ContinuousMap.Singleton
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Tactic.NormNum

/-!
# Compact-open multiplication and continuous-function recombination

Complex-valued continuous functions on the rational line use its usual
topology and the compact-open topology, without a local-compactness premise.
Sum, sigma, and singleton equivalences recover distinct nonzero complex
values and their products. Empty summands and an empty sigma index are
included in the recombination checks.
-/

noncomputable section

namespace MathlibExtTest.CompactOpenRingEquiv

open ContinuousMap

example : IsTopologicalRing C(ℚ, ℂ) :=
  ContinuousMap.complexCompactOpenTopologicalRing ℚ

example : Continuous (fun p : C(ℚ, ℂ) × C(ℚ, ℂ) => p.1 * p.2) :=
  continuous_mul

example :
    (ContinuousMap.const ℚ Complex.I * ContinuousMap.const ℚ Complex.I) (1 / 2) = -1 := by
  simp

private def sumFunction : C(Unit ⊕ Unit, ℂ) :=
  (sumRingEquiv Unit Unit ℂ).symm
    (ContinuousMap.const Unit Complex.I, ContinuousMap.const Unit 2)

example :
    (sumRingEquiv Unit Unit ℂ sumFunction).1 () = Complex.I ∧
      (sumRingEquiv Unit Unit ℂ sumFunction).2 () = 2 := by
  simp [sumFunction]

example :
    (sumFunction * sumFunction) (Sum.inl ()) = -1 ∧
      (sumFunction * sumFunction) (Sum.inr ()) = 4 := by
  norm_num [sumFunction]

example :
    (sumRingEquiv (Fin 0) Unit ℂ).symm
      (0, ContinuousMap.const Unit Complex.I) (Sum.inr ()) = Complex.I := by
  simp

private def sigmaFamily (i : Bool) : C(Unit, ℂ) :=
  ContinuousMap.const Unit (if i = true then 2 else Complex.I)

private def sigmaFunction : C((Σ _ : Bool, Unit), ℂ) :=
  (sigmaRingEquiv (fun _ : Bool => Unit) ℂ).symm sigmaFamily

example :
    sigmaFunction ⟨false, ()⟩ = Complex.I ∧ sigmaFunction ⟨true, ()⟩ = 2 ∧
      (sigmaRingEquiv (fun _ : Bool => Unit) ℂ (sigmaFunction * sigmaFunction)) false () = -1 := by
  norm_num [sigmaFunction, sigmaFamily]

example :
    (sigmaRingEquiv (fun _ : Fin 0 => Unit) ℂ).symm (fun _ => 0) = 0 := by
  ext ⟨i, x⟩
  exact Fin.elim0 i

example :
    constRingEquiv Unit ℂ Complex.I () = Complex.I ∧
      (constRingEquiv Unit ℂ).symm
        (constRingEquiv Unit ℂ Complex.I * constRingEquiv Unit ℂ Complex.I) = -1 := by
  simp

end MathlibExtTest.CompactOpenRingEquiv
