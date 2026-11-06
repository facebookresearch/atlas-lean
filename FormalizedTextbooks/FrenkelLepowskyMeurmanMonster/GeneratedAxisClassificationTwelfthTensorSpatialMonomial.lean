/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedTensorMatrixBindings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedKernelCertificates

/-! Complete original monomial numerators act on integer tensors by a single signed pullback. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A complete signed monomial integer matrix uses exactly one original input coordinate. -/
theorem generatedTwelfth_integer_matrix_monomial
    (N : Matrix (Fin 24) (Fin 24) ℤ) (p : Fin 24 → Fin 24) (s : Fin 24 → ℤ)
    (hN : ∀ i k, N i k = s i * if p i = k then 1 else 0)
    (v : Fin 24 → ℤ) (j : Fin 24) :
    ∑ k : Fin 24, N j k * v k = s j * v (p j) := by
  simp_rw [hN]
  simp

/-- All nine complete original physical kernel numerators are exact single signed pullbacks. -/
theorem generatedTwelfth_tensor_spatial_monomial
    (g : Fin 9) (n : Fin 4096) (j : Fin 24) :
    generatedTwelfthSpinTensorSpatialInteger (generatedTwelfthCertifiedKernelIndex g) n j =
      nortonUIntegerSign (generatedTwelfthCertifiedKernelLetterSign g j) *
        generatedTwelfthSpinTensorInputInteger n
          (generatedTwelfthCertifiedKernelLetterBackward g j) := by
  unfold generatedTwelfthSpinTensorSpatialInteger
  apply generatedTwelfth_integer_matrix_monomial
  intro i k
  rw [generatedTwelfth_certified_tensor_matrix_entries,
    generatedTwelfth_certified_kernel_matrix_entries]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
