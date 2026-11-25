/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Fourier.Vorticity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

open TorusSobolev
open scoped ComplexConjugate
noncomputable section

namespace TorusFourier
private def triad : Polynomial :=
  let b := AddMonoidAlgebra.single (![1, 0] : Frequency) (1 : ℂ) +
    AddMonoidAlgebra.single (![0, 2] : Frequency) Complex.I +
    AddMonoidAlgebra.single (![1, 2] : Frequency) Complex.I
  b + conjugate b

private theorem triad_real : IsReal triad := by
  rw [isReal_iff_conjugate_eq]
  simp only [triad, map_add, conjugate_conjugate]
  abel

-- Both ordered interactions contribute: 2 - 2/4 = 3/2.
example : (transport triad).coeff ![1, 2] = (3 / 2 : ℂ) * Complex.I := by
  norm_num [triad, transport, bracket, derivative, streamFunction,
    map_add, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    frequencyWeight, Fin.sum_univ_two, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]

example : (transport triad).coeff ![1, 0] = (1 / 10 : ℂ) := by
  norm_num [triad, transport, bracket, derivative, streamFunction,
    map_add, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    frequencyWeight, Fin.sum_univ_two, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]

example : (transport triad).coeff ![0, 2] = -(8 / 5 : ℂ) * Complex.I := by
  norm_num [triad, transport, bracket, derivative, streamFunction,
    map_add, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    frequencyWeight, Fin.sum_univ_two, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]

private theorem triad_project : project (squareModes 2) triad = triad := by
  norm_num [triad, project, map_add, mem_squareModes,
    funext_iff, Fin.forall_fin_two]

private theorem triad_support : triad.coeff.support ⊆ squareModes 2 := by
  simpa only [triad_project] using project_support (squareModes 2) triad

-- Cancellation is tested on the nonzero complex triad above.
example : ∑ k ∈ squareModes 2, conj (triad.coeff k) *
    (project (squareModes 2) (transport triad)).coeff k = 0 :=
  sum_project_transport_enstrophy_cancel _ (squareModes_symmetric 2) triad_support triad_real

example : ∑ k ∈ squareModes 2, conj (triad.coeff k) *
    (project (squareModes 2) (transport triad)).coeff k / (frequencyWeight k : ℂ) = 0 :=
  sum_project_transport_energy_cancel _ (squareModes_symmetric 2) triad_support triad_real

-- Projecting the output and recomputing from projected input are different operations.
example : (project (squareModes 1) (transport triad)).coeff ![1, 0] = (1 / 10 : ℂ) := by
  rw [project_coeff]
  norm_num [mem_squareModes, funext_iff, Fin.forall_fin_two]
  norm_num [triad, transport, bracket, derivative, streamFunction,
    map_add, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    frequencyWeight, Fin.sum_univ_two, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]

example : (transport (project (squareModes 1) triad)).coeff ![1, 0] = 0 := by
  norm_num [triad, project, mem_squareModes, transport, bracket, derivative, streamFunction,
    map_add, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    frequencyWeight, Fin.sum_univ_two, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]


-- Recover the actual prescribed vorticity, discharging the zero-mode condition.
example : derivative 0 (velocity triad 1) - derivative 1 (velocity triad 0) = triad ∧
    derivative 0 (velocity triad 0) + derivative 1 (velocity triad 1) = 0 := by
  refine ⟨velocity_curl ?_, velocity_divergence triad⟩
  norm_num [triad, Finsupp.single_apply, funext_iff, Fin.forall_fin_two]

-- The nonzero transport is real and remains real after the symmetric projection.
example : IsReal (project (squareModes 2) (transport triad)) :=
  triad_real.transport.project _ (squareModes_symmetric 2)

-- The mean-zero assumption cannot be omitted from inverse-Laplacian recovery.
example : laplacian (streamFunction (AddMonoidAlgebra.single (0 : Frequency) (7 : ℂ))) = 0 ∧
    (AddMonoidAlgebra.single (0 : Frequency) (7 : ℂ) : Polynomial) ≠ 0 := by
  norm_num [streamFunction, laplacian, frequencyWeight, derivative]

-- The zero cutoff really retains no modes.
example : squareModes 0 = ∅ := by
  ext k
  simp only [mem_squareModes, Finset.notMem_empty, iff_false, not_and]
  intro h0 hk
  apply h0
  ext j
  have h := hk j
  change k j = 0
  omega

-- Convective evolution has the negative of the positive transport coefficient.
example : (-project (squareModes 2) (transport triad)).coeff ![1, 2] =
    -(3 / 2 : ℂ) * Complex.I := by
  norm_num [triad, project, mem_squareModes, transport, bracket, derivative, streamFunction,
    map_add, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    frequencyWeight, Fin.sum_univ_two, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]

end TorusFourier
