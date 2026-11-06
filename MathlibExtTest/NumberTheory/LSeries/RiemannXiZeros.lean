/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RiemannXiZeros

/-!
# Tests for the zeros of the Riemann `ξ` function

The symmetries of `riemannZetaNontrivialZeros`, the finiteness of the zeros in horizontal strips,
and the existence of an enumeration of the zeros with multiplicity.
-/

@[expose] public section

open RiemannXi ComplexConjugate

namespace RiemannXiZerosTest

example {ρ : ℂ} (hρ : ρ ∈ riemannZetaNontrivialZeros) :
    ρ ≠ 0 ∧ ρ ≠ 1 ∧ 1 - ρ ∈ riemannZetaNontrivialZeros ∧ conj ρ ∈ riemannZetaNontrivialZeros :=
  ⟨ne_zero_of_mem_riemannZetaNontrivialZeros hρ, ne_one_of_mem_riemannZetaNontrivialZeros hρ,
    one_sub_mem_riemannZetaNontrivialZeros hρ, conj_mem_riemannZetaNontrivialZeros hρ⟩

/-- A zero of `ζ` with negative real part is a trivial zero. -/
example {s : ℂ} (hs : s.re < 0) (h : riemannZeta s = 0) : ∃ n : ℕ, 0 < n ∧ s = -(2 * n) :=
  exists_eq_neg_two_mul_of_riemannZeta_eq_zero_of_re_neg hs h

/-- Finitely many nontrivial zeros in any box. -/
example (R h : ℝ) : {ρ | ρ ∈ riemannZetaNontrivialZeros ∧ |ρ.im - R| ≤ h}.Finite := by
  simpa using finite_setOf_mem_riemannZetaNontrivialZeros_abs_im_sub_le R h

example (w : ℂ) : analyticOrderAt riemannXi w ≠ ⊤ := analyticOrderAt_riemannXi_ne_top w

example : riemannXi 0 ≠ 0 := riemannXi_zero_ne_zero

/-- The enumeration hypothesis is satisfiable. -/
example : ∃ (ι : Type) (z : ι → ℂ), ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w :=
  exists_card_eq_analyticOrderAt

/-- An enumeration lists exactly the nontrivial zeros. -/
example : ∃ (ι : Type) (z : ι → ℂ), Set.range z = riemannZetaNontrivialZeros := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  refine ⟨ι, z, Set.Subset.antisymm ?_ fun ρ hρ => exists_eq_of_card_eq_analyticOrderAt hz hρ⟩
  rintro _ ⟨n, rfl⟩
  exact mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz n

/-- The reflected family `1 - z` is again an enumeration. -/
example {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    ∀ w, ENat.card {n // 1 - z n = w} = analyticOrderAt riemannXi w :=
  card_one_sub_eq_analyticOrderAt hz

/-- `ξ'/ξ` is odd about `1/2`. -/
example (s : ℂ) : logDeriv riemannXi (1 - s) = -logDeriv riemannXi s :=
  logDeriv_riemannXi_one_sub s

end RiemannXiZerosTest
