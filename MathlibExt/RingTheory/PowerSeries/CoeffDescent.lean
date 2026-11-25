/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean`
and
`P2M/Sol/S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace PowerSeries

/-- Descent of a finite linear combination of power series to a subfield:
if every coefficient of each `g i` lies in `K₀` and every coefficient of
`∑ i, c i • g i` lies in `K₀`, then the same combination can be written
with scalars `c' i ∈ K₀`.

No linear independence, finiteness, or separability hypothesis is needed:
a `K₀`-linear retraction of `L` onto `K₀` (which exists since `K₀` is a
field) applied to each `c i` gives the descended scalars, and it fixes
every coefficient of the combination. -/
public theorem exists_sum_smul_eq_of_forall_coeff_mem
    {L : Type} [Field L] (K₀ : Subfield L) {n : ℕ} (g : Fin n → PowerSeries L)
    (hg : ∀ (i : Fin n) (m : ℕ), PowerSeries.coeff (R := L) m (g i) ∈ K₀)
    (c : Fin n → L) (h : ∀ m : ℕ, PowerSeries.coeff (R := L) m (∑ i, c i • g i) ∈ K₀) :
    ∃ c' : Fin n → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i := by
  classical
  let ι : K₀ →ₗ[K₀] L := Algebra.linearMap K₀ L
  have hι : Function.Injective ι :=
    fun x y hxy => Subtype.ext (by simpa [ι] using hxy)
  obtain ⟨π, hπ⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hι)
  have hπι : ∀ z : K₀, π (algebraMap K₀ L z) = z := by
    intro z
    have hz : (π.comp ι) z = z := by rw [hπ]; rfl
    simpa [ι] using hz
  refine ⟨fun i => (π (c i) : L), fun i => (π (c i)).2, ?_⟩
  apply PowerSeries.ext
  intro m
  have hcoeff : ∀ (a : L) (φ : PowerSeries L),
      PowerSeries.coeff (R := L) m (a • φ) = a * PowerSeries.coeff (R := L) m φ := by
    intro a φ
    rw [map_smul, smul_eq_mul]
  have hsum : PowerSeries.coeff (R := L) m (∑ i, c i • g i)
      = ∑ i, c i * PowerSeries.coeff (R := L) m (g i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hcoeff (c i) (g i)
  have hsum' : PowerSeries.coeff (R := L) m (∑ i, (π (c i) : L) • g i)
      = ∑ i, (π (c i) : L) * PowerSeries.coeff (R := L) m (g i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hcoeff _ (g i)
  rw [hsum', hsum]
  have key : ((π (∑ i, c i * PowerSeries.coeff (R := L) m (g i)) : K₀) : L)
      = ∑ i, (π (c i) : L) * PowerSeries.coeff (R := L) m (g i) := by
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmul : c i * PowerSeries.coeff (R := L) m (g i)
        = (⟨PowerSeries.coeff (R := L) m (g i), hg i m⟩ : K₀) • c i := by
      simp [Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [hmul, map_smul, smul_eq_mul]
    push_cast
    exact mul_comm _ _
  have hmem : (∑ i, c i * PowerSeries.coeff (R := L) m (g i)) ∈ K₀ := by
    rw [← hsum]
    exact h m
  calc ∑ i, (π (c i) : L) * PowerSeries.coeff (R := L) m (g i)
      = ((π (∑ i, c i * PowerSeries.coeff (R := L) m (g i)) : K₀) : L) := key.symm
    _ = ∑ i, c i * PowerSeries.coeff (R := L) m (g i) := by
        have hfix : π (∑ i, c i * PowerSeries.coeff (R := L) m (g i))
            = ⟨∑ i, c i * PowerSeries.coeff (R := L) m (g i), hmem⟩ :=
          hπι ⟨∑ i, c i * PowerSeries.coeff (R := L) m (g i), hmem⟩
        rw [hfix]

end PowerSeries
