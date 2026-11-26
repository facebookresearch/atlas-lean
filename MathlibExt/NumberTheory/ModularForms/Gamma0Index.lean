/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_ProjectiveLine.lean`,
`Theorems/Thm_ModularCurve_Gamma0_index.lean`,
`Theorems/Thm_ModularCurve_card_quotient_gamma0_eq_index.lean`,
`P2M/Sol/S_ModularCurve_Gamma0_index.lean` and
`P2M/Sol/S_ModularCurve_card_quotient_gamma0_eq_index.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed, the names restated in Mathlib style, and the proofs rewritten to use
Mathlib APIs directly. The Dedekind psi value is the arithmetic function
`ArithmeticFunction.dedekindPsi` already in this repository.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi

import MathlibExt.GroupTheory.CyclicSubgroupsZModSquare
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.SLTwoZModSurjective
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Index of the congruence subgroup Gamma0

For `N ≠ 0`, the index of `Gamma0 N` in `SL(2, Z)` is the Dedekind psi value
`psi(N)`. The cardinality of the quotient of the modular group by the image of
`Gamma0 N` equals that index for every `N`; both are `0` when the index is
infinite, as for `N = 0`. The proof identifies the quotient by the Borel
subgroup of upper-triangular matrices with the projective line
`ProjectiveLine (ZMod N)`, whose points are counted by
`card_projectiveLine_zmod`, and transfers the index along reduction modulo `N`,
which is surjective by
`Matrix.SpecialLinearGroup.map_intCastRingHom_zmod_surjective`.
-/

@[expose] public section

namespace ModularCurve

open Matrix CongruenceSubgroup
open scoped MatrixGroups

section Borel

variable {R : Type*} [CommRing R]

/-- **Borel subgroup of $\mathrm{SL}_2(R)$.** For a commutative ring $R$, the subgroup of
$\mathrm{SL}_2(R)$ of upper-triangular matrices, those whose lower-left entry is zero. -/
def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    change (A * B).1 1 0 = 0
    rw [SpecialLinearGroup.coe_mul, (Matrix.two_mul_expl A.1 B.1).2.2.1, hA, hB]
    ring
  inv_mem' := by
    intro A hA
    change (A⁻¹).1 1 0 = 0
    have h : (A⁻¹).1 = !![A.1 1 1, -A.1 0 1; -A.1 1 0, A.1 0 0] :=
      congrArg Subtype.val (SpecialLinearGroup.SL2_inv_expl A)
    rw [h]
    exact neg_eq_zero.mpr hA

theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl

end Borel

section QuotientBorel
variable {R : Type*} [CommRing R]

private theorem isUnimodularRow_firstCol (A : SpecialLinearGroup (Fin 2) R) :
    IsUnimodularRow (A.1 0 0) (A.1 1 0) := by
  refine ⟨A.1 1 1, -A.1 0 1, ?_⟩
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have h := A.2; rwa [Matrix.det_fin_two] at h
  linear_combination hdet

private def firstColumnClass (A : SpecialLinearGroup (Fin 2) R) : ProjectiveLine R :=
  ⟦⟨(A.1 0 0, A.1 1 0), isUnimodularRow_firstCol A⟩⟧

private theorem firstColumnClass_eq_iff (A B : SpecialLinearGroup (Fin 2) R) :
    firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R := by
  constructor
  · intro hAB
    obtain ⟨u, h1, h2⟩ := Quotient.exact hAB
    have h1' : (u : R) * A.1 0 0 = B.1 0 0 := h1
    have h2' : (u : R) * A.1 1 0 = B.1 1 0 := h2
    change (A⁻¹ * B).1 1 0 = 0
    have hinv : (A⁻¹).1 = !![A.1 1 1, -A.1 0 1; -A.1 1 0, A.1 0 0] :=
      congrArg Subtype.val (SpecialLinearGroup.SL2_inv_expl A)
    have e10 : (A⁻¹).1 1 0 = -A.1 1 0 := by simp [hinv]
    have e11 : (A⁻¹).1 1 1 = A.1 0 0 := by simp [hinv]
    have hentry : (A⁻¹ * B).1 1 0 = -A.1 1 0 * B.1 0 0 + A.1 0 0 * B.1 1 0 := by
      rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e10, e11]
    rw [hentry, ← h1', ← h2']; ring
  · intro hAB
    have hB : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
    have hC10 : (A⁻¹ * B).1 1 0 = 0 := hAB
    have hCdet : (A⁻¹ * B).1 0 0 * (A⁻¹ * B).1 1 1 = 1 := by
      have h := (A⁻¹ * B).2; rw [Matrix.det_fin_two, hC10] at h; linear_combination h
    have hB00 : B.1 0 0 = A.1 0 0 * (A⁻¹ * B).1 0 0 + A.1 0 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).1
    have hB10 : B.1 1 0 = A.1 1 0 * (A⁻¹ * B).1 0 0 + A.1 1 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).2.2.1
    refine Quotient.sound ⟨⟨(A⁻¹ * B).1 0 0, (A⁻¹ * B).1 1 1, hCdet,
      (mul_comm _ _).trans hCdet⟩, ?_, ?_⟩
    · change (A⁻¹ * B).1 0 0 * A.1 0 0 = B.1 0 0; rw [hB00, hC10]; ring
    · change (A⁻¹ * B).1 0 0 * A.1 1 0 = B.1 1 0; rw [hB10, hC10]; ring

private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) := by
  have hwd : ∀ A B : SpecialLinearGroup (Fin 2) R, QuotientGroup.leftRel (borel R) A B →
      firstColumnClass A = firstColumnClass B := by
    intro A B hAB
    rw [QuotientGroup.leftRel_apply] at hAB
    exact (firstColumnClass_eq_iff A B).mpr hAB
  refine Nat.card_eq_of_bijective (fun q => Quotient.liftOn' q firstColumnClass hwd) ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂' q q' ?_
    intro A B hAB
    have hAB' : firstColumnClass A = firstColumnClass B := hAB
    exact (QuotientGroup.eq).mpr ((firstColumnClass_eq_iff A B).mp hAB')
  · intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨x, y, hxy⟩ := v.2
    refine ⟨QuotientGroup.mk ⟨!![v.1.1, -y; v.1.2, x], by
      rw [Matrix.det_fin_two_of]; linear_combination hxy⟩, ?_⟩
    change firstColumnClass _ = ⟦v⟧
    refine Quotient.sound ⟨1, ?_, ?_⟩
    · change (1 : R) * !![v.1.1, -y; v.1.2, x] 0 0 = v.1.1; simp
    · change (1 : R) * !![v.1.1, -y; v.1.2, x] 1 0 = v.1.2; simp

end QuotientBorel

private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  ext A
  rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
  constructor
  · intro hA
    change (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0; simpa using hA
  · intro hA
    have hA' : (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0 := hA; simpa using hA'

/-- **Index of $\Gamma_0(N)$.** For every natural number $N \ne 0$, the index of the congruence
subgroup $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb{Z})$ is the Dedekind psi value $\psi(N)$, that is,
$N \prod_{p \mid N} (1 + 1/p)$ with $p$ running over the prime divisors of $N$. -/
theorem Gamma0_index (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).index = ArithmeticFunction.dedekindPsi N := by
  have h1 : (CongruenceSubgroup.Gamma0 N).index = (borel (ZMod N)).index := by
    rw [Gamma0_eq_comap_borel]
    exact Subgroup.index_comap_of_surjective _
      (Matrix.SpecialLinearGroup.map_intCastRingHom_zmod_surjective N)
  rw [h1, Subgroup.index_eq_card, card_quotient_borel,
    card_projectiveLine_zmod N (NeZero.ne N)]

end ModularCurve

open scoped MatrixGroups in
/-- **Cosets of $\Gamma_0(N)$ in the modular group.** For every natural number $N$, the
cardinality of the quotient of the modular group `𝒮ℒ` (the image of $\mathrm{SL}_2(\mathbb{Z})$ in
$\mathrm{GL}_2(\mathbb{R})$) by the image of $\Gamma_0(N)$ equals the index of $\Gamma_0(N)$ in
$\mathrm{SL}_2(\mathbb{Z})$. Both are natural numbers, so both are $0$ when the quotient is
infinite, as it is for $N = 0$: `Nat.card` of an infinite type and `Subgroup.index` of a subgroup
of infinite index are $0$. -/
theorem ModularCurve.card_quotient_gamma0_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) =
      (CongruenceSubgroup.Gamma0 N).index := by
  rw [← Subgroup.index_eq_card]
  change Subgroup.relIndex _ _ = _
  rw [MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _
      Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
