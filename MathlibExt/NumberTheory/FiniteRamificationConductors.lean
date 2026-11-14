/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The lower filtration definitions and elementary laws are adapted from
TauCeti/RingTheory/LocalRing/RamificationGroup.lean and
TauCeti/NumberTheory/LocalField/RamificationGroup.lean at
62bbc0596dc3539d488232e4e924a338548ea0a9:
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. Licensed under Apache 2.0.
Modification notice: use the actual Mathlib valuation decomposition group;
define higher-rank Artin/Swan sums from actual invariant subspaces and
prove independence of the supplied actual finite ramification bound.
-/

module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public noncomputable section

/-!
# Actual higher-rank finite-image Artin and Swan conductors

The local group is the actual valuation decomposition subgroup of
Gal(L/K). Its lower filtration fixes the actual ring of integers modulo
powers of its maximal ideal. Conductors use actual invariant subspaces,
with weights #G_i/#G_0; the Swan sum omits i=0.

A bound N is supplied with the actual proposition G_N=1. Existing public
ramification theory produces such bounds; no new existence goal is made
here. The completed independence theorem makes the finite sums intrinsic.
The remaining integrality theorem concerns arbitrary finite-dimensional
rational adic representations, beyond the covered one-dimensional
abelian Artin-conductor formula.

Reference: Serre, Corps Locaux, Chapter IV, §1 and Chapter VI, §2.
-/

namespace MathlibExt.NumberTheory.FiniteRamificationConductors

open ValuativeRel
open scoped BigOperators

universe u v w

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  [ValuativeRel L]

/-- The actual valuation ring defining the local ramification problem. -/
abbrev integerRing := (valuation L).valuationSubring

/-- The actual decomposition group of that valuation ring. -/
abbrev DecompositionGroup := (integerRing L).decompositionSubgroup K

/-- Actual lower numbering: the ring-of-integers congruence modulo m^(i+1). -/
def lowerGroup (i : ℤ) : Subgroup (DecompositionGroup K L) :=
  (IsLocalRing.maximalIdeal (integerRing L) ^ (i + 1).toNat).inertia
    (DecompositionGroup K L)

theorem mem_lowerGroup_iff {i : ℤ} {σ : DecompositionGroup K L} :
    σ ∈ lowerGroup K L i ↔
      ∀ a : integerRing L, σ • a - a ∈
        IsLocalRing.maximalIdeal (integerRing L) ^ (i + 1).toNat :=
  Ideal.mem_inertia

theorem lowerGroup_zero :
    lowerGroup K L 0 = (IsLocalRing.maximalIdeal (integerRing L)).inertia
      (DecompositionGroup K L) := by
  simp [lowerGroup]

theorem lowerGroup_eq_top_of_le_neg_one {i : ℤ} (hi : i ≤ -1) :
    lowerGroup K L i = ⊤ := by
  have h : (i + 1).toNat = 0 := by omega
  ext σ
  simp [mem_lowerGroup_iff, h]

theorem lowerGroup_antitone : Antitone (lowerGroup K L) := by
  intro i j hij σ hσ
  rw [mem_lowerGroup_iff] at hσ ⊢
  exact fun a ↦ Ideal.pow_le_pow_right (by omega) (hσ a)

theorem lowerGroup_eq_bot_of_bound (N : ℕ) (hN : lowerGroup K L N = ⊥)
    (i : ℕ) (hi : N ≤ i) : lowerGroup K L i = ⊥ :=
  eq_bot_iff.mpr ((lowerGroup_antitone K L (by exact_mod_cast hi)).trans hN.le)

section Conductors

variable (ell : ℕ) [Fact ell.Prime] (V : Type w) [AddCommGroup V] [Module ℚ_[ell] V]
  [Module.Finite ℚ_[ell] V] (ρ : Representation ℚ_[ell] (DecompositionGroup K L) V)

/-- The actual subspace fixed by the displayed ramification subgroup. -/
def invariantSubspace (H : Subgroup (DecompositionGroup K L)) : Submodule ℚ_[ell] V where
  carrier := {v | ∀ σ ∈ H, ρ σ v = v}
  zero_mem' σ _ := map_zero _
  add_mem' hv hw σ hσ := by rw [map_add, hv σ hσ, hw σ hσ]
  smul_mem' a v hv σ hσ := by rw [map_smul, hv σ hσ]

omit [Module.Finite ℚ_[ell] V] in
theorem invariantSubspace_bot : invariantSubspace K L ell V ρ ⊥ = ⊤ := by
  ext v
  simp [invariantSubspace]

/-- Codimension of the actual invariant subspace. -/
def invariantCodimension (H : Subgroup (DecompositionGroup K L)) : ℕ :=
  Module.finrank ℚ_[ell] V - Module.finrank ℚ_[ell] (invariantSubspace K L ell V ρ H)

/-- The lower-numbering contribution with denominator #G_0. -/
def conductorSummand (i : ℕ) : ℚ :=
  (Nat.card (lowerGroup K L i) : ℚ) / (Nat.card (lowerGroup K L 0) : ℚ) *
    invariantCodimension K L ell V ρ (lowerGroup K L i)

/-- Artin conductor, including the inertia contribution at i=0. -/
def artinConductor (N : ℕ) : ℚ := ∑ i ∈ Finset.range N, conductorSummand K L ell V ρ i

/-- Swan conductor, omitting the inertia term i=0. -/
def swanConductor (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, if i = 0 then 0 else conductorSummand K L ell V ρ i

omit [Module.Finite ℚ_[ell] V] in
theorem conductorSummand_eq_zero_of_bound (N : ℕ) (hN : lowerGroup K L N = ⊥)
    (i : ℕ) (hi : N ≤ i) : conductorSummand K L ell V ρ i = 0 := by
  unfold conductorSummand invariantCodimension
  rw [lowerGroup_eq_bot_of_bound K L N hN i hi, invariantSubspace_bot]
  simp

omit [Module.Finite ℚ_[ell] V] in
/-- Once actual ramification vanishes, extending the Artin sum changes nothing. -/
theorem artinConductor_eq_of_le_bound (N M : ℕ) (hN : lowerGroup K L N = ⊥)
    (hNM : N ≤ M) : artinConductor K L ell V ρ N = artinConductor K L ell V ρ M := by
  unfold artinConductor
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro i _ hi
  exact conductorSummand_eq_zero_of_bound K L ell V ρ N hN i
    (by simpa using hi)

omit [Module.Finite ℚ_[ell] V] in
/-- The Artin sum is independent of the actual finite ramification bound. -/
theorem artinConductor_independent (N M : ℕ) (hN : lowerGroup K L N = ⊥)
    (hM : lowerGroup K L M = ⊥) : artinConductor K L ell V ρ N =
      artinConductor K L ell V ρ M := by
  rcases le_total N M with h | h
  · exact artinConductor_eq_of_le_bound K L ell V ρ N M hN h
  · exact (artinConductor_eq_of_le_bound K L ell V ρ M N hM h).symm

omit [Module.Finite ℚ_[ell] V] in
/-- The Swan sum is independent of the actual finite ramification bound. -/
theorem swanConductor_independent (N M : ℕ) (hN : lowerGroup K L N = ⊥)
    (hM : lowerGroup K L M = ⊥) : swanConductor K L ell V ρ N =
      swanConductor K L ell V ρ M := by
  have hle (a b : ℕ) (ha : lowerGroup K L a = ⊥) (hab : a ≤ b) :
      swanConductor K L ell V ρ a = swanConductor K L ell V ρ b := by
    unfold swanConductor
    apply Finset.sum_subset (Finset.range_mono hab)
    intro i _ hi
    simp [conductorSummand_eq_zero_of_bound K L ell V ρ a ha i (by simpa using hi)]
  rcases le_total N M with h | h
  · exact hle N M hN h
  · exact (hle M N hM h).symm

end Conductors

end MathlibExt.NumberTheory.FiniteRamificationConductors
