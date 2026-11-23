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
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public noncomputable section

/-!
# Actual higher-rank finite-image Artin and Swan conductors

The local group is the actual valuation decomposition subgroup of
Gal(L/K). Its lower filtration fixes the actual ring of integers modulo
powers of its maximal ideal. Conductors use Mathlib's invariant subspaces
`Representation.invariants` of the restricted representations, with weights
#G_i/#G_0; the Swan sum omits i=0. The conductor API assumes that `L/K` is
finite, so the decomposition group and its lower groups are finite and the
weights are ratios of positive integers.

The conductors take a certified bound: an index N with the actual proposition
G_N=1, beyond which every summand vanishes. For a finite extension of
nonarchimedean local fields such a bound exists (the lower filtration
terminates); that existence is a separate wanted statement, not proved here.
The completed independence theorems show that the conductors do not depend on
the bound. The generic weighted codimension sums over i < N, for any N and any
valued field, are named separately (`weightedCodimensionSum`,
`positiveWeightedCodimensionSum`); the named conductors require a finite Galois
extension of nonarchimedean local fields. The remaining integrality theorem concerns arbitrary
finite-dimensional rational adic representations, beyond the covered
one-dimensional abelian Artin-conductor formula.

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

/-- Actual lower numbering: the ring-of-integers congruence modulo m^(i+1). For a finite Galois
extension of nonarchimedean local fields these are Serre's lower ramification groups `G_i`
(Corps Locaux, Chapter IV, §1); in general they are the inertia subgroups of the powers of the
maximal ideal. -/
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
  (ρ : Representation ℚ_[ell] (DecompositionGroup K L) V)

/-- Codimension of the subspace fixed by the displayed ramification subgroup, using
Mathlib's invariants of the restricted representation. It is defined only for a
finite-dimensional representation, where it is a genuine codimension. -/
def invariantCodimension [Module.Finite ℚ_[ell] V] (H : Subgroup (DecompositionGroup K L)) : ℕ :=
  Module.finrank ℚ_[ell] V -
    Module.finrank ℚ_[ell] (Representation.invariants (ρ.comp H.subtype))

variable [Module.Finite ℚ_[ell] V]

theorem invariantCodimension_bot : invariantCodimension K L ell V ρ ⊥ = 0 := by
  have : Representation.invariants (ρ.comp (⊥ : Subgroup (DecompositionGroup K L)).subtype) =
      ⊤ := by
    ext v
    simp only [Representation.mem_invariants, Submodule.mem_top, iff_true]
    rintro ⟨σ, hσ⟩
    rw [Subgroup.mem_bot] at hσ
    subst hσ
    simp
  rw [invariantCodimension, this, finrank_top, Nat.sub_self]

/-- The lower-numbering contribution with denominator #G_0. Since `L/K` is finite, the lower
groups are finite and nonempty, so `#G_i/#G_0` is a ratio of positive integers. -/
def conductorSummand [FiniteDimensional K L] (i : ℕ) : ℚ :=
  (Nat.card (lowerGroup K L i) : ℚ) / (Nat.card (lowerGroup K L 0) : ℚ) *
    invariantCodimension K L ell V ρ (lowerGroup K L i)

/-- The weighted codimension sum `∑_{i < N} (#G_i/#G_0) codim V^{G_i}`, including the inertia
contribution at `i = 0`. For a finite Galois extension of local fields with `G_N = 1` it is the
Artin conductor (`artinConductor`). -/
def weightedCodimensionSum [FiniteDimensional K L] (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, conductorSummand K L ell V ρ i

/-- The weighted codimension sum over the indices `0 < i < N`, omitting the inertia term `i = 0`.
For a finite Galois extension of local fields with `G_N = 1` it is the Swan conductor
(`swanConductor`). -/
def positiveWeightedCodimensionSum [FiniteDimensional K L] (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, if i = 0 then 0 else conductorSummand K L ell V ρ i

/-- The Artin conductor of a representation of the Galois group of a finite Galois extension of
nonarchimedean local fields, computed from a certified ramification bound `N` with `G_N = 1`; it
does not depend on the bound (`artinConductor_eq`). -/
def artinConductor [TopologicalSpace K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    [FiniteDimensional K L] [IsGalois K L] (N : {N : ℕ // lowerGroup K L N = ⊥}) : ℚ :=
  weightedCodimensionSum K L ell V ρ N

/-- The Swan conductor of a representation of the Galois group of a finite Galois extension of
nonarchimedean local fields, computed from a certified ramification bound `N` with `G_N = 1`; it
does not depend on the bound (`swanConductor_eq`). -/
def swanConductor [TopologicalSpace K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    [FiniteDimensional K L] [IsGalois K L] (N : {N : ℕ // lowerGroup K L N = ⊥}) : ℚ :=
  positiveWeightedCodimensionSum K L ell V ρ N

variable [FiniteDimensional K L]

/-- The `i = 0` summand has weight `#G_0/#G_0 = 1`: it is the codimension of the inertia
invariants. -/
theorem conductorSummand_zero :
    conductorSummand K L ell V ρ 0 = invariantCodimension K L ell V ρ (lowerGroup K L 0) := by
  have : (Nat.card (lowerGroup K L 0) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simp [conductorSummand, this]

theorem conductorSummand_eq_zero_of_bound (N : ℕ) (hN : lowerGroup K L N = ⊥)
    (i : ℕ) (hi : N ≤ i) : conductorSummand K L ell V ρ i = 0 := by
  unfold conductorSummand
  rw [lowerGroup_eq_bot_of_bound K L N hN i hi, invariantCodimension_bot]
  simp

/-- For a positive cutoff, the weighted sum is the positive weighted sum plus the codimension
of the inertia invariants. -/
theorem weightedCodimensionSum_eq_positive_add (N : ℕ) (hN : 0 < N) :
    weightedCodimensionSum K L ell V ρ N = positiveWeightedCodimensionSum K L ell V ρ N +
      invariantCodimension K L ell V ρ (lowerGroup K L 0) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp [weightedCodimensionSum, positiveWeightedCodimensionSum, Finset.sum_range_succ',
    conductorSummand_zero]

/-- Once actual ramification vanishes, extending the weighted sum changes nothing. -/
theorem weightedCodimensionSum_eq_of_le_bound (N M : ℕ) (hN : lowerGroup K L N = ⊥)
    (hNM : N ≤ M) :
    weightedCodimensionSum K L ell V ρ N = weightedCodimensionSum K L ell V ρ M := by
  unfold weightedCodimensionSum
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro i _ hi
  exact conductorSummand_eq_zero_of_bound K L ell V ρ N hN i
    (by simpa using hi)

/-- Once actual ramification vanishes, extending the positive weighted sum changes nothing. -/
theorem positiveWeightedCodimensionSum_eq_of_le_bound (N M : ℕ) (hN : lowerGroup K L N = ⊥)
    (hNM : N ≤ M) : positiveWeightedCodimensionSum K L ell V ρ N =
      positiveWeightedCodimensionSum K L ell V ρ M := by
  unfold positiveWeightedCodimensionSum
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro i _ hi
  simp [conductorSummand_eq_zero_of_bound K L ell V ρ N hN i (by simpa using hi)]

section LocalField

variable [TopologicalSpace K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]

/-- The Artin conductor is independent of the certified ramification bound. -/
theorem artinConductor_eq (N M : {N : ℕ // lowerGroup K L N = ⊥}) :
    artinConductor K L ell V ρ N = artinConductor K L ell V ρ M := by
  unfold artinConductor
  rcases le_total N.1 M.1 with h | h
  · exact weightedCodimensionSum_eq_of_le_bound K L ell V ρ N M N.2 h
  · exact (weightedCodimensionSum_eq_of_le_bound K L ell V ρ M N M.2 h).symm

/-- The Swan conductor is independent of the certified ramification bound. -/
theorem swanConductor_eq (N M : {N : ℕ // lowerGroup K L N = ⊥}) :
    swanConductor K L ell V ρ N = swanConductor K L ell V ρ M := by
  unfold swanConductor
  rcases le_total N.1 M.1 with h | h
  · exact positiveWeightedCodimensionSum_eq_of_le_bound K L ell V ρ N M N.2 h
  · exact (positiveWeightedCodimensionSum_eq_of_le_bound K L ell V ρ M N M.2 h).symm

/-- The Artin conductor is the Swan conductor plus the codimension of the inertia
invariants. -/
theorem artinConductor_eq_swanConductor_add (N : {N : ℕ // lowerGroup K L N = ⊥}) :
    artinConductor K L ell V ρ N = swanConductor K L ell V ρ N +
      invariantCodimension K L ell V ρ (lowerGroup K L 0) := by
  rcases Nat.eq_zero_or_pos N.1 with h | h
  · have h0 : lowerGroup K L 0 = ⊥ := by simpa [h] using N.2
    simp [artinConductor, swanConductor, weightedCodimensionSum,
      positiveWeightedCodimensionSum, h, h0,
      invariantCodimension_bot]
  · exact weightedCodimensionSum_eq_positive_add K L ell V ρ N h

end LocalField

end Conductors

end MathlibExt.NumberTheory.FiniteRamificationConductors
