/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerIncomingTree
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPacket

/-! Genuine source support transport is parametric in the actual fiber. Sparse cache
soundness is parametric in its carrier, rows, dictionary and source coefficients.
Both zero and nonzero cases are retained; no Ninth action is used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual transported preferred target of an original source packet label. -/
def generatedTenthRootTwoGenericSourceTarget (f : localFiberSubgroup)
    (a : GeneratedAxisGlobalFifthShortPacketIndex) : GriessShortIndex :=
  griessShortPermutation f.val.2 (generatedAxisGlobalFifthShortPacketLabel a)

/-- Every nonzero actual coefficient comes from the complete original source catalogue. -/
theorem generatedTenth_root_two_generic_actual_nonzero_covered
    (f : localFiberSubgroup) (r : GriessShortIndex)
    (hr : (griessConwayEncode (rhoLocal (localFiberIntoH f) generatedFifthAxis)).2.1 r ≠ 0) :
    ∃ a : GeneratedAxisGlobalFifthShortPacketIndex,
      generatedTenthRootTwoGenericSourceTarget f a = r := by
  let u := (griessShortPermutation f.val.2).symm r
  have hu : griessShortPermutation f.val.2 u = r := Equiv.apply_symm_apply _ r
  have hn : (griessConwayEncode generatedFifthAxis).2.1 u ≠ 0 := by
    intro h
    apply hr
    rw [generatedFourth_local_short, ← hu, localShortOperator_image, h, mul_zero]
  obtain ⟨a, ha⟩ := generatedNinth_original_short_nonzero_covered u hn
  refine ⟨a, ?_⟩
  change griessShortPermutation f.val.2 (generatedNinthOriginalShortIndex a) = r
  exact (congrArg (griessShortPermutation f.val.2) ha).trans hu

/-- A sparse dictionary stores only its exact indexed integer value, or zero. -/
def generatedTenthRootTwoGenericDictionaryCoefficient {R A : Type*}
    (address : R → ℕ) (key : A → ℕ) (value : A → ℤ)
    (tree : GeneratedNinthIncomingTree A) (r : R) : ℤ :=
  match tree.lookup key (address r) with
  | none => 0
  | some a => value a

/-- Every nonzero candidate cache entry has its genuine addressed source row. -/
theorem generatedTenth_root_two_generic_cache_nonzero_covered {R A K : Type*}
    (address : R → ℕ) (hinjective : Function.Injective address)
    (key : A → ℕ) (value : A → ℤ) (tree : GeneratedNinthIncomingTree A)
    (row : A → K) (target : K → R)
    (hkey : ∀ a, key a = address (target (row a))) (r : R)
    (h : generatedTenthRootTwoGenericDictionaryCoefficient address key value tree r ≠ 0) :
    ∃ k : K, target k = r := by
  unfold generatedTenthRootTwoGenericDictionaryCoefficient at h
  split at h
  · exact False.elim (h rfl)
  · rename_i a ha
    refine ⟨row a, ?_⟩
    apply hinjective
    exact (hkey a).symm.trans (GeneratedNinthIncomingTree.lookup_sound _ _ _ _ ha)

/-- Full source-row soundness and coverage bind every cache coordinate, including zero. -/
theorem generatedTenth_root_two_generic_cache_actual {R A K : Type*}
    (actual : R → ℝ) (address : R → ℕ) (hinjective : Function.Injective address)
    (key : A → ℕ) (value : A → ℤ) (tree : GeneratedNinthIncomingTree A)
    (row : A → K) (target : K → R) (numerator : K → ℤ) (D : ℕ)
    (hkey : ∀ a, key a = address (target (row a)))
    (hcoverage : ∀ k,
      generatedTenthRootTwoGenericDictionaryCoefficient address key value tree (target k) =
        numerator k)
    (hactualCoverage : ∀ r, actual r ≠ 0 → ∃ k, target k = r)
    (hrows : ∀ k, actual (target k) = (numerator k : ℝ) / D) (r : R) :
    actual r =
      (generatedTenthRootTwoGenericDictionaryCoefficient address key value tree r : ℝ) / D := by
  by_cases hc : generatedTenthRootTwoGenericDictionaryCoefficient address key value tree r = 0
  · rw [hc, Int.cast_zero, zero_div]
    apply not_ne_iff.mp
    intro hr
    obtain ⟨k, hk⟩ := hactualCoverage r hr
    have hn : numerator k = 0 := by rw [← hcoverage, hk, hc]
    apply hr
    rw [← hk, hrows, hn, Int.cast_zero, zero_div]
  · obtain ⟨k, hk⟩ := generatedTenth_root_two_generic_cache_nonzero_covered address
      hinjective key value tree row target hkey r hc
    rw [← hk, hrows, hcoverage]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
