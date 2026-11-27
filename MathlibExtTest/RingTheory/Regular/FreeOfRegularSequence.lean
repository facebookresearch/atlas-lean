/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Regular.FreeOfRegularSequence

@[expose] public section

open RingTheory.Sequence

-- `exactSource` consumer with the original binders.
example {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (hA : RingTheory.Sequence.IsRegular A rs)
    (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : RingTheory.Sequence.IsRegular M rs) : Module.Free A M :=
  Module.free_of_isRegular_of_span_eq_maximalIdeal rs hA hspan M hM

-- Base case: over a field the empty sequence spans the maximal ideal `⊥`,
-- and every finite module is free.
example : Module.Free ℚ (ℚ × ℚ) := by
  have hspan : Ideal.ofList ([] : List ℚ) = IsLocalRing.maximalIdeal ℚ := by
    rw [Ideal.ofList_nil]
    exact IsLocalRing.maximalIdeal_eq_bot.symm
  exact Module.free_of_isRegular_of_span_eq_maximalIdeal []
    (RingTheory.Sequence.IsRegular.nil ℚ ℚ) hspan _
    (RingTheory.Sequence.IsRegular.nil ℚ (ℚ × ℚ))

-- Consumer of the weakly regular form with its own binders.
example {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : RingTheory.Sequence.IsWeaklyRegular M rs) : Module.Free A M :=
  Module.free_of_isWeaklyRegular_of_span_eq_maximalIdeal rs hspan M hM

-- The weakly regular form needs no nontriviality: from the empty sequence, every
-- finite `ℚ`-module is free, the zero module included. The regular form does not
-- reach the zero module, since `IsRegular M []` forces `M` to be nontrivial.
example (M : Type*) [AddCommGroup M] [Module ℚ M] [Module.Finite ℚ M] :
    Module.Free ℚ M :=
  Module.free_of_isWeaklyRegular_of_span_eq_maximalIdeal []
    (by rw [Ideal.ofList_nil]; exact IsLocalRing.maximalIdeal_eq_bot.symm) M
    (RingTheory.Sequence.IsWeaklyRegular.nil ℚ M)

-- Both hypotheses of the regular form fail for the sequence `[0]` over `ℚ` on the
-- zero module: `0` is not regular on `ℚ`, and `⊤ = Ideal.ofList [0] • ⊤` on `Unit`.
-- The weakly regular form still applies: `[0]` generates the maximal ideal `⊥` of
-- `ℚ` and is weakly regular on `Unit`.
example : ¬ RingTheory.Sequence.IsRegular ℚ [(0 : ℚ)] ∧
    ¬ RingTheory.Sequence.IsRegular Unit [(0 : ℚ)] ∧ Module.Free ℚ Unit :=
  ⟨fun h => IsSMulRegular.not_zero
      ((isWeaklyRegular_singleton_iff ℚ (0 : ℚ)).mp h.toIsWeaklyRegular),
    fun h => h.top_ne_smul (Subsingleton.elim _ _),
    Module.free_of_isWeaklyRegular_of_span_eq_maximalIdeal [0]
      (by simp [IsLocalRing.maximalIdeal_eq_bot]) Unit
      ((isWeaklyRegular_singleton_iff Unit (0 : ℚ)).mpr IsSMulRegular.zero)⟩
