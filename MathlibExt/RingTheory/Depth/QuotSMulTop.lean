/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Depth.Basic
import Mathlib.RingTheory.Regular.Category

/-!
# Depth drops by one modulo a nonzerodivisor

Let `(R, 𝔪)` be a Noetherian local ring, `M` a nonzero finitely generated `R`-module and
`x ∈ 𝔪` a nonzerodivisor on `M`. We prove `depth (M / x M) + 1 = depth M`, hence
`depth (M / x M) = depth M - 1`.

Depth is Mathlib's `IsLocalRing.depth`, defined through vanishing of `Ext` from the residue field.
For a nonzero finite module over a Noetherian local ring it agrees with the supremum of the
lengths of `M`-regular sequences in `𝔪` (`IsLocalRing.depth_eq_sSup_length_isRegular`), which is
the definition used in the Stacks project.

## Main results

* `IsLocalRing.one_le_depth_iff`: `1 ≤ depth M` iff `𝔪` contains a nonzerodivisor on `M`.
* `IsLocalRing.depth_quotSMulTop_add_one`: `depth (M / x M) + 1 = depth M`.
* `IsLocalRing.depth_quotSMulTop`: `depth (M / x M) = depth M - 1`.

## Proof

The inequality `depth M - 1 ≤ depth (M / x M)` comes from the long exact `Ext` sequence of
`0 → M → M → M / x M → 0` (`ModuleCat.depth_min_snd_fst_sub_one_le_trd_right`). The inequality
`depth (M / x M) + 1 ≤ depth M` holds because `x` followed by an `M / x M`-regular sequence in
`𝔪` is an `M`-regular sequence in `𝔪`.

## References

* The Stacks project, Tag 090R (Lemma 10.72.7), part (1).
* The Stacks project, Tag 00LE (Definition 10.72.1) for depth.
-/

@[expose] public section

universe v u

open IsLocalRing RingTheory.Sequence Pointwise

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

variable [Small.{v} R] [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M]

/-- Over a Noetherian local ring `R`, a nonzero finitely generated module `M` has
`1 ≤ IsLocalRing.depth M` if and only if some element of the maximal ideal is a nonzerodivisor
on `M`. -/
theorem one_le_depth_iff :
    1 ≤ IsLocalRing.depth (ModuleCat.of R M) ↔ ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  rw [IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of R M)]
  constructor
  · intro h
    by_contra! hne
    refine absurd h (not_le.mpr (lt_of_le_of_lt (sSup_le ?_) zero_lt_one))
    rintro b ⟨s, hs, hsm, rfl⟩
    cases s with
    | nil => simp
    | cons y t =>
      exact absurd ((isRegular_cons_iff M y t).mp hs).1
        (hne y (hsm y List.mem_cons_self))
  · rintro ⟨x, hx, hreg⟩
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
    refine le_sSup ⟨[x], ?_, by simpa using hx, by simp⟩
    exact (isRegular_cons_iff M x []).mpr ⟨hreg, IsRegular.nil R (QuotSMulTop x M)⟩

/-- **Depth drops by one modulo a nonzerodivisor** (Stacks, Tag 090R, Lemma 10.72.7,
part (1)). Let `R` be a Noetherian local ring, `M` a nonzero finitely generated `R`-module and
`x` an element of the maximal ideal that is a nonzerodivisor on `M`. Then
`IsLocalRing.depth (M / x M) + 1 = IsLocalRing.depth M`, as an equality in `ℕ∞`.

Here depth is Mathlib's `Ext`-based `IsLocalRing.depth`, which for these modules equals the
supremum of the lengths of regular sequences in the maximal ideal
(`IsLocalRing.depth_eq_sSup_length_isRegular`), the definition used in the source. The module
`M / x M` is `QuotSMulTop x M`. -/
theorem depth_quotSMulTop_add_one {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 =
      IsLocalRing.depth (ModuleCat.of R M) := by
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  refine le_antisymm ?_ ?_
  · rw [IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of R (QuotSMulTop x M)),
      IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of R M), ENat.sSup_add]
    swap
    · exact ⟨0, [], IsRegular.nil R (QuotSMulTop x M), by simp, rfl⟩
    refine iSup₂_le fun b ⟨s, hs, hsm, hb⟩ ↦ le_sSup ⟨x :: s, ?_, ?_, ?_⟩
    · exact (isRegular_cons_iff M x s).mpr ⟨hreg, hs⟩
    · exact List.forall_mem_cons.mpr ⟨hx, hsm⟩
    · simp [← hb]
  · have h := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
      (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) _
      (IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg)
    exact tsub_le_iff_right.mp ((le_inf tsub_le_self le_rfl).trans h)

/-- **Depth drops by one modulo a nonzerodivisor** (Stacks, Tag 090R, Lemma 10.72.7,
part (1)), in the printed form: for a Noetherian local ring `R`, a nonzero finitely generated
`R`-module `M` and an element `x` of the maximal ideal that is a nonzerodivisor on `M`,
`IsLocalRing.depth (M / x M) = IsLocalRing.depth M - 1` (truncated subtraction in `ℕ∞`; since
`depth M ≥ 1` here, it is the honest difference). See `depth_quotSMulTop_add_one`. -/
theorem depth_quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) =
      IsLocalRing.depth (ModuleCat.of R M) - 1 := by
  rw [← depth_quotSMulTop_add_one hx hreg]
  simp

end IsLocalRing
