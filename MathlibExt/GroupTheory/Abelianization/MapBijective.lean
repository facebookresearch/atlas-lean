/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Bijectivity reflected by abelianization of commutative groups

The original group map is bijective when its abelianization map is bijective.
The source and target groups may have independent universes.
-/

noncomputable section

universe v w

public section

namespace MonoidHom

private theorem abelianization_of_injective (G : Type v) [Group G] [IsMulCommutative G] :
    Function.Injective (Abelianization.of : G →* Abelianization G) := by
  apply (MonoidHom.ker_eq_bot_iff (Abelianization.of : G →* Abelianization G)).mp
  rw [Abelianization.ker_of, commutator_eq_bot]

private theorem abelianization_of_surjective (G : Type v) [Group G] :
    Function.Surjective (Abelianization.of : G →* Abelianization G) :=
  QuotientGroup.mk_surjective

/-- Bijectivity of abelianization reflects the exact original map between commutative groups. -/
theorem bijective_of_abelianization_map
    {G : Type v} {H : Type w} [Group G] [Group H]
    [IsMulCommutative G] [IsMulCommutative H] (f : G →* H)
    (hf : Function.Bijective (Abelianization.map f)) : Function.Bijective f := by
  constructor
  · intro a b h
    apply abelianization_of_injective G
    apply hf.1
    exact congrArg (Abelianization.of : H →* Abelianization H) h
  · intro b
    obtain ⟨q, hq⟩ := hf.2 (Abelianization.of b)
    obtain ⟨a, ha⟩ := abelianization_of_surjective G q
    refine ⟨a, ?_⟩
    apply abelianization_of_injective H
    exact (Abelianization.map_of f a).symm.trans ((congrArg (Abelianization.map f) ha).trans hq)

end MonoidHom
