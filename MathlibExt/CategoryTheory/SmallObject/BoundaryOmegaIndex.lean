/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Original countable small-object stage indices

The actual Cardinal.aleph0.ord.ToType indexing order is identified with
natural-number stages through its native ordinal coordinate map. Zero
and every actual successor are retained by the whole order isomorphism.
-/

@[expose] public section

noncomputable section
universe u

namespace CategoryTheory.SmallObject

/-- The actual native ordinal coordinate of a natural-number stage. -/
def aleph0Stage (n : ℕ) : Cardinal.aleph0.{u}.ord.ToType :=
  Ordinal.ToType.mk ⟨n, by
    simpa only [Cardinal.ord_aleph0, Set.mem_Iio] using Ordinal.natCast_lt_omega0 n⟩

/-- The whole native stage map is strictly increasing. -/
theorem aleph0Stage_strictMono : StrictMono (aleph0Stage.{u}) := by
  intro n m h
  apply Ordinal.ToType.mk.strictMono
  change (n : Ordinal.{u}) < (m : Ordinal.{u})
  exact_mod_cast h

/-- Every actual original countable small-object stage has a natural-number ordinal coordinate. -/
theorem aleph0Stage_surjective : Function.Surjective (aleph0Stage.{u}) := by
  intro j
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp
    (by simpa only [Cardinal.ord_aleph0, Set.mem_Iio] using j.toOrd.property)
  refine ⟨n, ?_⟩
  have he : (⟨(n : Ordinal.{u}), by
      simpa only [Cardinal.ord_aleph0, Set.mem_Iio] using Ordinal.natCast_lt_omega0 n⟩ :
      Set.Iio Cardinal.aleph0.{u}.ord) = Ordinal.ToType.mk.symm j :=
    Subtype.ext hn.symm
  exact (congrArg Ordinal.ToType.mk he).trans (Ordinal.ToType.mk.apply_symm_apply j)

/-- The original countable stage order is exactly the natural-number stage order. -/
def aleph0StageOrderIso : ℕ ≃o Cardinal.aleph0.{u}.ord.ToType :=
  StrictMono.orderIsoOfSurjective aleph0Stage aleph0Stage_strictMono aleph0Stage_surjective

attribute [local instance] Cardinal.orderBotAleph0OrdToType

/-- Stage zero is the SAME actual original bottom stage. -/
theorem aleph0Stage_zero : aleph0Stage.{u} 0 = ⊥ := aleph0StageOrderIso.map_bot

/-- Every natural-number successor is the SAME actual original successor stage. -/
theorem aleph0Stage_succ (n : ℕ) : aleph0Stage.{u} (n + 1) = Order.succ (aleph0Stage n) :=
  aleph0StageOrderIso.map_succ n

end CategoryTheory.SmallObject
