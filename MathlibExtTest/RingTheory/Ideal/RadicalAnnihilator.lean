/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.RadicalAnnihilator
public import Mathlib.Data.ZMod.Basic

@[expose] public section

-- `exactSource` consumer with the original `Type` binders.
example {S : Type} [CommRing S] [IsReduced S] (a : S) :
    (Ideal.span {a}).radical ⊓ ((Ideal.span {a}).annihilator).radical = ⊥ ∧
      ∀ s : S, a * s ∈ ((Ideal.span {a}).annihilator).radical →
        s ∈ ((Ideal.span {a}).annihilator).radical :=
  Ideal.radical_span_inf_radical_annihilator_eq_bot_of_isReduced a

-- Higher-universe consumer.
example {S : Type 1} [CommRing S] [IsReduced S] (a : S) :
    (Ideal.span {a}).radical ⊓ ((Ideal.span {a}).annihilator).radical = ⊥ ∧
      ∀ s : S, a * s ∈ ((Ideal.span {a}).annihilator).radical →
        s ∈ ((Ideal.span {a}).annihilator).radical :=
  Ideal.radical_span_inf_radical_annihilator_eq_bot_of_isReduced a

-- Reducedness matters: in `ZMod 4`, `2` lies in both radicals for `a = 2`,
-- so their infimum is not `⊥`.
example :
    ¬ ((Ideal.span {(2 : ZMod 4)}).radical ⊓
      ((Ideal.span {(2 : ZMod 4)}).annihilator).radical = ⊥) := by
  intro h
  have h2 : (2 : ZMod 4) ∈ (Ideal.span {(2 : ZMod 4)}).radical ⊓
      ((Ideal.span {(2 : ZMod 4)}).annihilator).radical := by
    constructor
    · refine ⟨2, ?_⟩
      rw [show (2 : ZMod 4) ^ 2 = 0 by decide]
      exact Submodule.zero_mem _
    · refine ⟨1, ?_⟩
      rw [pow_one, Submodule.mem_annihilator_span_singleton]
      decide
  rw [h, Ideal.mem_bot] at h2
  exact (by decide : (2 : ZMod 4) ≠ 0) h2
