/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Undecidable

@[expose] public section

/-!
# Tests for undecidability on multi-stack machines

The halting problem in its three forms, Rice's theorem used to rederive undecidability of
halting on input `0`, and mapping reductions.
-/

set_option autoImplicit false

open Computability Turing Cslib.Decidability MetaMathlibExt.TM2Recursive
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.Undecidable

example : ¬TM2Decidable fun c : Code ↦ (c.eval 0).Dom := not_tm2Decidable_halting 0

example : TM2Recognizable (fun c : Code ↦ (c.eval 0).Dom) ∧
    ¬TM2CoRecognizable fun c : Code ↦ (c.eval 0).Dom :=
  ⟨tm2Recognizable_halting 0, not_tm2CoRecognizable_halting 0⟩

example : ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
    ¬TM2Decidable fun n : ℕ ↦ TM2HaltsOn tm ((encodeNat n).map e.symm) :=
  exists_not_tm2Decidable_tm2HaltsOn

/-- Rice's theorem is not vacuous: "defined at `0`" separates the identity from the empty
function, so no machine decides it. -/
example : ¬TM2Decidable fun c : Code ↦ c.eval ∈ {f : ℕ →. ℕ | 0 ∈ f.Dom} := by
  intro h
  have hg : (fun _ : ℕ ↦ (Part.none : Part ℕ)) ∈ {f : ℕ →. ℕ | 0 ∈ f.Dom} :=
    rice_tm2 _ h (f := fun n ↦ Part.some n) Nat.Partrec.some Nat.Partrec.none
      ((PFun.mem_dom _ _).mpr ⟨0, Part.mem_some 0⟩)
  obtain ⟨y, hy⟩ := (PFun.mem_dom _ _).mp hg
  simp at hy

/-- The identity reduction, with a machine computing its action on codes. -/
example (p : ℕ → Prop) : ∃ f : ℕ → ℕ, (∃ F : ℕ → ℕ,
    Nonempty (TM2Computable encodeNat encodeNat F) ∧ ∀ a, F (Encodable.encode a) =
      Encodable.encode (f a)) ∧ ∀ a, p a ↔ p (f a) :=
  manyOneReducible_iff_exists_tm2.mp (manyOneReducible_refl p)

/-- Decidability transfers along a reduction. -/
example (p : ℕ → Prop) (hp : TM2Decidable p) : TM2Decidable p :=
  tm2Decidable_of_manyOneReducible (manyOneReducible_refl p) hp

/-- Halting on input `0` does not reduce to a decidable predicate. -/
example (q : ℕ → Prop) (hq : TM2Decidable q) :
    ¬ManyOneReducible (fun c : Code ↦ (c.eval 0).Dom) q :=
  fun hr ↦ not_tm2Decidable_halting 0 (tm2Decidable_of_manyOneReducible hr hq)

end CSLibExtTest.Computability.Decidability.Undecidable
