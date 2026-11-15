/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

/-!
# Growth function of a concept class

For a finite concept class `C` and finite sample `s`, this
module defines the induced labelings (`restrictions`) and
shattering, and proves the basic counting facts: at most
`2 ^ |s|` labelings are induced, and shattering is exactly
inducing all of them. The Sauer-Shelah polynomial bound is
not proved here.
-/

@[expose] public section

/-- The set of labelings a concept class `C` induces on a finite
sample `s`: restrictions of concepts to `s`, as functions on the
subtype. -/
noncomputable def restrictions {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (s : Finset X) :
    Finset (s → Bool) :=
  C.image (fun c x => c x)

/-- Shattering: every labeling of `s` is realized by `C`. -/
def Shatters {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (s : Finset X) : Prop :=
  restrictions C s = Finset.univ

/-- The growth function bound: at most `2 ^ |s|` labelings. -/
theorem restrictions_card_le {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (s : Finset X) :
    (restrictions C s).card ≤ 2 ^ s.card := by
  calc (restrictions C s).card ≤ Fintype.card (s → Bool) := Finset.card_le_univ _
    _ = 2 ^ s.card := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- Shattering is exactly realizing all `2 ^ |s|` labelings. -/
theorem shatters_iff_card {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (s : Finset X) :
    Shatters C s ↔ (restrictions C s).card = 2 ^ s.card := by
  unfold Shatters
  constructor
  · intro h
    rw [h, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  · intro h
    apply Finset.eq_univ_of_card
    rw [h, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

end
