/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic

/-!
# Recoverability hierarchy: inclusion core

History classes characterized by predicates form an inclusion
chain whenever the characterizing properties do. This module
proves that abstract core of the recoverability hierarchy
(strict, ACA, RC classes), including properness from
separating histories. Concrete schedule classes are not
formalized here.
-/

@[expose] public section

/-- Recoverability hierarchy, abstract core of DPA-31:
history classes are sets of histories characterized by
predicates `Pst` (serializable/strict), `Paca`, `Prc` with
`Pst → Paca → Prc`. The classes then form the chain
`ST ⊆ ACA ⊆ RC`. -/
def HistClass {H : Type*} (P : H → Prop) : Set H := {h | P h}

theorem histClass_chain {H : Type*} {Pst Paca Prc : H → Prop}
    (h1 : ∀ h, Pst h → Paca h) (h2 : ∀ h, Paca h → Prc h) :
    HistClass Pst ⊆ HistClass Paca ∧ HistClass Paca ⊆ HistClass Prc := by
  constructor
  · intro h hh
    exact h1 h hh
  · intro h hh
    exact h2 h hh

/-- Strictness skeleton: separating histories make the
inclusions proper. The separating histories and their
properties are the concrete content supplied downstream. -/
theorem histClass_strict {H : Type*} {Pst Paca Prc : H → Prop}
    (h1 : ∀ h, Pst h → Paca h) (h2 : ∀ h, Paca h → Prc h)
    (w1 : H) (hw1 : Paca w1 ∧ ¬ Pst w1)
    (w2 : H) (hw2 : Prc w2 ∧ ¬ Paca w2) :
    HistClass Pst ⊂ HistClass Paca ∧ HistClass Paca ⊂ HistClass Prc := by
  constructor
  · refine Set.ssubset_iff_subset_ne.mpr ⟨fun h hh => h1 h hh, ?_⟩
    intro heq
    have hm : w1 ∈ HistClass Paca := hw1.1
    rw [← heq] at hm
    exact hw1.2 hm
  · refine Set.ssubset_iff_subset_ne.mpr ⟨fun h hh => h2 h hh, ?_⟩
    intro heq
    have hm : w2 ∈ HistClass Prc := hw2.1
    rw [← heq] at hm
    exact hw2.2 hm

#print axioms histClass_chain
#print axioms histClass_strict

end
