/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.Basic
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleIndex

/-!
# Nonidentity group-bar tuples under shuffle interleaving

The tuple interleaving used by the existing shuffle operator has no identity
entry precisely when neither input tuple has an identity entry. This needs
only a distinguished identity element and an actual permutation; the shared
Eilenberg–Zilber shuffle predicate is reused.
-/

@[expose] public section

namespace Rep.NormalizedBar

universe v

variable {G : Type v} [One G]

/-- The actual tuple interleaving in the group-bar shuffle formula. -/
def interleave {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) : Fin (p + q) → G :=
  Fin.addCases a b ∘ σ.symm

/-- A permutation interleaving preserves and reflects nonidentity entries. -/
theorem isNondegenerate_interleave_iff {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) :
    IsNondegenerate G (interleave a b σ) ↔
      IsNondegenerate G a ∧ IsNondegenerate G b := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [interleave, Function.comp_apply] using h (σ (Fin.castAdd q i))
    · intro j
      simpa [interleave, Function.comp_apply] using h (σ (Fin.natAdd p j))
  · rintro ⟨ha, hb⟩
    intro i
    change (Fin.addCases (motive := fun _ => G) a b) (σ.symm i) ≠ (1 : G)
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        (Fin.addCases (motive := fun _ => G) a b j) ≠ 1) ?_ ?_ (σ.symm i)
    · intro j
      simpa using ha j
    · intro j
      simpa using hb j

/-- Every interleaving of a tuple containing identity is degenerate. -/
theorem interleave_degenerate_left {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) (ha : ¬ IsNondegenerate G a) :
    ¬ IsNondegenerate G (interleave a b σ) :=
  fun h => ha ((isNondegenerate_interleave_iff a b σ).mp h).1

theorem interleave_degenerate_right {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) (hb : ¬ IsNondegenerate G b) :
    ¬ IsNondegenerate G (interleave a b σ) :=
  fun h => hb ((isNondegenerate_interleave_iff a b σ).mp h).2

/-- The literal nonidentity tuple obtained by interleaving two normalized generators. -/
def interleaveTuple {p q : ℕ} (a : Tuple G p) (b : Tuple G q)
    (σ : Equiv.Perm (Fin (p + q))) : Tuple G (p + q) :=
  ⟨interleave a.val b.val σ,
    (isNondegenerate_interleave_iff a.val b.val σ).mpr ⟨a.property, b.property⟩⟩

@[simp]
theorem interleaveTuple_val {p q : ℕ} (a : Tuple G p) (b : Tuple G q)
    (σ : Equiv.Perm (Fin (p + q))) :
    (interleaveTuple a b σ).val = interleave a.val b.val σ := rfl

end Rep.NormalizedBar
