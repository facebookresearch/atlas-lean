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
# Nonidentity tuples under permutation interleaving

Let G be any type with distinguished element 1.
For tuples a of length p, b of length q, and a permutation σ of p+q
positions, interleaving is their concatenation precomposed by σ⁻¹.
It has no identity entry exactly when neither input tuple has one.

Thus an identity-containing input remains degenerate after every
permutation interleaving, while two nonidentity tuples give a tuple
in N_(p+q). No group operation is required.
-/

@[expose] public section

namespace Rep.NormalizedBar

universe v

variable {G : Type v} [One G]

/-- For a type G with distinguished element 1, tuples a:G^p,b:G^q
and permutation σ of p+q positions, interleave(a,b,σ) is the
concatenation (a,b) evaluated at σ⁻¹(i) in output position i. -/
def interleave {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) : Fin (p + q) → G :=
  Fin.addCases a b ∘ σ.symm

/-- For a type G with distinguished element 1 and any permutation
σ, interleave(a,b,σ) has no identity entries exactly when both a
and b have no identity entries. -/
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

/-- For a type G with distinguished element 1, if a has an
identity entry, every permutation interleaving of a with any b
also has an identity entry. -/
theorem interleave_degenerate_left {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) (ha : ¬ IsNondegenerate G a) :
    ¬ IsNondegenerate G (interleave a b σ) :=
  fun h => ha ((isNondegenerate_interleave_iff a b σ).mp h).1

theorem interleave_degenerate_right {p q : ℕ} (a : Fin p → G) (b : Fin q → G)
    (σ : Equiv.Perm (Fin (p + q))) (hb : ¬ IsNondegenerate G b) :
    ¬ IsNondegenerate G (interleave a b σ) :=
  fun h => hb ((isNondegenerate_interleave_iff a b σ).mp h).2

/-- For a type G with distinguished element 1, two nonidentity
tuples a∈N_p,b∈N_q and any permutation σ give the nonidentity
tuple interleave(a,b,σ)∈N_(p+q). -/
def interleaveTuple {p q : ℕ} (a : Tuple G p) (b : Tuple G q)
    (σ : Equiv.Perm (Fin (p + q))) : Tuple G (p + q) :=
  ⟨interleave a.val b.val σ,
    (isNondegenerate_interleave_iff a.val b.val σ).mpr ⟨a.property, b.property⟩⟩

@[simp]
theorem interleaveTuple_val {p q : ℕ} (a : Tuple G p) (b : Tuple G q)
    (σ : Equiv.Perm (Fin (p + q))) :
    (interleaveTuple a b σ).val = interleave a.val b.val σ := rfl

end Rep.NormalizedBar
