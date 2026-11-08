/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Craig interpolation for classical propositional logic
-/
module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Completeness

/-!
# Craig interpolation for classical propositional logic

If `A → B` is a tautology, there is an *interpolant* `I`, built only from the
atoms that `A` and `B` share (and the constant `⊥`), such that `A → I` and
`I → B` are tautologies.  The interpolant here eliminates the atoms private to
`A` by Boolean quantification: `∃p. A` is `A[p := ⊤] ∨ A[p := ⊥]`.  Through
completeness of classical natural deduction (`derivableIn_cpl_iff`) the same
interpolant works for derivability in `CPL`.

As elsewhere in this directory, `⊥` is upstream CSLib's atom `.atom ⊥`, read as
false by the classical semantics; `⊤` is written `⊥ → ⊥`.

## Main definitions

- `Proposition.atoms A` : the finite set of atoms occurring in `A`.
- `Proposition.fixAtom p b A` : substitute the constant `⊤` (if `b`) or `⊥` for
  the atom `p`.
- `Proposition.elimAtom p A` : `A[p := ⊤] ∨ A[p := ⊥]`, the Boolean
  quantification `∃p. A`; `Proposition.elimAtoms ps A` iterates it.

## Main results

- `Proposition.evalBool_elimAtoms` : `elimAtoms ps A` is true under `v` iff `A`
  is true under some valuation that agrees with `v` off `ps`.
- `exists_interpolant` (semantic interpolation): if every valuation with `⊥`
  false that makes `A` true makes `B` true, an interpolant over the common
  atoms exists.
- `exists_interpolant_cpl` (syntactic interpolation): if `CPL` derives `A → B`,
  there is `I` over the common atoms with `CPL` deriving `A → I` and `I → B`.

## References

- W. Craig, *Three uses of the Herbrand-Gentzen theorem in relating model
  theory and proof theory*, J. Symbolic Logic 22(3), 1957, 269-285.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem

variable {Atom : Type u} [DecidableEq Atom]

namespace Proposition

/-- The atoms occurring in a proposition. -/
def atoms : Proposition Atom → Finset Atom
  | atom x => {x}
  | and A B => A.atoms ∪ B.atoms
  | or A B => A.atoms ∪ B.atoms
  | imp A B => A.atoms ∪ B.atoms

/-- The truth value of `A` depends only on the valuation of its atoms. -/
theorem evalBool_congr {A : Proposition Atom} {v w : Atom → Bool}
    (h : ∀ x ∈ A.atoms, v x = w x) : A.evalBool v = A.evalBool w := by
  induction A with
  | atom x => exact h x (by simp [atoms])
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [atoms, Finset.mem_union] at h
    simp only [evalBool, ihA fun x hx ↦ h x (Or.inl hx), ihB fun x hx ↦ h x (Or.inr hx)]

variable [Bot Atom]

/-- Substitute the constant `⊤` (written `⊥ → ⊥`) if `b`, or `⊥` otherwise, for the atom
`p`. -/
def fixAtom (p : Atom) (b : Bool) : Proposition Atom → Proposition Atom
  | atom x => if x = p then (if b then (⊥ → ⊥ : Proposition Atom) else ⊥) else atom x
  | and A B => and (fixAtom p b A) (fixAtom p b B)
  | or A B => or (fixAtom p b A) (fixAtom p b B)
  | imp A B => imp (fixAtom p b A) (fixAtom p b B)

theorem evalBool_fixAtom (p : Atom) (b : Bool) (A : Proposition Atom)
    {v : Atom → Bool} (hv : v ⊥ = false) :
    (A.fixAtom p b).evalBool v = A.evalBool (Function.update v p b) := by
  induction A with
  | atom x =>
    by_cases hx : x = p
    · subst hx
      cases b <;> simp [fixAtom, hv]
    · simp [fixAtom, hx]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB => simp [fixAtom, evalBool, ihA, ihB]

theorem atoms_fixAtom_subset (p : Atom) (b : Bool) (A : Proposition Atom) :
    (A.fixAtom p b).atoms ⊆ insert ⊥ (A.atoms.erase p) := by
  induction A with
  | atom x =>
    by_cases hx : x = p
    · subst hx
      intro y hy
      cases b
      · simp [fixAtom, atoms] at hy
        simp [hy]
      · simp only [fixAtom, ite_true] at hy
        change y ∈ ({⊥} ∪ {⊥} : Finset Atom) at hy
        simp only [Finset.union_idempotent, Finset.mem_singleton] at hy
        simp [hy]
    · simp [fixAtom, atoms, hx]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [fixAtom, atoms]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have := ihA hx
      simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_union] at this ⊢
      tauto
    · have := ihB hx
      simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_union] at this ⊢
      tauto

/-- Boolean quantification over the atom `p`: `∃p. A` is `A[p := ⊤] ∨ A[p := ⊥]`. -/
def elimAtom (p : Atom) (A : Proposition Atom) : Proposition Atom :=
  or (A.fixAtom p true) (A.fixAtom p false)

theorem evalBool_elimAtom (p : Atom) (A : Proposition Atom) {v : Atom → Bool}
    (hv : v ⊥ = false) :
    (A.elimAtom p).evalBool v = true ↔ ∃ b, A.evalBool (Function.update v p b) = true := by
  simp only [elimAtom, evalBool, evalBool_fixAtom _ _ _ hv, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h

/-- Eliminate a list of atoms one after another. -/
def elimAtoms : List Atom → Proposition Atom → Proposition Atom
  | [], A => A
  | p :: ps, A => (elimAtoms ps A).elimAtom p

/-- `elimAtoms ps A` holds iff `A` holds after changing the valuation on `ps` only. -/
theorem evalBool_elimAtoms {ps : List Atom} (hps : ⊥ ∉ ps) (A : Proposition Atom)
    {v : Atom → Bool} (hv : v ⊥ = false) :
    (elimAtoms ps A).evalBool v = true ↔
      ∃ w : Atom → Bool, (∀ x, x ∉ ps → w x = v x) ∧ A.evalBool w = true := by
  induction ps generalizing v with
  | nil =>
    simp only [elimAtoms, List.not_mem_nil, not_false_eq_true, forall_const]
    exact ⟨fun h ↦ ⟨v, fun _ ↦ rfl, h⟩, fun ⟨w, hw, h⟩ ↦ funext hw ▸ h⟩
  | cons p ps ih =>
    have hp : p ≠ ⊥ := fun h ↦ hps (h ▸ List.mem_cons_self ..)
    have hps' : ⊥ ∉ ps := fun h ↦ hps (List.mem_cons_of_mem _ h)
    rw [elimAtoms, evalBool_elimAtom _ _ hv]
    constructor
    · rintro ⟨b, hb⟩
      have hv' : Function.update v p b ⊥ = false := by
        rw [Function.update_of_ne (Ne.symm hp), hv]
      obtain ⟨w, hw, hA⟩ := (ih hps' hv').mp hb
      refine ⟨w, fun x hx ↦ ?_, hA⟩
      rw [hw x fun h ↦ hx (List.mem_cons_of_mem _ h),
        Function.update_of_ne fun h ↦ hx (by simp [h])]
    · rintro ⟨w, hw, hA⟩
      refine ⟨w p, (ih hps' (by rw [Function.update_of_ne (Ne.symm hp), hv])).mpr
        ⟨w, fun x hx ↦ ?_, hA⟩⟩
      by_cases hxp : x = p
      · subst hxp
        simp
      · rw [Function.update_of_ne hxp]
        exact hw x (by simp [hxp, hx])

theorem atoms_elimAtoms_subset (ps : List Atom) (A : Proposition Atom) :
    (elimAtoms ps A).atoms ⊆ insert ⊥ (A.atoms.filter (· ∉ ps)) := by
  induction ps with
  | nil => exact fun x hx ↦ Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx, by simp⟩)
  | cons p ps ih =>
    intro x hx
    simp only [elimAtoms, elimAtom, atoms, Finset.mem_union] at hx
    have hx' : x ∈ insert ⊥ ((elimAtoms ps A).atoms.erase p) := by
      rcases hx with hx | hx
      · exact atoms_fixAtom_subset p true _ hx
      · exact atoms_fixAtom_subset p false _ hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx'
    rcases hx' with rfl | ⟨hxp, hx'⟩
    · exact Finset.mem_insert_self _ _
    · have := ih hx'
      simp only [Finset.mem_insert, Finset.mem_filter, List.mem_cons, not_or] at this ⊢
      tauto

end Proposition

/-! ### Interpolation -/

variable [Bot Atom]

/-- **Craig interpolation** (semantic form): if every valuation with `⊥` false that makes
`A` true makes `B` true, there is `I` whose atoms are common to `A` and `B` (or `⊥`) with
`A ⊨ I` and `I ⊨ B`. -/
theorem exists_interpolant {A B : Proposition Atom}
    (h : ∀ v : Atom → Bool, v ⊥ = false → A.evalBool v = true → B.evalBool v = true) :
    ∃ I : Proposition Atom, I.atoms ⊆ insert ⊥ (A.atoms ∩ B.atoms) ∧
      (∀ v : Atom → Bool, v ⊥ = false → A.evalBool v = true → I.evalBool v = true) ∧
      (∀ v : Atom → Bool, v ⊥ = false → I.evalBool v = true → B.evalBool v = true) := by
  -- eliminate the atoms of `A` that are not atoms of `B` (other than `⊥`)
  let ps := ((A.atoms \ B.atoms).erase ⊥).toList
  have hps : ⊥ ∉ ps := by simp [ps]
  have hmem : ∀ x, x ∈ ps ↔ x ∈ A.atoms ∧ x ∉ B.atoms ∧ x ≠ ⊥ := fun x ↦ by
    simp [ps, and_comm, and_left_comm]
  refine ⟨elimAtoms ps A, fun x hx ↦ ?_, fun v hv hA ↦ ?_, fun v hv hI ↦ ?_⟩
  · have := atoms_elimAtoms_subset ps A hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_inter, hmem] at this ⊢
    tauto
  · exact (evalBool_elimAtoms hps A hv).mpr ⟨v, fun _ _ ↦ rfl, hA⟩
  · obtain ⟨w, hw, hA⟩ := (evalBool_elimAtoms hps A hv).mp hI
    have hwbot : w ⊥ = false := by rw [hw ⊥ hps, hv]
    rw [← h w hwbot hA]
    exact evalBool_congr fun x hx ↦ (hw x fun hxp ↦ ((hmem x).mp hxp).2.1 hx).symm

/-- **Craig interpolation** for classical natural deduction: if `CPL` derives `A → B`, there
is `I` over the atoms common to `A` and `B` (and `⊥`) with `CPL` deriving `A → I` and
`I → B`. -/
theorem exists_interpolant_cpl {A B : Proposition Atom}
    (h : DerivableIn (CPL Atom) (A → B : Proposition Atom)) :
    ∃ I : Proposition Atom, I.atoms ⊆ insert ⊥ (A.atoms ∩ B.atoms) ∧
      DerivableIn (CPL Atom) (A → I : Proposition Atom) ∧
      DerivableIn (CPL Atom) (I → B : Proposition Atom) := by
  rw [DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff] at h
  obtain ⟨I, hI, hAI, hIB⟩ := exists_interpolant (A := A) (B := B) fun v hv hA ↦ by
    have := h v hv (by simp)
    simpa [hA] using this
  refine ⟨I, hI, ?_, ?_⟩
  · rw [DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff]
    intro v hv _
    cases hA : A.evalBool v
    · simp [hA]
    · simp [hAI v hv hA]
  · rw [DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff]
    intro v hv _
    cases hIv : I.evalBool v
    · simp [hIv]
    · simp [hIB v hv hIv]

end Cslib.Logic.PL
