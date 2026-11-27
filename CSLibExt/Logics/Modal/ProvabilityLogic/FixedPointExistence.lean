/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ProvabilityLogic.FixedPoint

/-!
# Existence of fixed points in GL

`Cslib.Modal.fixedPoint_GL` proves the de Jongh–Sambin theorem by treating the outermost boxes
as a finite system of equations and eliminating one unknown at a time.
-/

@[expose] public section

namespace Cslib.Modal
namespace FixedPointExistence

variable {α β γ : Type*}

/-- Simultaneously substitute a formula for each atom. -/
private def inst (σ : α → Formula β) : Formula α → Formula β
  | .atom a => σ a
  | .bot => .bot
  | .imp A B => .imp (inst σ A) (inst σ B)
  | .box A => .box (inst σ A)

private theorem inst_comp (τ : β → Formula γ) (σ : α → Formula β) (A : Formula α) :
    inst τ (inst σ A) = inst (fun i ↦ inst τ (σ i)) A := by
  induction A <;> simp_all [inst]

private theorem inst_congr {σ τ : α → Formula β} (A : Formula α)
    (h : ∀ i ∈ A.atoms, σ i = τ i) : inst σ A = inst τ A := by
  induction A with
  | atom i => exact h i rfl
  | bot => rfl
  | imp A B ihA ihB =>
    exact congrArg₂ Formula.imp (ihA fun i hi ↦ h i (Or.inl hi)) (ihB fun i hi ↦ h i (Or.inr hi))
  | box A ih => exact congrArg Formula.box (ih h)

private theorem atoms_inst_subset (σ : α → Formula β) (S : Set β) (h : ∀ i, (σ i).atoms ⊆ S)
    (A : Formula α) : (inst σ A).atoms ⊆ S := by
  induction A with
  | atom i => exact h i
  | bot => exact Set.empty_subset _
  | imp A B ihA ihB => exact Set.union_subset ihA ihB
  | box A ih => exact ih

private theorem subst_eq_inst [DecidableEq α] (p : α) (B A : Formula α) :
    A.subst p B = inst (fun q ↦ if q = p then B else .atom q) A := by
  induction A <;> simp_all [Formula.subst, inst]

private theorem inst_derivable (σ : α → Formula β) {A : Formula α} (h : Derivable Axioms.GL A) :
    Derivable Axioms.GL (inst σ A) := by
  induction h with
  | ax1 => exact .ax1 _ _
  | ax2 => exact .ax2 _ _ _
  | dne => exact .dne _
  | distrib => exact .distrib _ _
  | extra h =>
    obtain ⟨B, rfl⟩ := h
    exact .extra (Axioms.axiomLob_mem_GL (inst σ B))
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | nec _ ih => exact .nec ih

/-- Solve the equation for the box indexed by `i`, leaving the other variables as parameters.
The auxiliary atom `r` is the identity context in the one-box theorem. -/
private theorem diagonal [DecidableEq α] (i r : α) (hne : i ≠ r) (C : Formula α) :
    let D := Formula.box (C.subst i .top)
    Derivable Axioms.GL (D.iff (.box (C.subst i D))) := by
  have h := Derivable.fixedPoint_GL_of_box (B := .atom r) (C := C) (p := i) (r := r)
    (show i ∉ (Formula.atom r).atoms from hne)
  simpa only [Formula.subst, ↓reduceIte] using h

/-- Eliminate the finite set `s` of unknowns in equations `i ↔ □(C i)`. The parameter `r` lies
outside the system. The assignment on the parameters also bounds the atoms of the solution. -/
private theorem solve (r : α) (base : α → Formula β) (S : Set β)
    (hbase : ∀ i, (base i).atoms ⊆ S) (s : Finset α) (hr : r ∉ s) (C : α → Formula α) :
    ∃ σ : α → Formula β, (∀ i, (σ i).atoms ⊆ S) ∧ (∀ i ∉ s, σ i = base i) ∧
      ∀ i ∈ s, Derivable Axioms.GL ((σ i).iff (.box (inst σ (C i)))) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => exact ⟨base, hbase, by simp, by simp⟩
  | @insert i s hi ih =>
    have hne : i ≠ r := fun e ↦ hr (e ▸ Finset.mem_insert_self i s)
    let D := Formula.box ((C i).subst i .top)
    let replace (j : α) : Formula α := if j = i then D else .atom j
    -- Substitute the diagonal for i throughout the remaining equations before solving them.
    obtain ⟨τ, hτ, hparam, heq⟩ := ih (fun h ↦ hr (Finset.mem_insert_of_mem h))
      (fun j ↦ inst replace (C j))
    let σ (j : α) := inst τ (replace j)
    have σi : σ i = inst τ D := by simp [σ, replace]
    have σj {j : α} (hj : j ≠ i) : σ j = τ j := by simp [σ, replace, hj, inst]
    refine ⟨σ, fun j ↦ atoms_inst_subset τ S hτ _, ?_, ?_⟩
    · intro j hj
      rw [Finset.mem_insert, not_or] at hj
      exact (σj hj.1).trans (hparam j hj.2)
    · intro j hj
      rcases Finset.mem_insert.mp hj with e | hj
      · subst j
        rw [σi]
        have hd := inst_derivable τ (diagonal i r hne (C i))
        change Derivable Axioms.GL ((inst τ D).iff (.box (inst τ ((C i).subst i D)))) at hd
        rwa [subst_eq_inst, inst_comp] at hd
      · rw [σj (fun e ↦ hi (e ▸ hj))]
        simpa only [inst_comp, σ] using heq j hj

/-- Replace each outermost box by an unknown indexed by its contents. -/
private def skeleton : Formula α → Formula (α ⊕ Formula α)
  | .atom q => .atom (.inl q)
  | .bot => .bot
  | .imp B C => .imp (skeleton B) (skeleton C)
  | .box C => .atom (.inr C)

private def unknowns [DecidableEq α] : Formula α → Finset (α ⊕ Formula α)
  | .atom _ | .bot => ∅
  | .imp B C => unknowns B ∪ unknowns C
  | .box C => {.inr C}

private theorem parameter_notMem [DecidableEq α] (q : α) (A : Formula α) :
    Sum.inl q ∉ unknowns A := by
  induction A <;> simp_all [unknowns]

private theorem iff_self (A : Formula α) : Derivable Axioms.GL (A.iff A) :=
  Derivable.GL_of_K4 (derivable_K4_iff.mpr fun _ M _ w ↦ (M.satisfies_iff w A A).mpr Iff.rfl)

private theorem imp_congr_GL {A B A' B' : Formula α}
    (ha : Derivable Axioms.GL (A.iff A')) (hb : Derivable Axioms.GL (B.iff B')) :
    Derivable Axioms.GL ((A.imp B).iff (A'.imp B')) := by
  refine .mp (Derivable.mp_of_K ?_ ha) hb
  refine derivable_K_iff.mpr fun _ M w ↦ ?_
  simp only [KripkeModel.satisfies_imp, KripkeModel.satisfies_iff]
  exact imp_congr

/-- Reassemble the outer propositional connectives using the equations for their boxes. -/
private theorem assemble [DecidableEq α] (σ : α ⊕ Formula α → Formula α) (p : α)
    (H B : Formula α) (hm : B.Modalised p)
    (hbox : ∀ C, .inr C ∈ unknowns B → Derivable Axioms.GL
      ((σ (.inr C)).iff (.box (inst (fun q ↦ if q = p then H else σ (.inl q)) C)))) :
    Derivable Axioms.GL ((inst σ (skeleton B)).iff
      (inst (fun q ↦ if q = p then H else σ (.inl q)) B)) := by
  induction B with
  | atom q =>
    simpa [skeleton, inst, show q ≠ p from hm] using iff_self (σ (.inl q))
  | bot => exact iff_self .bot
  | imp B C ihB ihC =>
    exact imp_congr_GL (ihB hm.1 fun D hD ↦ hbox D (Finset.mem_union_left _ hD))
      (ihC hm.2 fun D hD ↦ hbox D (Finset.mem_union_right _ hD))
  | box C _ => exact hbox C (Finset.mem_singleton_self _)

end FixedPointExistence

open FixedPointExistence

universe u

variable {Atom : Type u}

/-- **The de Jongh–Sambin fixed point theorem.** If every occurrence of the atom `p` in `A` lies
under a box, there is a formula `H` in which `p` does not occur, all of whose atoms occur in `A`,
such that `GL ⊢ H ↔ A(H)` (de Jongh and Sambin, 1975; Verbrugge, "Provability logic", *Stanford
Encyclopedia of Philosophy*, current edition, §2.2). The fixed point is unique up to GL-provable
equivalence by the proved `Derivable.fixedPoint_unique_GL`; the case of one boxed occurrence is
the proved `Derivable.fixedPoint_GL_of_box`. -/
theorem fixedPoint_GL [DecidableEq Atom] {A : Formula Atom} {p : Atom}
    (hA : A.Modalised p) :
    ∃ H : Formula Atom, p ∉ H.atoms ∧ H.atoms ⊆ A.atoms ∧
      Derivable Axioms.GL (H.iff (A.subst p H)) := by
  classical
  let S := A.atoms \ {p}
  let base : Atom ⊕ Formula Atom → Formula Atom :=
    Sum.elim (fun q ↦ if q ∈ S then .atom q else .bot) (fun _ ↦ .bot)
  have hbase (i) : (base i).atoms ⊆ S := by
    cases i with
    | inl q =>
      dsimp [base]
      split <;> simp [Formula.atoms, *]
    | inr C => exact Set.empty_subset _
  -- A box with contents C must denote □C[ p := the value of the skeleton ].
  let replace (q : Atom) : Formula (Atom ⊕ Formula Atom) :=
    if q = p then skeleton A else .atom (.inl q)
  let body : Atom ⊕ Formula Atom → Formula (Atom ⊕ Formula Atom) :=
    Sum.elim (fun _ ↦ .bot) (inst replace)
  obtain ⟨σ, hσ, hparam, heq⟩ :=
    solve (.inl p) base S hbase (unknowns A) (parameter_notMem p A) body
  let H := inst σ (skeleton A)
  have hH := atoms_inst_subset σ S hσ (skeleton A)
  refine ⟨H, fun hp ↦ (hH hp).2 rfl, fun q hq ↦ (hH hq).1, ?_⟩
  have hval (q) : inst σ (replace q) = if q = p then H else σ (.inl q) := by
    by_cases h : q = p <;> simp [replace, h, H, inst]
  have h := assemble σ p H A hA fun C hC ↦ by
    simpa only [body, Sum.elim_inr, inst_comp, hval] using heq (.inr C) hC
  rw [subst_eq_inst]
  convert h using 2
  apply inst_congr
  intro q hq
  by_cases e : q = p
  · simp [e]
  · have hqS : q ∈ S := ⟨hq, e⟩
    simp [e, hparam _ (parameter_notMem q A), base, hqS]

end Cslib.Modal
