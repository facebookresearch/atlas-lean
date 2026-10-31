/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modified for Atlas by Meta Platforms, Inc.: ported exact last-occurrence variable compaction and
support model counts to the canonical CSLib CNF representation.
-/
module

public import MathlibExt.Data.Fintype.PrescribedFunctions
public import Mathlib.SetTheory.Cardinal.Finite
public import CSLibExt.Logics.Propositional.CNF.Restriction

/-! # Exact variable compaction for conjunctive normal form

This file renames the variables occurring in a canonical CNF to a dense initial range. The
renaming follows the source algorithm exactly: variables are deduplicated in last-occurrence
order, then replaced by their `List.idxOf` positions.

Adapted from `eth/proof/variables/VariableBound/Paper/Rename/{Defs,Math}.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNF

/-- The number of Boolean assignments to the variables occurring in a formula that satisfy it. -/
def modelCount (formula : CNF) : Nat :=
  letI (assignment : {x // x ∈ formula.vars} → Bool) : Decidable
      (formula.Satisfies fun x => if h : x ∈ formula.vars then assignment ⟨x, h⟩ else false) := by
    unfold Satisfies CNFClause.Satisfies CNFLiteral.Satisfies
    infer_instance
  (Finset.univ.filter fun assignment : {x // x ∈ formula.vars} → Bool =>
    formula.Satisfies fun x => if h : x ∈ formula.vars then assignment ⟨x, h⟩ else false).card

@[simp]
theorem modelCount_nil : modelCount [] = 1 := by
  classical
  simp [modelCount]

/-- Rename every occurring variable by its position in the last-occurrence list. -/
def compact (formula : CNF) : CNF :=
  let names := (formula.flatMap fun clause => clause.map Prod.fst).dedup
  formula.map fun clause => clause.map fun literal => (names.idxOf literal.1, literal.2)

/-- Compaction preserves the number of clauses. -/
@[simp]
theorem length_compact (formula : CNF) : formula.compact.length = formula.length := by
  simp [compact]

/-- Compaction preserves every clause length, in the original clause order. -/
theorem clauseLengths_compact (formula : CNF) :
    formula.compact.map List.length = formula.map List.length := by
  simp [compact]

/-- Compaction preserves every upper bound on clause length. -/
theorem boundedClauseLength_compact_iff (formula : CNF) (k : Nat) :
    (∀ clause ∈ formula.compact, clause.length ≤ k) ↔
      ∀ clause ∈ formula, clause.length ≤ k := by
  simp [compact]

/-- Compaction preserves the absence of duplicate clauses. -/
theorem nodup_compact_iff (formula : CNF) :
    formula.compact.Nodup ↔ formula.Nodup := by
  let L := (formula.flatMap fun clause => clause.map Prod.fst).dedup
  let rename := fun literal : Nat × Bool => (L.idxOf literal.1, literal.2)
  change (formula.map fun clause => clause.map rename).Nodup ↔ formula.Nodup
  have hmem (x : Nat) : x ∈ L ↔ x ∈ formula.vars := by
    simp [L, CNF.mem_vars]
  have mapBack (clause : CNFClause) (hclause : clause ∈ formula) :
      (clause.map rename).map (fun literal => (L.getD literal.1 0, literal.2)) = clause := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id clause]
    refine List.map_congr_left fun literal hliteral => ?_
    have hlt : L.idxOf literal.1 < L.length := List.idxOf_lt_length_iff.mpr
      (hmem literal.1 |>.mpr <| CNF.mem_vars.mpr
        ⟨clause, hclause, literal.2, hliteral⟩)
    simp [rename, List.getElem?_eq_getElem hlt]
  constructor
  · exact List.Nodup.of_map _
  · intro hnodup
    refine hnodup.map_on fun clause hclause other hother heq => ?_
    rw [← mapBack clause hclause, ← mapBack other hother, heq]

/-- The variables of a compacted formula are exactly its dense initial range. -/
theorem vars_compact (formula : CNF) :
    formula.compact.vars = Finset.range formula.vars.card := by
  let L := (formula.flatMap fun clause => clause.map Prod.fst).dedup
  have hmem (x : Nat) : x ∈ L ↔ x ∈ formula.vars := by
    simp [L, CNF.mem_vars]
  have hnodup : L.Nodup := by
    dsimp [L]
    exact List.nodup_dedup _
  have htoFinset : L.toFinset = formula.vars := by
    ext x
    simp [hmem]
  have hlength : L.length = formula.vars.card := by
    rw [← htoFinset]
    exact (List.toFinset_card_of_nodup hnodup).symm
  ext j
  rw [Finset.mem_range]
  constructor
  · intro hj
    obtain ⟨clause, hclause, polarity, hliteral⟩ := CNF.mem_vars.mp hj
    obtain ⟨sourceClause, hsourceClause, rfl⟩ := List.mem_map.mp hclause
    obtain ⟨literal, hliteral, heq⟩ := List.mem_map.mp hliteral
    rw [Prod.mk.injEq] at heq
    rw [← heq.1, ← hlength]
    exact List.idxOf_lt_length_iff.mpr
      (hmem literal.1 |>.mpr <| CNF.mem_vars.mpr
        ⟨sourceClause, hsourceClause, literal.2, hliteral⟩)
  · intro hj
    have hjL : j < L.length := by simpa [hlength] using hj
    let x := L[j]
    have hxL : x ∈ L := List.getElem_mem hjL
    obtain ⟨sourceClause, hsourceClause, polarity, hliteral⟩ :=
      CNF.mem_vars.mp (hmem x |>.mp hxL)
    apply CNF.mem_vars.mpr
    refine ⟨sourceClause.map fun literal => (L.idxOf literal.1, literal.2), ?_, polarity, ?_⟩
    · simpa [compact, L] using List.mem_map_of_mem
        (f := fun clause => clause.map fun literal => (L.idxOf literal.1, literal.2))
        hsourceClause
    · apply List.mem_map.mpr
      refine ⟨(x, polarity), hliteral, Prod.ext ?_ rfl⟩
      exact hnodup.idxOf_getElem j hjL

/-- Satisfaction after compaction is satisfaction before compaction with names translated by
their exact last-occurrence positions. -/
theorem satisfies_compact_iff (formula : CNF) (assignment : Nat → Bool) :
    formula.compact.Satisfies assignment ↔
      formula.Satisfies fun x =>
        assignment ((formula.flatMap fun C => C.map Prod.fst).dedup.idxOf x) := by
  let rename := fun literal : Nat × Bool =>
    ((formula.flatMap fun C => C.map Prod.fst).dedup.idxOf literal.1, literal.2)
  change CNF.Satisfies assignment (formula.map fun clause => clause.map rename) ↔ _
  constructor
  · intro hsatisfies clause hclause
    obtain ⟨renamed, hrenamed, heq⟩ := hsatisfies (clause.map rename)
      (List.mem_map_of_mem hclause)
    obtain ⟨literal, hliteral, rfl⟩ := List.mem_map.mp hrenamed
    exact ⟨literal, hliteral, heq⟩
  · intro hsatisfies renamedClause hrenamedClause
    obtain ⟨clause, hclause, rfl⟩ := List.mem_map.mp hrenamedClause
    obtain ⟨literal, hliteral, heq⟩ := hsatisfies clause hclause
    exact ⟨rename literal, List.mem_map_of_mem hliteral, heq⟩

/-- Exact variable compaction preserves the number of assignments to the occurring variables. -/
theorem modelCount_compact (formula : CNF) :
    formula.compact.modelCount = formula.modelCount := by
  classical
  let L := (formula.flatMap fun clause => clause.map Prod.fst).dedup
  have hmem (x : Nat) : x ∈ L ↔ x ∈ formula.vars := by
    simp [L, CNF.mem_vars]
  have hnodup : L.Nodup := by
    dsimp [L]
    exact List.nodup_dedup _
  have htoFinset : L.toFinset = formula.vars := by
    ext x
    simp [hmem]
  have hlength : L.length = formula.vars.card := by
    rw [← htoFinset]
    exact (List.toFinset_card_of_nodup hnodup).symm
  let pos0 : {x // x ∈ formula.vars} → Fin formula.vars.card := fun x =>
    ⟨L.idxOf x.1, by
      rw [← hlength]
      exact List.idxOf_lt_length_iff.mpr (hmem x.1 |>.mpr x.2)⟩
  have hpos0 : Function.Bijective pos0 := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact (List.idxOf_inj (hmem x.1 |>.mpr x.2)).mp (congrArg Fin.val hxy)
    · intro j
      have hj : j.1 < L.length := by simp [hlength]
      let x := L[j.1]
      refine ⟨⟨x, hmem x |>.mp (List.getElem_mem hj)⟩, Fin.ext ?_⟩
      exact hnodup.idxOf_getElem j.1 hj
  let pos : {x // x ∈ formula.vars} ≃ Fin formula.vars.card :=
    Equiv.ofBijective pos0 hpos0
  let dense : {x // x ∈ formula.compact.vars} ≃ Fin formula.vars.card :=
    { toFun := fun x =>
        ⟨x.1, Finset.mem_range.mp (by simpa [vars_compact] using x.2)⟩
      invFun := fun j =>
        ⟨j.1, by simp [vars_compact]⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Fin.ext rfl }
  let supportEquiv : {x // x ∈ formula.vars} ≃ {x // x ∈ formula.compact.vars} :=
    pos.trans dense.symm
  let assignmentEquiv :
      ({x // x ∈ formula.vars} → Bool) ≃ ({x // x ∈ formula.compact.vars} → Bool) :=
    Equiv.arrowCongr supportEquiv (Equiv.refl Bool)
  have hassignment (a : {x // x ∈ formula.vars} → Bool) :
      formula.Satisfies (fun x => if h : x ∈ formula.vars then a ⟨x, h⟩ else false) ↔
        formula.compact.Satisfies (fun x => if h : x ∈ formula.compact.vars then
          assignmentEquiv a ⟨x, h⟩ else false) := by
    rw [satisfies_compact_iff]
    apply iff_of_eq
    apply propext
    apply CNF.satisfies_def.trans
    rw [CNF.satisfies_def]
    apply forall₂_congr
    intro clause hclause
    apply exists_congr
    intro literal
    apply and_congr_right
    intro hliteral
    have hx : literal.1 ∈ formula.vars :=
      CNF.mem_vars.mpr ⟨clause, hclause, literal.2, hliteral⟩
    have hidx : L.idxOf literal.1 ∈ formula.compact.vars := by
      rw [vars_compact]
      exact Finset.mem_range.mpr (by
        rw [← hlength]
        exact List.idxOf_lt_length_iff.mpr (hmem literal.1 |>.mpr hx))
    simp only [L] at hidx ⊢
    rw [CNFLiteral.satisfies_def, CNFLiteral.satisfies_def]
    simp only [hx, hidx, dite_true]
    have heqSupport : supportEquiv ⟨literal.1, hx⟩ =
        ⟨(formula.flatMap fun C => C.map Prod.fst).dedup.idxOf literal.1, hidx⟩ := by
      apply Subtype.ext
      rfl
    rw [← heqSupport]
    simp [assignmentEquiv]
  rw [modelCount, modelCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (assignmentEquiv.symm.subtypeEquiv fun a => by
      simpa using (hassignment (assignmentEquiv.symm a)).symm)

/-- If every occurring name is below `N`, the count over all `Fin N` assignments is the support
count times one Boolean choice for each unused ambient variable. -/
theorem card_satisfying_fin (formula : CNF) (N : Nat)
    (hvars : ∀ x ∈ formula.vars, x < N) :
    Nat.card {assignment : Fin N → Bool //
      formula.Satisfies fun x => if h : x < N then assignment ⟨x, h⟩ else false} =
      2 ^ (N - formula.vars.card) * formula.modelCount := by
  classical
  let occurs : Fin N → Prop := fun i => i.1 ∈ formula.vars
  let supportEquiv : {x // x ∈ formula.vars} ≃ {i : Fin N // occurs i} :=
    { toFun := fun x => ⟨⟨x.1, hvars x.1 x.2⟩, x.2⟩
      invFun := fun i => ⟨i.1.1, i.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Fin.ext rfl) }
  let firstEquiv : ({i : Fin N // occurs i} → Bool) ≃
      ({x // x ∈ formula.vars} → Bool) :=
    (Equiv.arrowCongr supportEquiv (Equiv.refl Bool)).symm
  let split : (Fin N → Bool) ≃
      ({x // x ∈ formula.vars} → Bool) × ({i : Fin N // ¬occurs i} → Bool) :=
    (Equiv.piEquivPiSubtypeProd occurs fun _ => Bool).trans
      (Equiv.prodCongr firstEquiv (Equiv.refl _))
  have hpredicate (assignment : Fin N → Bool) :
      formula.Satisfies (fun x => if h : x < N then assignment ⟨x, h⟩ else false) ↔
        formula.Satisfies (fun x => if h : x ∈ formula.vars then
          (split assignment).1 ⟨x, h⟩ else false) := by
    constructor
    · apply CNF.satisfies_congr
      intro x hx
      simp only [hvars x hx, hx, dite_true]
      rfl
    · apply CNF.satisfies_congr
      intro x hx
      simp only [hx, hvars x hx, dite_true]
      rfl
  rw [modelCount, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have e :
      {assignment : Fin N → Bool //
        formula.Satisfies fun x => if h : x < N then assignment ⟨x, h⟩ else false} ≃
      {assignment : {x // x ∈ formula.vars} → Bool //
        formula.Satisfies fun x => if h : x ∈ formula.vars then assignment ⟨x, h⟩ else false} ×
        ({i : Fin N // ¬occurs i} → Bool) :=
    (split.subtypeEquiv hpredicate).trans Equiv.prodSubtypeFstEquivSubtypeProd
  have hfree : Nat.card {i : Fin N // ¬occurs i} = N - formula.vars.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
    congr 2
    calc
      Fintype.card {i : Fin N // occurs i} = Fintype.card {x // x ∈ formula.vars} :=
        Fintype.card_congr supportEquiv.symm
      _ = formula.vars.card := Fintype.card_coe _
  have hfreeAssignments : Nat.card ({i : Fin N // ¬occurs i} → Bool) =
      2 ^ (N - formula.vars.card) := by
    have hfreeFintype : Fintype.card {i : Fin N // ¬occurs i} =
        N - formula.vars.card := by
      simpa [Nat.card_eq_fintype_card] using hfree
    rw [Nat.card_eq_fintype_card]
    convert Fintype.card_filter_univ_eqOn
      (∅ : Finset {i : Fin N // ¬occurs i}) (fun _ => false) using 1 <;>
      simp [hfreeFintype]
  rw [Nat.card_congr e, Nat.card_prod, hfreeAssignments, mul_comm]

end CNF

end Cslib.Logic.PL
