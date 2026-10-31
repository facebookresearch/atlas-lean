/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modified for Atlas by Meta Platforms, Inc.: ported the source's unique-extension width
reduction to the canonical CSLib CNF representation and support model count.
-/
module

public import CSLibExt.Logics.Propositional.CNF.Compaction

/-! # Parsimonious reduction to clauses of width three

This file turns every canonical CNF clause into clauses of length at most three. Each step
replaces the first two literals of a long clause by a fresh variable and adds three clauses
forcing that variable to equal their disjunction. Thus every satisfying assignment has exactly
one extension across the allocated fresh-variable interval.

Adapted from `eth/proof/networks/Eight/Cor/{WidthDefs,Width}.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNF

/-- The number of fresh variables used by the parsimonious width-three reduction. -/
def numFreshParsimonious3 (formula : CNF) : Nat :=
  (formula.map fun clause => clause.length - 3).sum

/-- Reduce a CNF to clauses of length at most three, allocating fresh variables consecutively
from `start`. Repeated output clauses are removed in last-occurrence order. -/
def to3Parsimonious (formula : CNF) (start : Nat) : CNF :=
  (splitAll ((List.range formula.numFreshParsimonious3).map fun offset => start + offset)
    formula).dedup
where
  neg (literal : Nat × Bool) : Nat × Bool := (literal.1, !literal.2)
  forced (fresh : Nat) (first second : Nat × Bool) : CNF :=
    [[(fresh, false), first, second],
      [(fresh, true), neg first],
      [(fresh, true), neg second]]
  splitClause : List Nat → CNFClause → CNF
    | fresh :: rest, first :: second :: third :: fourth :: tail =>
        forced fresh first second ++
          splitClause rest ((fresh, true) :: third :: fourth :: tail)
    | _, clause => [clause]
  splitAll : List Nat → CNF → CNF
    | _, [] => []
    | fresh, clause :: rest =>
        splitClause (fresh.take (clause.length - 3)) clause ++
          splitAll (fresh.drop (clause.length - 3)) rest

local notation "neg" => to3Parsimonious.neg
local notation "forced" => to3Parsimonious.forced
local notation "splitClause" => to3Parsimonious.splitClause
local notation "splitAll" => to3Parsimonious.splitAll
private abbrev freshNames (start count : Nat) :=
  (List.range count).map fun offset => start + offset

private theorem to3Parsimonious_eq (formula : CNF) (start : Nat) :
    formula.to3Parsimonious start =
      (splitAll (freshNames start formula.numFreshParsimonious3) formula).dedup := rfl

private theorem satisfies_forced (assignment : Nat → Bool) (fresh : Nat)
    (first second : Nat × Bool) :
    (forced fresh first second).Satisfies assignment ↔
      (assignment fresh = true ↔
        assignment first.1 = first.2 ∨ assignment second.1 = second.2) := by
  obtain ⟨firstVar, firstPolarity⟩ := first
  obtain ⟨secondVar, secondPolarity⟩ := second
  unfold to3Parsimonious.forced to3Parsimonious.neg
  simp only [CNF.Satisfies, CNFClause.Satisfies, CNFLiteral.Satisfies,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq_left]
  generalize assignment fresh = freshValue
  generalize assignment firstVar = firstValue
  generalize assignment secondVar = secondValue
  cases freshValue <;> cases firstValue <;> cases secondValue <;>
    cases firstPolarity <;> cases secondPolarity <;> simp

private theorem splitClause_nil (clause : CNFClause) :
    splitClause [] clause = [clause] := by
  rw [to3Parsimonious.splitClause.eq_2]
  simp

private theorem splitClause_short (fresh : List Nat) {clause : CNFClause}
    (hclause : clause.length ≤ 3) : splitClause fresh clause = [clause] := by
  rw [to3Parsimonious.splitClause.eq_2]
  intro head tail first second third fourth rest hfresh hclauseEq
  subst fresh
  subst clause
  simp at hclause
  omega

private theorem exists_four {clause : CNFClause} (hclause : ¬ clause.length ≤ 3) :
    ∃ first second third fourth tail,
      clause = first :: second :: third :: fourth :: tail := by
  match clause, hclause with
  | first :: second :: third :: fourth :: tail, _ =>
      exact ⟨first, second, third, fourth, tail, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h => simp at h

private theorem splitClause_step (fresh : Nat) (rest : List Nat)
    (first second third fourth : Nat × Bool) (tail : CNFClause) :
    splitClause (fresh :: rest) (first :: second :: third :: fourth :: tail) =
      forced fresh first second ++
        splitClause rest ((fresh, true) :: third :: fourth :: tail) := rfl

private theorem splitClause_sound (assignment : Nat → Bool) :
    ∀ (fresh : List Nat) (clause : CNFClause),
      (splitClause fresh clause).Satisfies assignment → clause.Satisfies assignment
  | [], clause, hsatisfies => by
      rw [splitClause_nil] at hsatisfies
      exact hsatisfies clause (by simp)
  | fresh :: rest, clause, hsatisfies => by
      by_cases hclause : clause.length ≤ 3
      · rw [splitClause_short _ hclause] at hsatisfies
        exact hsatisfies clause (by simp)
      · obtain ⟨first, second, third, fourth, tail, rfl⟩ := exists_four hclause
        rw [splitClause_step, CNF.satisfies_append, satisfies_forced] at hsatisfies
        obtain ⟨literal, hliteral, heq⟩ := splitClause_sound assignment rest _ hsatisfies.2
        rcases List.mem_cons.mp hliteral with rfl | hliteral
        · rcases hsatisfies.1.mp heq with heq | heq
          · exact ⟨first, by simp, heq⟩
          · exact ⟨second, by simp, heq⟩
        · exact ⟨literal, by simp only [List.mem_cons] at hliteral ⊢; tauto, heq⟩

private theorem satisfies_congr_literals {first second : Nat → Bool} {formula : CNF}
    (hagrees : ∀ clause ∈ formula, ∀ literal ∈ clause,
      first literal.1 = second literal.1) :
    formula.Satisfies first ↔ formula.Satisfies second := by
  constructor
  · intro hsatisfies clause hclause
    obtain ⟨literal, hliteral, heq⟩ := hsatisfies clause hclause
    refine ⟨literal, hliteral, ?_⟩
    change second literal.1 = literal.2
    change first literal.1 = literal.2 at heq
    rw [← hagrees clause hclause literal hliteral]
    exact heq
  · intro hsatisfies clause hclause
    obtain ⟨literal, hliteral, heq⟩ := hsatisfies clause hclause
    refine ⟨literal, hliteral, ?_⟩
    change first literal.1 = literal.2
    change second literal.1 = literal.2 at heq
    rw [hagrees clause hclause literal hliteral]
    exact heq

private theorem splitClause_vars :
    ∀ (fresh : List Nat) (clause : CNFClause),
      ∀ output ∈ splitClause fresh clause, ∀ literal ∈ output,
        literal.1 ∈ fresh ∨ ∃ source ∈ clause, source.1 = literal.1
  | [], clause, output, houtput, literal, hliteral => by
      rw [splitClause_nil] at houtput
      obtain rfl : output = clause := by simpa using houtput
      exact Or.inr ⟨literal, hliteral, rfl⟩
  | head :: tail, clause, output, houtput, literal, hliteral => by
      by_cases hclause : clause.length ≤ 3
      · rw [splitClause_short _ hclause] at houtput
        obtain rfl : output = clause := by simpa using houtput
        exact Or.inr ⟨literal, hliteral, rfl⟩
      · obtain ⟨first, second, third, fourth, rest, rfl⟩ := exists_four hclause
        rw [splitClause_step, List.mem_append] at houtput
        rcases houtput with houtput | houtput
        · unfold to3Parsimonious.forced to3Parsimonious.neg at houtput
          simp only [List.mem_cons, List.not_mem_nil, or_false] at houtput
          rcases houtput with rfl | rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral <;>
            rcases hliteral with rfl | rfl | rfl <;> simp
        · rcases splitClause_vars tail _ output houtput literal hliteral with
            hfresh | ⟨source, hsource, heq⟩
          · exact Or.inl (List.mem_cons_of_mem _ hfresh)
          · rcases List.mem_cons.mp hsource with rfl | hsource
            · exact Or.inl (by simp [← heq])
            · exact Or.inr ⟨source, by
                simp only [List.mem_cons] at hsource ⊢
                tauto, heq⟩

private theorem splitClause_contains :
    ∀ (fresh : List Nat) (clause : CNFClause) (literal : Nat × Bool),
      literal ∈ clause → ∃ output ∈ splitClause fresh clause, literal ∈ output
  | [], clause, literal, hliteral => ⟨clause, by simp [splitClause_nil], hliteral⟩
  | head :: tail, clause, literal, hliteral => by
      by_cases hclause : clause.length ≤ 3
      · exact ⟨clause, by simp [splitClause_short _ hclause], hliteral⟩
      · obtain ⟨first, second, third, fourth, rest, rfl⟩ := exists_four hclause
        rcases List.mem_cons.mp hliteral with rfl | hliteral
        · refine ⟨[(head, false), literal, second], ?_, by simp⟩
          rw [splitClause_step, List.mem_append]
          left
          unfold to3Parsimonious.forced
          simp
        · rcases List.mem_cons.mp hliteral with rfl | hliteral
          · refine ⟨[(head, false), first, literal], ?_, by simp⟩
            rw [splitClause_step, List.mem_append]
            left
            unfold to3Parsimonious.forced
            simp
          · obtain ⟨output, houtput, hliteral⟩ :=
              splitClause_contains tail ((head, true) :: third :: fourth :: rest)
                literal (List.mem_cons_of_mem _ hliteral)
            exact ⟨output, by
              rw [splitClause_step, List.mem_append]
              exact Or.inr houtput, hliteral⟩

private theorem splitClause_extend :
    ∀ (fresh : List Nat) (clause : CNFClause) (assignment : Nat → Bool),
      fresh.Nodup → (∀ literal ∈ clause, literal.1 ∉ fresh) →
      clause.Satisfies assignment →
        ∃ extension : Nat → Bool,
          (∀ x, x ∉ fresh → extension x = assignment x) ∧
            (splitClause fresh clause).Satisfies extension
  | [], clause, assignment, _, _, hsatisfies =>
      ⟨assignment, fun _ _ => rfl, by
        rw [splitClause_nil]
        simpa [CNF.Satisfies] using hsatisfies⟩
  | head :: tail, clause, assignment, hnodup, hfresh, hsatisfies => by
      classical
      by_cases hclause : clause.length ≤ 3
      · exact ⟨assignment, fun _ _ => rfl, by
          rw [splitClause_short _ hclause]
          simpa [CNF.Satisfies] using hsatisfies⟩
      · obtain ⟨first, second, third, fourth, rest, rfl⟩ := exists_four hclause
        obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
        have hne : ∀ literal ∈ first :: second :: third :: fourth :: rest,
            literal.1 ≠ head := fun literal hliteral heq =>
          hfresh literal hliteral (by simp [heq])
        have hnotTail : ∀ literal ∈ first :: second :: third :: fourth :: rest,
            literal.1 ∉ tail := fun literal hliteral hmem =>
          hfresh literal hliteral (List.mem_cons_of_mem _ hmem)
        let updated : Nat → Bool := Function.update assignment head
          (decide (assignment first.1 = first.2 ∨ assignment second.1 = second.2))
        have hupdated : ∀ literal ∈ first :: second :: third :: fourth :: rest,
            updated literal.1 = assignment literal.1 := fun literal hliteral =>
          Function.update_of_ne (hne literal hliteral) _ _
        have hupdatedHead : updated head =
            decide (assignment first.1 = first.2 ∨ assignment second.1 = second.2) :=
          Function.update_self _ _ _
        obtain ⟨extension, hagrees, hextension⟩ := splitClause_extend tail
          ((head, true) :: third :: fourth :: rest) updated htail
          (by
            intro literal hliteral
            rcases List.mem_cons.mp hliteral with rfl | hliteral
            · exact hhead
            · exact hnotTail literal (by
                simp only [List.mem_cons] at hliteral ⊢
                tauto))
          (by
            obtain ⟨literal, hliteral, heq⟩ := hsatisfies
            by_cases hfirstSecond :
                assignment first.1 = first.2 ∨ assignment second.1 = second.2
            · exact ⟨(head, true), by simp, by simp [hupdatedHead, hfirstSecond]⟩
            · have hliteralRest : literal ∈ third :: fourth :: rest := by
                simp only [List.mem_cons] at hliteral ⊢
                rcases hliteral with rfl | rfl | hliteral
                · exact absurd (Or.inl heq) hfirstSecond
                · exact absurd (Or.inr heq) hfirstSecond
                · exact hliteral
              exact ⟨literal, List.mem_cons_of_mem _ hliteralRest, by
                change updated literal.1 = literal.2
                change assignment literal.1 = literal.2 at heq
                rw [hupdated literal hliteral]
                exact heq⟩)
        refine ⟨extension, fun x hx => ?_, ?_⟩
        · rw [hagrees x fun hmem => hx (List.mem_cons_of_mem _ hmem)]
          exact Function.update_of_ne (fun heq => hx (by simp [heq])) _ _
        · rw [splitClause_step, CNF.satisfies_append, satisfies_forced]
          refine ⟨?_, hextension⟩
          rw [hagrees head hhead,
            hagrees _ (hnotTail first (by simp)),
            hagrees _ (hnotTail second (by simp)),
            hupdated first (by simp), hupdated second (by simp), hupdatedHead]
          simp

private theorem splitClause_unique (first second : Nat → Bool) :
    ∀ (fresh : List Nat) (clause : CNFClause),
      fresh.length ≤ clause.length - 3 →
      (∀ literal ∈ clause, first literal.1 = second literal.1) →
      (splitClause fresh clause).Satisfies first →
      (splitClause fresh clause).Satisfies second →
      ∀ x ∈ fresh, first x = second x
  | [], _, _, _, _, _, x, hx => by simp at hx
  | head :: tail, clause, hlength, hagrees, hfirst, hsecond, x, hx => by
      have hclause : ¬ clause.length ≤ 3 := by
        simp at hlength
        omega
      obtain ⟨firstLiteral, secondLiteral, third, fourth, rest, rfl⟩ :=
        exists_four hclause
      rw [splitClause_step, CNF.satisfies_append, satisfies_forced] at hfirst hsecond
      have hhead : first head = second head := by
        have heq : (first head = true ↔ second head = true) := by
          rw [hfirst.1, hsecond.1,
            hagrees firstLiteral (by simp), hagrees secondLiteral (by simp)]
        cases hfirstValue : first head <;> cases hsecondValue : second head <;> simp_all
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hhead
      · refine splitClause_unique first second tail _ (by
            simp at hlength ⊢
            omega) ?_ hfirst.2 hsecond.2 x hx
        intro literal hliteral
        rcases List.mem_cons.mp hliteral with rfl | hliteral
        · exact hhead
        · exact hagrees literal (by
            simp only [List.mem_cons] at hliteral ⊢
            tauto)

private theorem splitClause_width :
    ∀ (fresh : List Nat) (clause : CNFClause), clause.length - 3 ≤ fresh.length →
      ∀ output ∈ splitClause fresh clause, output.length ≤ 3
  | [], clause, hlength, output, houtput => by
      rw [splitClause_nil] at houtput
      obtain rfl : output = clause := by simpa using houtput
      simp at hlength
      omega
  | head :: tail, clause, hlength, output, houtput => by
      by_cases hclause : clause.length ≤ 3
      · rw [splitClause_short _ hclause] at houtput
        obtain rfl : output = clause := by simpa using houtput
        exact hclause
      · obtain ⟨first, second, third, fourth, rest, rfl⟩ := exists_four hclause
        rw [splitClause_step, List.mem_append] at houtput
        rcases houtput with houtput | houtput
        · unfold to3Parsimonious.forced at houtput
          simp only [List.mem_cons, List.not_mem_nil, or_false] at houtput
          rcases houtput with rfl | rfl | rfl <;> simp
        · exact splitClause_width tail _ (by
            simp at hlength ⊢
            omega) output houtput

private theorem length_splitClause :
    ∀ (fresh : List Nat) (clause : CNFClause),
      (splitClause fresh clause).length =
        1 + 3 * min fresh.length (clause.length - 3)
  | [], clause => by
      rw [splitClause_nil]
      simp
  | head :: tail, clause => by
      by_cases hclause : clause.length ≤ 3
      · rw [splitClause_short _ hclause]
        simp
        omega
      · obtain ⟨first, second, third, fourth, rest, rfl⟩ := exists_four hclause
        rw [splitClause_step, List.length_append, length_splitClause tail]
        unfold to3Parsimonious.forced
        simp
        omega

private theorem splitAll_cons (fresh : List Nat) (clause : CNFClause) (formula : CNF) :
    splitAll fresh (clause :: formula) =
      splitClause (fresh.take (clause.length - 3)) clause ++
        splitAll (fresh.drop (clause.length - 3)) formula :=
  to3Parsimonious.splitAll.eq_2 fresh clause formula

private theorem numFreshParsimonious3_cons (clause : CNFClause) (formula : CNF) :
    numFreshParsimonious3 (clause :: formula) =
      (clause.length - 3) + numFreshParsimonious3 formula := by
  simp [numFreshParsimonious3]

private theorem splitAll_sound (assignment : Nat → Bool) :
    ∀ (formula : CNF) (fresh : List Nat),
      (splitAll fresh formula).Satisfies assignment → formula.Satisfies assignment
  | [], _, _ => CNF.satisfies_nil _
  | clause :: formula, fresh, hsatisfies => by
      rw [splitAll_cons, CNF.satisfies_append] at hsatisfies
      exact CNF.satisfies_cons.mpr
        ⟨splitClause_sound assignment _ clause hsatisfies.1,
          splitAll_sound assignment formula _ hsatisfies.2⟩

private theorem splitAll_vars :
    ∀ (formula : CNF) (fresh : List Nat),
      ∀ output ∈ splitAll fresh formula, ∀ literal ∈ output,
        literal.1 ∈ fresh ∨ ∃ sourceClause ∈ formula,
          ∃ sourceLiteral ∈ sourceClause, sourceLiteral.1 = literal.1
  | [], _, output, houtput, _, _ => by
      simp [to3Parsimonious.splitAll] at houtput
  | clause :: formula, fresh, output, houtput, literal, hliteral => by
      rw [splitAll_cons, List.mem_append] at houtput
      rcases houtput with houtput | houtput
      · rcases splitClause_vars _ clause output houtput literal hliteral with
          hfresh | ⟨source, hsource, heq⟩
        · exact Or.inl (List.mem_of_mem_take hfresh)
        · exact Or.inr ⟨clause, by simp, source, hsource, heq⟩
      · rcases splitAll_vars formula _ output houtput literal hliteral with
          hfresh | ⟨sourceClause, hclause, sourceLiteral, hliteral, heq⟩
        · exact Or.inl (List.mem_of_mem_drop hfresh)
        · exact Or.inr
            ⟨sourceClause, List.mem_cons_of_mem _ hclause, sourceLiteral, hliteral, heq⟩

private theorem splitAll_contains :
    ∀ (formula : CNF) (fresh : List Nat) (clause : CNFClause),
      clause ∈ formula → ∀ literal ∈ clause,
        ∃ output ∈ splitAll fresh formula, literal ∈ output
  | [], _, _, hclause, _, _ => by simp at hclause
  | first :: formula, fresh, clause, hclause, literal, hliteral => by
      rcases List.mem_cons.mp hclause with rfl | hclause
      · obtain ⟨output, houtput, hliteral⟩ :=
          splitClause_contains (fresh.take (clause.length - 3)) clause literal hliteral
        exact ⟨output, by
          rw [splitAll_cons, List.mem_append]
          exact Or.inl houtput, hliteral⟩
      · obtain ⟨output, houtput, hliteral⟩ :=
          splitAll_contains formula (fresh.drop (first.length - 3))
            clause hclause literal hliteral
        exact ⟨output, by
          rw [splitAll_cons, List.mem_append]
          exact Or.inr houtput, hliteral⟩

private theorem splitAll_extend :
    ∀ (formula : CNF) (fresh : List Nat) (assignment : Nat → Bool),
      fresh.Nodup →
      (∀ clause ∈ formula, ∀ literal ∈ clause, literal.1 ∉ fresh) →
      formula.Satisfies assignment →
        ∃ extension : Nat → Bool,
          (∀ x, x ∉ fresh → extension x = assignment x) ∧
            (splitAll fresh formula).Satisfies extension
  | [], _, assignment, _, _, _ => ⟨assignment, fun _ _ => rfl, CNF.satisfies_nil _⟩
  | clause :: formula, fresh, assignment, hnodup, hfresh, hsatisfies => by
      obtain ⟨hclause, hformula⟩ := CNF.satisfies_cons.mp hsatisfies
      have htake : (fresh.take (clause.length - 3)).Sublist fresh :=
        List.take_sublist _ _
      have hdrop : (fresh.drop (clause.length - 3)).Sublist fresh :=
        List.drop_sublist _ _
      obtain ⟨firstExtension, hfirstAgrees, hfirstSatisfies⟩ :=
        splitClause_extend (fresh.take (clause.length - 3)) clause assignment
          (hnodup.sublist htake)
          (fun literal hliteral hmem =>
            hfresh clause (by simp) literal hliteral (htake.subset hmem)) hclause
      have hformulaFirst : CNF.Satisfies firstExtension formula :=
        (satisfies_congr_literals fun source hsource literal hliteral =>
          hfirstAgrees literal.1 fun hmem =>
            hfresh source (List.mem_cons_of_mem _ hsource) literal hliteral
              (htake.subset hmem)).mpr hformula
      obtain ⟨extension, hextensionAgrees, hextensionSatisfies⟩ :=
        splitAll_extend formula (fresh.drop (clause.length - 3)) firstExtension
          (hnodup.sublist hdrop)
          (fun source hsource literal hliteral hmem =>
            hfresh source (List.mem_cons_of_mem _ hsource) literal hliteral
              (hdrop.subset hmem)) hformulaFirst
      refine ⟨extension, fun x hx => ?_, ?_⟩
      · rw [hextensionAgrees x fun hmem => hx (hdrop.subset hmem),
          hfirstAgrees x fun hmem => hx (htake.subset hmem)]
      · rw [splitAll_cons, CNF.satisfies_append]
        refine ⟨(satisfies_congr_literals fun output houtput literal hliteral =>
          hextensionAgrees literal.1 fun hdropMem => ?_).mpr hfirstSatisfies,
          hextensionSatisfies⟩
        rcases splitClause_vars _ clause output houtput literal hliteral with
          htakeMem | ⟨source, hsource, heq⟩
        · exact List.disjoint_take_drop hnodup le_rfl htakeMem hdropMem
        · exact hfresh clause (by simp) source hsource (heq ▸ hdrop.subset hdropMem)

private theorem splitAll_unique (first second : Nat → Bool) :
    ∀ (formula : CNF) (fresh : List Nat), fresh.length ≤ formula.numFreshParsimonious3 →
      (∀ clause ∈ formula, ∀ literal ∈ clause,
        first literal.1 = second literal.1) →
      (splitAll fresh formula).Satisfies first →
      (splitAll fresh formula).Satisfies second →
      ∀ x ∈ fresh, first x = second x
  | [], fresh, hlength, _, _, _, x, hx => by
      obtain rfl : fresh = [] := List.length_eq_zero_iff.mp (by
        simpa [numFreshParsimonious3] using hlength)
      simp at hx
  | clause :: formula, fresh, hlength, hagrees, hfirst, hsecond, x, hx => by
      rw [splitAll_cons, CNF.satisfies_append] at hfirst hsecond
      rw [numFreshParsimonious3_cons] at hlength
      rw [← List.take_append_drop (clause.length - 3) fresh, List.mem_append] at hx
      rcases hx with hx | hx
      · exact splitClause_unique first second _ clause (by simp)
          (hagrees clause (by simp)) hfirst.1 hsecond.1 x hx
      · exact splitAll_unique first second formula _ (by
          simp
          omega) (fun source hsource =>
            hagrees source (List.mem_cons_of_mem _ hsource)) hfirst.2 hsecond.2 x hx

private theorem splitAll_width :
    ∀ (formula : CNF) (fresh : List Nat), formula.numFreshParsimonious3 ≤ fresh.length →
      ∀ output ∈ splitAll fresh formula, output.length ≤ 3
  | [], _, _, output, houtput => by
      simp [to3Parsimonious.splitAll] at houtput
  | clause :: formula, fresh, hlength, output, houtput => by
      rw [numFreshParsimonious3_cons] at hlength
      rw [splitAll_cons, List.mem_append] at houtput
      rcases houtput with houtput | houtput
      · exact splitClause_width _ clause (by simp; omega) output houtput
      · exact splitAll_width formula _ (by simp; omega) output houtput

private theorem length_splitAll :
    ∀ (formula : CNF) (fresh : List Nat), formula.numFreshParsimonious3 ≤ fresh.length →
      (splitAll fresh formula).length = formula.length + 3 * formula.numFreshParsimonious3
  | [], _, _ => by
      simp [to3Parsimonious.splitAll, numFreshParsimonious3]
  | clause :: formula, fresh, hlength => by
      rw [numFreshParsimonious3_cons] at hlength
      rw [splitAll_cons, List.length_append, length_splitClause,
        length_splitAll formula _ (by simp; omega), numFreshParsimonious3_cons]
      simp
      omega

private theorem numFreshParsimonious3_le_aux (k : Nat) :
    ∀ formula : CNF, (∀ clause ∈ formula, clause.length ≤ k) →
      formula.numFreshParsimonious3 ≤ (k - 3) * formula.length
  | [], _ => by simp [numFreshParsimonious3]
  | clause :: formula, hbound => by
      have hclause := hbound clause (by simp)
      have hformula := numFreshParsimonious3_le_aux k formula fun source hsource =>
        hbound source (List.mem_cons_of_mem _ hsource)
      rw [numFreshParsimonious3_cons, List.length_cons, Nat.mul_succ]
      omega

private theorem length_freshNames (start count : Nat) :
    (freshNames start count).length = count := by
  simp [freshNames]

private theorem nodup_freshNames (start count : Nat) :
    (freshNames start count).Nodup := by
  unfold freshNames
  have hrange : (List.range count).Nodup := List.nodup_range
  exact hrange.map fun _ _ heq => Nat.add_left_cancel heq

private theorem mem_freshNames {start count x : Nat} :
    x ∈ freshNames start count ↔ start ≤ x ∧ x < start + count := by
  simp only [freshNames, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, hoffset, rfl⟩
    omega
  · rintro ⟨hlower, hupper⟩
    exact ⟨x - start, by omega, by omega⟩

private theorem satisfies_dedup {assignment : Nat → Bool} {formula : CNF} :
    CNF.Satisfies assignment formula.dedup ↔ CNF.Satisfies assignment formula := by
  simp [CNF.Satisfies]

/-- Satisfaction of the reduced formula implies satisfaction of the original formula under the
same values of the original variable names. -/
theorem satisfies_of_satisfies_to3Parsimonious {formula : CNF} {start : Nat}
    {assignment : Nat → Bool}
    (hsatisfies : (formula.to3Parsimonious start).Satisfies assignment) :
    formula.Satisfies assignment := by
  rw [to3Parsimonious_eq] at hsatisfies
  exact splitAll_sound assignment formula
    (freshNames start formula.numFreshParsimonious3) (satisfies_dedup.mp hsatisfies)

private theorem vars_subset_to3Parsimonious (formula : CNF) (start : Nat) :
    formula.vars ⊆ (formula.to3Parsimonious start).vars := by
  intro x hx
  obtain ⟨clause, hclause, polarity, hliteral⟩ := CNF.mem_vars.mp hx
  obtain ⟨output, houtput, hliteral⟩ :=
    splitAll_contains formula (freshNames start formula.numFreshParsimonious3)
      clause hclause (x, polarity) hliteral
  apply CNF.mem_vars.mpr
  refine ⟨output, ?_, polarity, hliteral⟩
  rw [to3Parsimonious_eq, List.mem_dedup]
  exact houtput

private theorem mem_vars_to3Parsimonious (formula : CNF) (start x : Nat)
    (hx : x ∈ (formula.to3Parsimonious start).vars) :
    x ∈ formula.vars ∨
      (start ≤ x ∧ x < start + formula.numFreshParsimonious3) := by
  obtain ⟨output, houtput, polarity, hliteral⟩ := CNF.mem_vars.mp hx
  rw [to3Parsimonious_eq, List.mem_dedup] at houtput
  rcases splitAll_vars formula (freshNames start formula.numFreshParsimonious3)
      output houtput (x, polarity) hliteral with hfresh | hold
  · exact Or.inr (mem_freshNames.mp hfresh)
  · obtain ⟨sourceClause, hclause, sourceLiteral, hliteral, heq⟩ := hold
    apply Or.inl
    apply CNF.mem_vars.mpr
    refine ⟨sourceClause, hclause, sourceLiteral.2, ?_⟩
    have hpair : sourceLiteral = (x, sourceLiteral.2) := Prod.ext heq rfl
    exact hpair ▸ hliteral

/-- Every output clause has length at most three, and duplicate clauses have been removed. -/
theorem isThreeCNF_to3Parsimonious (formula : CNF) (start : Nat) :
    (∀ clause ∈ formula.to3Parsimonious start, clause.length ≤ 3) ∧
      (formula.to3Parsimonious start).Nodup := by
  constructor
  · intro clause hclause
    rw [to3Parsimonious_eq, List.mem_dedup] at hclause
    exact splitAll_width formula _ (by rw [length_freshNames]) clause hclause
  · rw [to3Parsimonious_eq]
    exact List.nodup_dedup _

/-- A width bound on the input gives the source bounds on allocated fresh variables and output
clauses. -/
theorem size_to3Parsimonious (formula : CNF) (start k : Nat)
    (hbound : ∀ clause ∈ formula, clause.length ≤ k) :
    formula.numFreshParsimonious3 ≤ (k - 3) * formula.length ∧
      (formula.to3Parsimonious start).length ≤
        formula.length + 3 * ((k - 3) * formula.length) := by
  have hfresh := numFreshParsimonious3_le_aux k formula hbound
  refine ⟨hfresh, ?_⟩
  calc
    (formula.to3Parsimonious start).length ≤
        (splitAll (freshNames start formula.numFreshParsimonious3) formula).length := by
      rw [to3Parsimonious_eq]
      exact (List.dedup_sublist _).length_le
    _ = formula.length + 3 * formula.numFreshParsimonious3 :=
      length_splitAll formula _ (by rw [length_freshNames])
    _ ≤ formula.length + 3 * ((k - 3) * formula.length) := by omega

/-- Every satisfying assignment of the original formula has exactly one satisfying extension that
can differ only on the allocated fresh-variable interval. -/
theorem existsUnique_satisfies_to3Parsimonious {formula : CNF} {start : Nat}
    {assignment : Nat → Bool}
    (hstart : ∀ x ∈ formula.vars, x < start)
    (hsatisfies : formula.Satisfies assignment) :
    ∃! extension : Nat → Bool,
      (formula.to3Parsimonious start).Satisfies extension ∧
        ∀ x, x < start ∨ start + formula.numFreshParsimonious3 ≤ x →
          extension x = assignment x := by
  classical
  let fresh := freshNames start formula.numFreshParsimonious3
  have hnotFresh : ∀ clause ∈ formula, ∀ literal ∈ clause, literal.1 ∉ fresh := by
    intro clause hclause literal hliteral hmem
    have hlt : literal.1 < start := hstart literal.1
      (CNF.mem_vars.mpr ⟨clause, hclause, literal.2, hliteral⟩)
    have hinterval := mem_freshNames.mp hmem
    omega
  obtain ⟨extension, hagrees, hextension⟩ :=
    splitAll_extend formula fresh assignment
      (by simpa [fresh] using nodup_freshNames start formula.numFreshParsimonious3)
      hnotFresh hsatisfies
  refine ⟨extension, ⟨?_, ?_⟩, ?_⟩
  · rw [to3Parsimonious_eq]
    exact satisfies_dedup.mpr hextension
  · intro x hx
    apply hagrees x
    intro hmem
    have hinterval := mem_freshNames.mp hmem
    omega
  · rintro other ⟨hother, hotherAgrees⟩
    funext x
    by_cases hx : x ∈ fresh
    · apply splitAll_unique other extension formula fresh (by
          dsimp [fresh]
          rw [length_freshNames]) ?_ ?_ hextension x hx
      · intro clause hclause literal hliteral
        have hlt : literal.1 < start := hstart literal.1
          (CNF.mem_vars.mpr ⟨clause, hclause, literal.2, hliteral⟩)
        rw [hotherAgrees literal.1 (Or.inl hlt),
          hagrees literal.1 (hnotFresh clause hclause literal hliteral)]
      · rw [to3Parsimonious_eq] at hother
        exact satisfies_dedup.mp hother
    · have houtside : x < start ∨ start + formula.numFreshParsimonious3 ≤ x := by
          have hnotInterval : ¬(start ≤ x ∧ x < start + formula.numFreshParsimonious3) :=
            fun hinterval => hx (by
              dsimp [fresh]
              exact mem_freshNames.mpr hinterval)
          omega
      rw [hotherAgrees x houtside, hagrees x hx]

/-- The parsimonious reduction preserves the number of assignments to the variables occurring in
the formula. -/
theorem modelCount_to3Parsimonious (formula : CNF) (start : Nat)
    (hstart : ∀ x ∈ formula.vars, x < start) :
    (formula.to3Parsimonious start).modelCount = formula.modelCount := by
  classical
  let reduced := formula.to3Parsimonious start
  let oldTotal : ({x // x ∈ formula.vars} → Bool) → Nat → Bool := fun assignment x =>
    if h : x ∈ formula.vars then assignment ⟨x, h⟩ else false
  let newTotal : ({x // x ∈ reduced.vars} → Bool) → Nat → Bool := fun assignment x =>
    if h : x ∈ reduced.vars then assignment ⟨x, h⟩ else false
  let OldSat := {assignment : {x // x ∈ formula.vars} → Bool //
    formula.Satisfies (oldTotal assignment)}
  let NewSat := {assignment : {x // x ∈ reduced.vars} → Bool //
    reduced.Satisfies (newTotal assignment)}
  let extend : OldSat → Nat → Bool := fun assignment =>
    Classical.choose
      (existsUnique_satisfies_to3Parsimonious hstart assignment.property)
  have extend_spec (assignment : OldSat) :
      reduced.Satisfies (extend assignment) ∧
        ∀ x, x < start ∨ start + formula.numFreshParsimonious3 ≤ x →
          extend assignment x = oldTotal assignment.1 x := by
    dsimp [reduced, extend]
    exact (Classical.choose_spec
      (existsUnique_satisfies_to3Parsimonious hstart assignment.property)).1
  let forward : OldSat → NewSat := fun assignment =>
    ⟨fun x => extend assignment x.1, by
      apply CNF.satisfies_congr (assignment₁ := extend assignment)
        (assignment₂ := newTotal fun x => extend assignment x.1)
      · intro x hx
        dsimp [newTotal]
        rw [ite_eq_left hx]
      · exact (extend_spec assignment).1⟩
  let backward : NewSat → OldSat := fun assignment =>
    ⟨fun x => newTotal assignment.1 x.1, by
      apply CNF.satisfies_congr
        (assignment₁ := newTotal assignment.1)
        (assignment₂ := oldTotal fun x => newTotal assignment.1 x.1)
      · intro x hx
        dsimp [oldTotal]
        rw [ite_eq_left hx]
      · exact satisfies_of_satisfies_to3Parsimonious assignment.property⟩
  have leftInverse : Function.LeftInverse backward forward := by
    intro assignment
    apply Subtype.ext
    funext x
    have hxNew : x.1 ∈ reduced.vars := by
      dsimp [reduced]
      exact vars_subset_to3Parsimonious formula start x.2
    have hxlt : x.1 < start := hstart x.1 x.2
    change newTotal (forward assignment).1 x.1 = assignment.1 x
    rw [show newTotal (forward assignment).1 x.1 = extend assignment x.1 by
      dsimp [newTotal, forward]
      rw [ite_eq_left hxNew]]
    rw [(extend_spec assignment).2 x.1 (Or.inl hxlt)]
    dsimp [oldTotal]
    rw [ite_eq_left x.2]
  have rightInverse : Function.RightInverse backward forward := by
    intro assignment
    apply Subtype.ext
    funext x
    let source : OldSat := backward assignment
    have hother :
        reduced.Satisfies (newTotal assignment.1) ∧
          ∀ y, y < start ∨ start + formula.numFreshParsimonious3 ≤ y →
            newTotal assignment.1 y = oldTotal source.1 y := by
      refine ⟨assignment.property, ?_⟩
      intro y hy
      by_cases hyOld : y ∈ formula.vars
      · dsimp [oldTotal, source, backward]
        rw [ite_eq_left hyOld]
      · have hyNew : y ∉ reduced.vars := by
          intro hyNew
          rcases mem_vars_to3Parsimonious formula start y (by
            simpa [reduced] using hyNew) with hyOld' | hyInterval
          · exact hyOld hyOld'
          · omega
        dsimp [newTotal, oldTotal]
        rw [dite_eq_right hyNew, dite_eq_right hyOld]
    have heq : newTotal assignment.1 = extend source :=
      (existsUnique_satisfies_to3Parsimonious hstart source.property).unique
        hother (extend_spec source)
    change extend source x.1 = assignment.1 x
    have hxNew : x.1 ∈ reduced.vars := x.2
    have hxTotal : newTotal assignment.1 x.1 = assignment.1 x := by
      dsimp [newTotal]
      rw [ite_eq_left hxNew]
    rw [← heq, hxTotal]
  let satEquiv : OldSat ≃ NewSat :=
    { toFun := forward
      invFun := backward
      left_inv := leftInverse
      right_inv := rightInverse }
  rw [modelCount, modelCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr satEquiv.symm

end CNF

end Cslib.Logic.PL
