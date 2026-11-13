/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.Resolution
public import Mathlib.Logic.Relation

/-!
# Conflict-driven clause learning

An abstract CDCL transition system over the CNF representation `Cslib.Logic.PL.CNF`, in the
style of the abstract DPLL and CDCL calculi of Nieuwenhuis, Oliveras, and Tinelli and of
Weidenbach (as formalized by Blanchette, Fleury, Lammich, and Weidenbach). A state holds a
trail of decided and propagated literals, the learned clauses, and the clause under conflict
analysis, if any. The current clause set is the input formula followed by the learned clauses.

- `decide` sets an unassigned variable of the input.
- `propagate` sets the remaining literal of a current clause whose other literals are false on
  the trail.
- `conflict` makes a current clause that is false on the trail the conflict clause.
- `resolve` and `skip` analyze the conflict: resolve the conflict clause with the reason of the
  most recent literal, or pop that literal when the conflict clause does not mention it.
- `backjump` learns the conflict clause, cuts the trail back, and propagates a literal of the
  learned clause.
- `learn` adds a clause together with a resolution derivation of it from the current clause
  set, a `Cslib.Logic.PL.CNF.ResolutionDerivable` certificate.
- `restart` clears the trail and keeps the learned clauses.

No rule takes semantic entailment as a premise. Decision levels are not tracked: conflict
analysis and backjumping carry only the side conditions that soundness needs, so the results
also cover stricter strategies such as backjumping to the second-highest level of the learned
clause.

Soundness is an invariant of the reachable states (`Invariant`): the learned clauses, the
conflict clause, and every reason clause on the trail are resolution-derivable from the input;
every propagated literal is forced by its reason and the older part of the trail; and the
conflict clause is false on the trail. Resolution soundness
(`Cslib.Logic.PL.CNF.ResolutionDerivable.satisfies`) turns this invariant into unsatisfiability
of the input when a reachable state derives the empty clause or is in conflict without decisions
on its trail. Only this direction is proved: termination, completeness, and the correctness of
satisfiable answers are out of scope.

## Main definitions

- `TrailEntry`, `State`: trail entries and CDCL states.
- `Step F`: one CDCL transition for the input formula `F`; reachability is
  `Relation.ReflTransGen (Step F)`.
- `ReasonsValid F`, `Invariant F`: the soundness invariant.

## Main results

- `Invariant.reflTransGen`: the invariant holds along every run, and `invariant_initial` at the
  initial state.
- `resolutionDerivable_of_reachable`: every current clause of a reachable state is
  resolution-derivable from the input.
- `not_cnfSat_of_reachable_nil_mem`, `not_cnfSat_of_reachable_conflict_nil`: a reachable state
  that has learned the empty clause, or whose conflict clause is empty, refutes the input.
- `not_cnfSat_of_reachable_conflict`: a reachable state in conflict whose trail has no
  decision refutes the input; CDCL reports unsatisfiability on such a conflict.

## References

- R. Nieuwenhuis, A. Oliveras, C. Tinelli, *Solving SAT and SAT modulo theories: from an
  abstract Davis-Putnam-Logemann-Loveland procedure to DPLL(T)*, J. ACM 53(6), 2006, 937-977.
- J. C. Blanchette, M. Fleury, P. Lammich, C. Weidenbach, *A verified SAT solver framework with
  learn, forget, restart, and incrementality*, J. Automated Reasoning 61, 2018, 333-365.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

/-- Resolution derivations compose: if every clause of `ψ` is derivable from `φ`, then so is
every clause derivable from `ψ`. -/
theorem ResolutionDerivable.trans {φ ψ : CNF} {C : CNFClause} (h : ψ.ResolutionDerivable C)
    (hψ : ∀ D ∈ ψ, φ.ResolutionDerivable D) : φ.ResolutionDerivable C := by
  induction h with
  | ax hC => exact hψ _ hC
  | resolve x _ _ hxC hxD ihC ihD => exact .resolve x ihC ihD hxC hxD

end Cslib.Logic.PL.CNF

namespace Cslib.Algorithms.SAT.CDCL

open Cslib.Logic.PL

/-- A trail entry: a decision literal, or a literal propagated by its reason clause. -/
inductive TrailEntry where
  /-- A literal set by a decision. -/
  | decided (literal : Nat × Bool)
  /-- A literal forced by the reason clause `reason`. -/
  | propagated (literal : Nat × Bool) (reason : CNFClause)
  deriving DecidableEq

/-- The literal that a trail entry sets true. -/
def TrailEntry.lit : TrailEntry → Nat × Bool
  | .decided literal => literal
  | .propagated literal _ => literal

/-- The trail sets `literal` false: it sets the complementary literal true. -/
abbrev Falsifies (trail : List TrailEntry) (literal : Nat × Bool) : Prop :=
  (literal.1, !literal.2) ∈ trail.map TrailEntry.lit

/-- The trail assigns the variable `x`. -/
abbrev Assigns (trail : List TrailEntry) (x : Nat) : Prop :=
  x ∈ trail.map fun entry => entry.lit.1

/-- A CDCL state. -/
structure State where
  /-- Decided and propagated literals, the most recent first. -/
  trail : List TrailEntry
  /-- The learned clauses; the current clause set is the input formula followed by them. -/
  learned : CNF
  /-- The clause under conflict analysis, if the state is in conflict. -/
  conflict : Option CNFClause

/-- The initial state: an empty trail, no learned clauses, and no conflict. -/
def State.initial : State := ⟨[], [], none⟩

/-- Resolve a reason clause containing `literal` with a conflict clause containing the
complement of `literal`, on the variable of `literal`. -/
def resolveOn : Nat × Bool → CNFClause → CNFClause → CNFClause
  | (x, true), reason, conflict => CNFClause.resolvent x reason conflict
  | (x, false), reason, conflict => CNFClause.resolvent x conflict reason

/-- The literals of `resolveOn literal reason conflict` are those of `reason` other than
`literal` and those of `conflict` other than the complement of `literal`. -/
theorem mem_resolveOn {literal m : Nat × Bool} {reason conflict : CNFClause} :
    m ∈ resolveOn literal reason conflict ↔
      (m ∈ reason ∧ m ≠ literal) ∨ (m ∈ conflict ∧ m ≠ (literal.1, !literal.2)) := by
  obtain ⟨x, _ | _⟩ := literal
  · simp only [resolveOn, CNFClause.mem_resolvent, Bool.not_false]
    exact or_comm
  · simp only [resolveOn, CNFClause.mem_resolvent, Bool.not_true]

/-- Resolving two derivable clauses on a literal of the first whose complement is in the
second gives a derivable clause. -/
theorem resolutionDerivable_resolveOn {φ : CNF} {literal : Nat × Bool}
    {reason conflict : CNFClause} (hreason : φ.ResolutionDerivable reason)
    (hconflict : φ.ResolutionDerivable conflict) (hlit : literal ∈ reason)
    (hcompl : (literal.1, !literal.2) ∈ conflict) :
    φ.ResolutionDerivable (resolveOn literal reason conflict) := by
  obtain ⟨x, _ | _⟩ := literal
  · exact .resolve x hconflict hreason hcompl hlit
  · exact .resolve x hreason hconflict hlit hcompl

/-- One CDCL transition for the input formula `F`. The current clause set is
`F ++ learned`. -/
inductive Step (F : CNF) : State → State → Prop
  /-- Decide: set an unassigned variable of the input. -/
  | decide {trail : List TrailEntry} {learned : CNF} {literal : Nat × Bool}
      (hvar : literal.1 ∈ F.vars) (hfree : ¬Assigns trail literal.1) :
      Step F ⟨trail, learned, none⟩ ⟨.decided literal :: trail, learned, none⟩
  /-- Unit propagation: every literal of a current clause other than `literal` is false on the
  trail, and the variable of `literal` is unassigned. -/
  | propagate {trail : List TrailEntry} {learned : CNF} {clause : CNFClause}
      {literal : Nat × Bool} (hclause : clause ∈ F ++ learned) (hlit : literal ∈ clause)
      (hrest : ∀ m ∈ clause, m ≠ literal → Falsifies trail m)
      (hfree : ¬Assigns trail literal.1) :
      Step F ⟨trail, learned, none⟩ ⟨.propagated literal clause :: trail, learned, none⟩
  /-- Conflict: a current clause that is false on the trail becomes the conflict clause. -/
  | conflict {trail : List TrailEntry} {learned : CNF} {clause : CNFClause}
      (hclause : clause ∈ F ++ learned) (hfalse : ∀ m ∈ clause, Falsifies trail m) :
      Step F ⟨trail, learned, none⟩ ⟨trail, learned, some clause⟩
  /-- Conflict analysis: resolve the conflict clause with the reason of the most recent
  literal, whose complement it contains, and pop that literal. -/
  | resolve {trail : List TrailEntry} {learned : CNF} {literal : Nat × Bool}
      {reason conflict : CNFClause} (hcompl : (literal.1, !literal.2) ∈ conflict) :
      Step F ⟨.propagated literal reason :: trail, learned, some conflict⟩
        ⟨trail, learned, some (resolveOn literal reason conflict)⟩
  /-- Conflict analysis: pop the most recent propagated literal when the conflict clause does
  not contain its complement. -/
  | skip {trail : List TrailEntry} {learned : CNF} {literal : Nat × Bool}
      {reason conflict : CNFClause} (hcompl : (literal.1, !literal.2) ∉ conflict) :
      Step F ⟨.propagated literal reason :: trail, learned, some conflict⟩
        ⟨trail, learned, some conflict⟩
  /-- Backjump: learn the conflict clause, cut the trail back to a suffix `kept` on which every
  literal of the clause other than `literal` is false and the variable of `literal` is
  unassigned, and propagate `literal` with the learned clause as its reason. The conflict
  clause comes from the input or learned clauses by `resolve` steps, so it is
  resolution-derivable from the input (`Invariant.conflict`). -/
  | backjump {dropped kept : List TrailEntry} {learned : CNF} {conflict : CNFClause}
      {literal : Nat × Bool} (hlit : literal ∈ conflict)
      (hrest : ∀ m ∈ conflict, m ≠ literal → Falsifies kept m)
      (hfree : ¬Assigns kept literal.1) :
      Step F ⟨dropped ++ kept, learned, some conflict⟩
        ⟨.propagated literal conflict :: kept, conflict :: learned, none⟩
  /-- Learn: add a clause together with a resolution derivation of it from the current clause
  set. -/
  | learn {trail : List TrailEntry} {learned : CNF} {conflict : Option CNFClause}
      {clause : CNFClause} (hcert : (F ++ learned).ResolutionDerivable clause) :
      Step F ⟨trail, learned, conflict⟩ ⟨trail, clause :: learned, conflict⟩
  /-- Restart: clear the trail and keep the learned clauses. -/
  | restart {trail : List TrailEntry} {learned : CNF} :
      Step F ⟨trail, learned, none⟩ ⟨[], learned, none⟩

/-- Every propagated entry of the trail is justified: its reason clause is resolution-derivable
from `F` and contains the propagated literal, and every other literal of the reason is false on
the older part of the trail. -/
inductive ReasonsValid (F : CNF) : List TrailEntry → Prop
  /-- The empty trail. -/
  | nil : ReasonsValid F []
  /-- A decision needs no justification. -/
  | decided {literal : Nat × Bool} {trail : List TrailEntry} :
      ReasonsValid F trail → ReasonsValid F (.decided literal :: trail)
  /-- A propagated literal is justified by its reason clause. -/
  | propagated {literal : Nat × Bool} {reason : CNFClause} {trail : List TrailEntry} :
      F.ResolutionDerivable reason → literal ∈ reason →
      (∀ m ∈ reason, m ≠ literal → Falsifies trail m) → ReasonsValid F trail →
      ReasonsValid F (.propagated literal reason :: trail)

/-- The soundness invariant of CDCL for the input formula `F`. -/
structure Invariant (F : CNF) (s : State) : Prop where
  /-- Every learned clause is resolution-derivable from `F`. -/
  learned : ∀ C ∈ s.learned, F.ResolutionDerivable C
  /-- The conflict clause is resolution-derivable from `F` and false on the trail. -/
  conflict : ∀ C, s.conflict = some C →
    F.ResolutionDerivable C ∧ ∀ m ∈ C, Falsifies s.trail m
  /-- Every propagated literal on the trail is justified by its reason clause. -/
  reasons : ReasonsValid F s.trail

/-- Justified propagations stay justified when newer trail entries are dropped. -/
theorem ReasonsValid.of_append {F : CNF} {dropped kept : List TrailEntry}
    (h : ReasonsValid F (dropped ++ kept)) : ReasonsValid F kept := by
  induction dropped with
  | nil => exact h
  | cons entry dropped ih =>
    cases h with
    | decided h => exact ih h
    | propagated _ _ _ h => exact ih h

/-- A literal false on `entry :: trail` other than the complement of `entry` is false on
`trail`. -/
theorem Falsifies.of_cons {entry : TrailEntry} {trail : List TrailEntry} {m : Nat × Bool}
    (h : Falsifies (entry :: trail) m) (hne : m ≠ (entry.lit.1, !entry.lit.2)) :
    Falsifies trail m := by
  rcases List.mem_cons.mp h with heq | h
  · exact absurd (by rw [← heq]; simp) hne
  · exact h

/-- An assignment that sets true every literal of a trail sets false every literal that the
trail falsifies. -/
theorem not_satisfies_of_falsifies {σ : Nat → Bool} {trail : List TrailEntry}
    {m : Nat × Bool} (htrail : ∀ entry ∈ trail, CNFLiteral.Satisfies σ entry.lit)
    (hm : Falsifies trail m) : ¬CNFLiteral.Satisfies σ m := by
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
  have hcompl := htrail entry hentry
  rw [heq] at hcompl
  simp only [CNFLiteral.satisfies_def] at hcompl ⊢
  intro hsat
  rw [hsat] at hcompl
  simp at hcompl

/-- An assignment satisfying `F` sets true every literal of a trail without decisions whose
propagations are justified. -/
theorem ReasonsValid.satisfies {F : CNF} {σ : Nat → Bool} (hσ : F.Satisfies σ)
    {trail : List TrailEntry} (h : ReasonsValid F trail) :
    (∀ literal, TrailEntry.decided literal ∉ trail) →
      ∀ entry ∈ trail, CNFLiteral.Satisfies σ entry.lit := by
  induction h with
  | nil => simp
  | decided _ _ => exact fun hdec ↦ absurd (List.mem_cons_self ..) (hdec _)
  | @propagated literal reason trail hreason hlit hrest _ ih =>
    intro hdec
    have htrail := ih fun l hl ↦ hdec l (List.mem_cons_of_mem _ hl)
    intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · obtain ⟨m, hm, hsat⟩ := hreason.satisfies hσ
      by_cases hml : m = literal
      · subst hml
        exact hsat
      · exact absurd hsat (not_satisfies_of_falsifies htrail (hrest m hm hml))
    · exact htrail entry hentry

/-- The invariant holds at the initial state. -/
theorem invariant_initial (F : CNF) : Invariant F State.initial where
  learned := by simp [State.initial]
  conflict := by simp [State.initial]
  reasons := .nil

/-- Every CDCL step preserves the invariant. -/
theorem Invariant.step {F : CNF} {s t : State} (hs : Invariant F s) (h : Step F s t) :
    Invariant F t := by
  have hcur : ∀ C ∈ F ++ s.learned, F.ResolutionDerivable C := fun C hC ↦
    (List.mem_append.mp hC).elim .ax (hs.learned C)
  cases h with
  | decide _ _ => exact ⟨hs.learned, by simp, .decided hs.reasons⟩
  | propagate hclause hlit hrest _ =>
    exact ⟨hs.learned, by simp, .propagated (hcur _ hclause) hlit hrest hs.reasons⟩
  | conflict hclause hfalse =>
    refine ⟨hs.learned, ?_, hs.reasons⟩
    rintro C ⟨⟩
    exact ⟨hcur _ hclause, hfalse⟩
  | resolve hcompl =>
    obtain ⟨hderiv, hfalse⟩ := hs.conflict _ rfl
    cases hs.reasons with
    | propagated hreason hlit hrest hvalid =>
      refine ⟨hs.learned, ?_, hvalid⟩
      rintro C ⟨⟩
      refine ⟨resolutionDerivable_resolveOn hreason hderiv hlit hcompl, fun m hm ↦ ?_⟩
      rcases mem_resolveOn.mp hm with ⟨hm, hne⟩ | ⟨hm, hne⟩
      · exact hrest m hm hne
      · exact (hfalse m hm).of_cons hne
  | skip hcompl =>
    obtain ⟨hderiv, hfalse⟩ := hs.conflict _ rfl
    cases hs.reasons with
    | propagated _ _ _ hvalid =>
      refine ⟨hs.learned, ?_, hvalid⟩
      rintro C ⟨⟩
      refine ⟨hderiv, fun m hm ↦ (hfalse m hm).of_cons ?_⟩
      rintro rfl
      exact hcompl hm
  | backjump hlit hrest _ =>
    obtain ⟨hderiv, -⟩ := hs.conflict _ rfl
    refine ⟨?_, by simp, .propagated hderiv hlit hrest hs.reasons.of_append⟩
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hderiv
    · exact hs.learned C hC
  | learn hcert =>
    refine ⟨?_, hs.conflict, hs.reasons⟩
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hcert.trans hcur
    · exact hs.learned C hC
  | restart => exact ⟨hs.learned, by simp, .nil⟩

/-- The invariant holds along every run from a state that satisfies it. -/
theorem Invariant.reflTransGen {F : CNF} {s t : State} (hs : Invariant F s)
    (h : Relation.ReflTransGen (Step F) s t) : Invariant F t := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact ih.step hstep

/-- Every state reachable from the initial state satisfies the invariant. -/
theorem invariant_of_reachable {F : CNF} {s : State}
    (h : Relation.ReflTransGen (Step F) State.initial s) : Invariant F s :=
  (invariant_initial F).reflTransGen h

/-- Every current clause of a reachable state, input or learned, is resolution-derivable from
the input formula. -/
theorem resolutionDerivable_of_reachable {F : CNF} {s : State}
    (h : Relation.ReflTransGen (Step F) State.initial s) {C : CNFClause}
    (hC : C ∈ F ++ s.learned) : F.ResolutionDerivable C :=
  (List.mem_append.mp hC).elim .ax ((invariant_of_reachable h).learned C)

/-- **Soundness of CDCL**: a reachable state whose current clause set contains the empty clause
refutes the input formula. -/
theorem not_cnfSat_of_reachable_nil_mem {F : CNF} {s : State}
    (h : Relation.ReflTransGen (Step F) State.initial s) (hnil : [] ∈ F ++ s.learned) :
    ¬CNFSat F :=
  CNF.not_cnfSat_of_resolutionDerivable_nil (resolutionDerivable_of_reachable h hnil)

/-- **Soundness of CDCL**: a reachable state whose conflict clause is empty refutes the input
formula. -/
theorem not_cnfSat_of_reachable_conflict_nil {F : CNF} {s : State}
    (h : Relation.ReflTransGen (Step F) State.initial s) (hs : s.conflict = some []) :
    ¬CNFSat F :=
  CNF.not_cnfSat_of_resolutionDerivable_nil ((invariant_of_reachable h).conflict [] hs).1

/-- **Soundness of CDCL**: a reachable state in conflict whose trail has no decision refutes
the input formula. CDCL reports unsatisfiability on such a conflict. -/
theorem not_cnfSat_of_reachable_conflict {F : CNF} {s : State} {C : CNFClause}
    (h : Relation.ReflTransGen (Step F) State.initial s) (hs : s.conflict = some C)
    (hdec : ∀ literal, TrailEntry.decided literal ∉ s.trail) : ¬CNFSat F := by
  have hinv := invariant_of_reachable h
  obtain ⟨hderiv, hfalse⟩ := hinv.conflict C hs
  rw [cnfSat_iff_exists_satisfies]
  rintro ⟨σ, hσ⟩
  obtain ⟨m, hm, hsat⟩ := hderiv.satisfies hσ
  exact not_satisfies_of_falsifies (hinv.reasons.satisfies hσ hdec) (hfalse m hm) hsat

end Cslib.Algorithms.SAT.CDCL
