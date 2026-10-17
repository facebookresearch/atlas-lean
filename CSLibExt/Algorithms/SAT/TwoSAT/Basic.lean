/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-SAT through the implication graph
-/
module

public import CSLibExt.Logics.Propositional.CNF.Resolution
public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents

/-!
# 2-SAT through the implication graph

A clause `a ∨ b` is equivalent to each of the implications `¬a → b` and
`¬b → a`.  The *implication graph* of a 2-CNF formula has the literals as
vertices and these implications as edges.  Aspvall, Plass, and Tarjan (1979)
showed that a 2-CNF formula without the empty clause is satisfiable iff no
variable `x` has `x` and `¬x` in the same strongly connected component.

This file proves that characterization for the CSLibExt CNF representation
and turns it into a decision procedure that reads the SCC blocks computed by
`Cslib.Algorithms.Lean.StronglyConnectedComponents.components`.

## Main definitions

- `IsTwoCNF φ` : every clause of `φ` has at most two literals.
- `ImpEdge φ l m`, `ImpReach φ l m` : implication-graph edges and reachability
  on literals `Nat × Bool`.
- `implicationGraph φ` : the implication graph as a `DirectedAdjacency` on the
  literals over the variables of `φ`.
- `decide2SAT φ` : no empty clause, and no SCC block contains a literal and
  its complement.

## Main results

- `cnfSat_iff_of_isTwoCNF` : a 2-CNF formula is satisfiable iff it has no empty
  clause and no variable `x` with `x` and `¬x` reaching each other.
- `decide2SAT_eq_true_iff` : the SCC-based procedure decides satisfiability of
  2-CNF formulas.

## Proof notes

Satisfying assignments are closed along implication edges, which gives the
forward direction.  For the converse, an unsatisfiable formula has a
resolution refutation (`CNF.resolutionDerivable_nil_of_not_cnfSat`).  Every
clause resolution derives from a 2-CNF satisfies the invariant `Inv`: for each
of its literals `a`, the complement `¬a` reaches a literal of the clause.  The
last step of a refutation resolves two clauses consisting only of `x`, and only
of `¬x`, and the invariant for those two clauses says that `x` and `¬x` reach
each other.  The skew symmetry of the graph (`l ⇝ m` gives `¬m ⇝ ¬l`) is what
lets the invariant pass through a resolution step.

## References

- B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing
  the truth of certain quantified Boolean formulas*, Inf. Process. Lett. 8(3),
  1979, 121-123.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.SAT.TwoSAT

open Cslib.Logic.PL Cslib.Algorithms.Lean Cslib.Algorithms.Lean.StronglyConnectedComponents

/-- A CNF formula in which every clause has at most two literals. -/
def IsTwoCNF (φ : CNF) : Prop := ∀ C ∈ φ, C.length ≤ 2

instance (φ : CNF) : Decidable (IsTwoCNF φ) := by
  unfold IsTwoCNF
  infer_instance

/-- The complementary literal. -/
abbrev neg (l : Nat × Bool) : Nat × Bool := (l.1, !l.2)

@[simp]
theorem neg_neg (l : Nat × Bool) : neg (neg l) = l := by
  simp [neg]

theorem neg_ne_self (l : Nat × Bool) : neg l ≠ l := by
  obtain ⟨x, b⟩ := l
  cases b <;> simp [neg]

theorem satisfies_neg_iff {σ : Nat → Bool} {l : Nat × Bool} :
    CNFLiteral.Satisfies σ (neg l) ↔ ¬ CNFLiteral.Satisfies σ l := by
  obtain ⟨x, b⟩ := l
  cases b <;> cases h : σ x <;> simp [CNFLiteral.Satisfies, h]

/-- In a clause with at most two literals, two different members are all of its members. -/
theorem eq_or_eq_of_length_le_two {C : CNFClause} (hC : C.length ≤ 2) {a b c : Nat × Bool}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) (hc : c ∈ C) : c = a ∨ c = b := by
  match C, hC with
  | [], _ => simp at ha
  | [x], _ =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [x, y], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      simp_all
  | _ :: _ :: _ :: _, h => simp at h

/-! ### The implication graph on literals -/

/-- Implication edge `l → m`: some clause contains `¬l` and `m`, either as two different
literals or as its only literal (a unit clause `m` gives the edge `¬m → m`). -/
def ImpEdge (φ : CNF) (l m : Nat × Bool) : Prop :=
  ∃ C ∈ φ, neg l ∈ C ∧ m ∈ C ∧ (neg l ≠ m ∨ ∀ c ∈ C, c = m)

instance (φ : CNF) (l m : Nat × Bool) : Decidable (ImpEdge φ l m) := by
  unfold ImpEdge
  infer_instance

/-- Reachability in the implication graph. -/
def ImpReach (φ : CNF) : Nat × Bool → Nat × Bool → Prop :=
  Relation.ReflTransGen (ImpEdge φ)

/-- **Skew symmetry**: an edge `l → m` has the contrapositive edge `¬m → ¬l`. -/
theorem ImpEdge.skew {φ : CNF} {l m : Nat × Bool} (h : ImpEdge φ l m) :
    ImpEdge φ (neg m) (neg l) := by
  obtain ⟨C, hC, hl, hm, hor⟩ := h
  refine ⟨C, hC, by simpa using hm, hl, ?_⟩
  rw [neg_neg]
  rcases hor with hne | hall
  · exact Or.inl (Ne.symm hne)
  · exact Or.inr fun c hc ↦ (hall c hc).trans (hall _ hl).symm

theorem ImpReach.skew {φ : CNF} {l m : Nat × Bool} (h : ImpReach φ l m) :
    ImpReach φ (neg m) (neg l) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ e ih => exact Relation.ReflTransGen.head e.skew ih

/-- Satisfying assignments of a 2-CNF formula are closed along implication edges. -/
theorem satisfies_of_impEdge {φ : CNF} (h2 : IsTwoCNF φ) {σ : Nat → Bool}
    (hσ : φ.Satisfies σ) {l m : Nat × Bool} (h : ImpEdge φ l m)
    (hl : CNFLiteral.Satisfies σ l) : CNFLiteral.Satisfies σ m := by
  obtain ⟨C, hC, hnl, hm, hor⟩ := h
  obtain ⟨c, hc, hcs⟩ := hσ C hC
  have hcl : c ≠ neg l := fun h ↦ satisfies_neg_iff.mp (h ▸ hcs) hl
  rcases hor with hne | hall
  · rcases eq_or_eq_of_length_le_two (h2 C hC) hnl hm hne hc with h | h
    · exact absurd h hcl
    · exact h ▸ hcs
  · exact hall c hc ▸ hcs

theorem satisfies_of_impReach {φ : CNF} (h2 : IsTwoCNF φ) {σ : Nat → Bool}
    (hσ : φ.Satisfies σ) {l m : Nat × Bool} (h : ImpReach φ l m)
    (hl : CNFLiteral.Satisfies σ l) : CNFLiteral.Satisfies σ m := by
  induction h with
  | refl => exact hl
  | tail _ e ih => exact satisfies_of_impEdge h2 hσ e ih

/-! ### Resolution derivations from a 2-CNF formula -/

/-- The invariant of clauses derived by resolution: the complement of each literal reaches
some literal of the clause. -/
def Inv (φ : CNF) (C : CNFClause) : Prop := ∀ a ∈ C, ∃ b ∈ C, ImpReach φ (neg a) b

theorem inv_of_mem {φ : CNF} {C : CNFClause} (hC : C ∈ φ) : Inv φ C := by
  intro a ha
  by_cases hall : ∀ c ∈ C, c = a
  · exact ⟨a, ha, Relation.ReflTransGen.single ⟨C, hC, by simpa using ha, ha,
      Or.inr hall⟩⟩
  · simp only [not_forall] at hall
    obtain ⟨b, hb, hba⟩ := hall
    exact ⟨b, hb, Relation.ReflTransGen.single ⟨C, hC, by simpa using ha, hb,
      Or.inl (by rw [neg_neg]; exact fun h ↦ hba h.symm)⟩⟩

theorem inv_resolvent {φ : CNF} {C D : CNFClause} {x : Nat} (hC : Inv φ C) (hD : Inv φ D)
    (hx : (x, true) ∈ C) (hx' : (x, false) ∈ D) : Inv φ (CNFClause.resolvent x C D) := by
  intro c hc
  rcases CNFClause.mem_resolvent.mp hc with ⟨hcC, -⟩ | ⟨hcD, -⟩
  · obtain ⟨c', hc'C, hr⟩ := hC c hcC
    by_cases hc' : c' = (x, true)
    · subst hc'
      obtain ⟨d, hdD, hrd⟩ := hD (x, false) hx'
      by_cases hd : d = (x, false)
      · subst hd
        -- `¬c ⇝ x ⇝ ¬x ⇝ c`, the last part by skew symmetry of `¬c ⇝ x`
        have hback : ImpReach φ (neg (x, true)) c := by simpa using hr.skew
        exact ⟨c, hc, (hr.trans hrd).trans hback⟩
      · exact ⟨d, CNFClause.mem_resolvent.mpr (Or.inr ⟨hdD, hd⟩), hr.trans hrd⟩
    · exact ⟨c', CNFClause.mem_resolvent.mpr (Or.inl ⟨hc'C, hc'⟩), hr⟩
  · obtain ⟨d', hd'D, hr⟩ := hD c hcD
    by_cases hd' : d' = (x, false)
    · subst hd'
      obtain ⟨c'', hc''C, hrc⟩ := hC (x, true) hx
      by_cases hc'' : c'' = (x, true)
      · subst hc''
        have hback : ImpReach φ (neg (x, false)) c := by simpa using hr.skew
        exact ⟨c, hc, (hr.trans hrc).trans hback⟩
      · exact ⟨c'', CNFClause.mem_resolvent.mpr (Or.inl ⟨hc''C, hc''⟩), hr.trans hrc⟩
    · exact ⟨d', CNFClause.mem_resolvent.mpr (Or.inr ⟨hd'D, hd'⟩), hr⟩

theorem inv_of_resolutionDerivable {φ : CNF} {C : CNFClause} (h : φ.ResolutionDerivable C) :
    Inv φ C := by
  induction h with
  | ax hC => exact inv_of_mem hC
  | resolve x _ _ hx hx' ihC ihD => exact inv_resolvent ihC ihD hx hx'

/-- A resolution refutation of a formula without the empty clause yields a variable `x`
with `x` and `¬x` reaching each other. -/
theorem exists_contradictory_of_resolutionDerivable_nil {φ : CNF} (hnil : [] ∉ φ)
    (h : φ.ResolutionDerivable []) :
    ∃ x, ImpReach φ (x, true) (x, false) ∧ ImpReach φ (x, false) (x, true) := by
  generalize hE : ([] : CNFClause) = E at h
  cases h with
  | ax hmem => exact absurd (hE ▸ hmem) hnil
  | @resolve C D x hCd hDd hx hx' =>
    have hallC : ∀ c ∈ C, c = (x, true) := fun c hc ↦ by
      by_contra hne
      have : c ∈ CNFClause.resolvent x C D := CNFClause.mem_resolvent.mpr (Or.inl ⟨hc, hne⟩)
      simp [← hE] at this
    have hallD : ∀ d ∈ D, d = (x, false) := fun d hd ↦ by
      by_contra hne
      have : d ∈ CNFClause.resolvent x C D := CNFClause.mem_resolvent.mpr (Or.inr ⟨hd, hne⟩)
      simp [← hE] at this
    obtain ⟨b, hb, hrb⟩ := inv_of_resolutionDerivable hCd (x, true) hx
    obtain ⟨d, hd, hrd⟩ := inv_of_resolutionDerivable hDd (x, false) hx'
    rw [hallC b hb] at hrb
    rw [hallD d hd] at hrd
    exact ⟨x, hrd, hrb⟩

/-- **2-SAT characterization** (Aspvall, Plass, Tarjan): a 2-CNF formula is satisfiable iff
it has no empty clause and no variable `x` such that `x` and `¬x` reach each other in the
implication graph. -/
theorem cnfSat_iff_of_isTwoCNF {φ : CNF} (h2 : IsTwoCNF φ) :
    CNFSat φ ↔ [] ∉ φ ∧
      ∀ x, ¬ (ImpReach φ (x, true) (x, false) ∧ ImpReach φ (x, false) (x, true)) := by
  constructor
  · intro hsat
    obtain ⟨σ, hσ⟩ := cnfSat_iff_exists_satisfies.mp hsat
    refine ⟨fun hmem ↦ by simpa using hσ [] hmem, fun x ⟨h₁, h₂⟩ ↦ ?_⟩
    cases hx : σ x
    · have := satisfies_of_impReach h2 hσ h₂ (by simp [CNFLiteral.Satisfies, hx])
      simp [CNFLiteral.Satisfies, hx] at this
    · have := satisfies_of_impReach h2 hσ h₁ (by simp [CNFLiteral.Satisfies, hx])
      simp [CNFLiteral.Satisfies, hx] at this
  · rintro ⟨hnil, hx⟩
    by_contra hsat
    obtain ⟨x, h₁, h₂⟩ := exists_contradictory_of_resolutionDerivable_nil hnil
      (CNF.resolutionDerivable_nil_of_not_cnfSat hsat)
    exact hx x ⟨h₁, h₂⟩

/-! ### The implication graph as a finite directed graph, and the SCC decision procedure -/

/-- Literals over the variables of `φ`: the vertices of the implication graph. -/
abbrev Lit (φ : CNF) := {l : Nat × Bool // l.1 ∈ φ.vars}

instance (φ : CNF) : Hashable (Lit φ) := ⟨fun l ↦ hash l.val⟩

/-- The complementary literal over the same variable. -/
def Lit.neg {φ : CNF} (l : Lit φ) : Lit φ := ⟨TwoSAT.neg l.val, l.prop⟩

/-- The variables of `φ` as a list without repetition. -/
def varList (φ : CNF) : List Nat := (φ.flatMap fun C ↦ C.map Prod.fst).dedup

theorem mem_varList {φ : CNF} {x : Nat} : x ∈ varList φ ↔ x ∈ φ.vars := by
  simp only [varList, List.mem_dedup, List.mem_flatMap, List.mem_map, CNF.mem_vars]
  constructor
  · rintro ⟨C, hC, ⟨y, b⟩, hl, rfl⟩
    exact ⟨C, hC, b, hl⟩
  · rintro ⟨C, hC, b, hl⟩
    exact ⟨C, hC, (x, b), hl, rfl⟩

/-- All literals over the variables of `φ`, without repetition. -/
def litList (φ : CNF) : List (Lit φ) :=
  (varList φ).attach.flatMap fun x ↦
    [⟨(x.1, true), mem_varList.mp x.2⟩, ⟨(x.1, false), mem_varList.mp x.2⟩]

theorem mem_litList (φ : CNF) (l : Lit φ) : l ∈ litList φ := by
  obtain ⟨⟨x, b⟩, hx⟩ := l
  simp only [litList, List.mem_flatMap, List.mem_attach, true_and, List.mem_cons,
    List.not_mem_nil, or_false]
  refine ⟨⟨x, mem_varList.mpr hx⟩, ?_⟩
  cases b <;> simp

theorem nodup_litList (φ : CNF) : (litList φ).Nodup := by
  rw [litList, List.nodup_flatMap]
  refine ⟨fun x _ ↦ by simp, ?_⟩
  refine (List.nodup_attach.mpr (List.nodup_dedup (φ.flatMap fun C ↦ C.map Prod.fst))).imp
    fun {x y} hxy ↦ ?_
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
  refine List.disjoint_left.mpr fun {l} hl hl' ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl hl'
  apply hne
  rcases hl with rfl | rfl <;> rcases hl' with h | h <;>
    exact congrArg (fun l : Lit φ ↦ l.val.1) h

/-- The implication-graph successors of a literal. -/
def successors (φ : CNF) (l : Lit φ) : List (Lit φ) :=
  (litList φ).filter fun m ↦ decide (ImpEdge φ l.val m.val)

/-- The successor lists of all literals, computed once and stored in a hash map so that the
SCC traversal looks them up in expected constant time. -/
def adjacencyTable (φ : CNF) : Std.HashMap (Lit φ) (List (Lit φ)) :=
  Std.HashMap.ofList ((litList φ).map fun l ↦ (l, successors φ l))

theorem adjacencyTable_getD (φ : CNF) (l : Lit φ) :
    (adjacencyTable φ).getD l [] = successors φ l := by
  refine Std.HashMap.getD_ofList_of_mem (k := l) (beq_self_eq_true l) ?_
    (List.mem_map.mpr ⟨l, mem_litList φ l, rfl⟩)
  exact List.pairwise_map.mpr ((nodup_litList φ).imp fun hne ↦ beq_eq_false_iff_ne.mpr hne)

/-- The implication graph of `φ` on the literals over its variables, with adjacency read
from `adjacencyTable φ`. -/
def implicationGraph (φ : CNF) : DirectedAdjacency (Lit φ) :=
  let table := adjacencyTable φ
  { vertices := litList φ
    vertices_nodup := nodup_litList φ
    vertices_complete := mem_litList φ
    adjacency := fun l ↦ table.getD l [] }

theorem implicationGraph_edge {φ : CNF} {l m : Lit φ} :
    (implicationGraph φ).Edge l m ↔ ImpEdge φ l.val m.val := by
  simp [DirectedAdjacency.Edge, implicationGraph, adjacencyTable_getD, successors, mem_litList]

/-- An implication edge ends at a literal over a variable of `φ`. -/
theorem mem_vars_of_impEdge {φ : CNF} {l m : Nat × Bool} (h : ImpEdge φ l m) :
    m.1 ∈ φ.vars := by
  obtain ⟨C, hC, -, hm, -⟩ := h
  exact CNF.mem_vars.mpr ⟨C, hC, m.2, hm⟩

/-- Reachability in `implicationGraph φ` is implication-graph reachability on literals. -/
theorem implicationGraph_reachable_iff {φ : CNF} {l m : Lit φ} :
    (implicationGraph φ).Reachable l m ↔ ImpReach φ l.val m.val := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ e ih => exact ih.tail (implicationGraph_edge.mp e)
  · intro h
    suffices ∀ m' : Nat × Bool, ImpReach φ l.val m' →
        ∃ hm : m'.1 ∈ φ.vars, (implicationGraph φ).Reachable l ⟨m', hm⟩ by
      obtain ⟨_, hr⟩ := this m.val h
      exact hr
    intro m' hm'
    induction hm' with
    | refl => exact ⟨l.prop, Relation.ReflTransGen.refl⟩
    | @tail b c _ e ih =>
      obtain ⟨hb, hr⟩ := ih
      exact ⟨mem_vars_of_impEdge e,
        hr.tail (implicationGraph_edge.mpr (show ImpEdge φ b c from e))⟩

/-- The 2-SAT decision procedure: reject an empty clause, then accept iff no SCC block of
the implication graph contains a literal together with its complement. -/
def decide2SAT (φ : CNF) : Bool :=
  !φ.contains [] &&
    (components (implicationGraph φ)).all fun block ↦ block.all fun l ↦ !block.contains l.neg

/-- A contradictory pair of literals involves a variable of the formula. -/
theorem mem_vars_of_impReach_true_false {φ : CNF} {x : Nat}
    (h : ImpReach φ (x, true) (x, false)) : x ∈ φ.vars := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, e, -⟩
  · simp at heq
  · obtain ⟨C, hC, hnl, -, -⟩ := e
    exact CNF.mem_vars.mpr ⟨C, hC, false, hnl⟩

theorem decide2SAT_eq_true_iff_aux (φ : CNF) :
    decide2SAT φ = true ↔ [] ∉ φ ∧
      ∀ x, ¬ (ImpReach φ (x, true) (x, false) ∧ ImpReach φ (x, false) (x, true)) := by
  have h0 : (!φ.contains []) = true ↔ [] ∉ φ := by simp
  have hc : ∀ (block : List (Lit φ)) (l : Lit φ), (!block.contains l.neg) = true ↔
      l.neg ∉ block := by
    intro block l
    simp
  simp only [decide2SAT, Bool.and_eq_true, h0, List.all_eq_true, hc]
  refine and_congr Iff.rfl ⟨fun h x ⟨h₁, h₂⟩ ↦ ?_, fun h block hblock l hl hneg ↦ ?_⟩
  · have hx := mem_vars_of_impReach_true_false h₁
    let l : Lit φ := ⟨(x, true), hx⟩
    have hsc : StronglyConnected (implicationGraph φ) l l.neg :=
      ⟨implicationGraph_reachable_iff.mpr h₁, implicationGraph_reachable_iff.mpr h₂⟩
    obtain ⟨block, hblock, hl, hneg⟩ :=
      (share_component_iff_stronglyConnected _ _ _).mpr hsc
    exact h block hblock l hl hneg
  · have hsc := (share_component_iff_stronglyConnected (implicationGraph φ) l l.neg).mp
      ⟨block, hblock, hl, hneg⟩
    have h₁ := implicationGraph_reachable_iff.mp hsc.1
    have h₂ := implicationGraph_reachable_iff.mp hsc.2
    obtain ⟨⟨x, b⟩, hx⟩ := l
    cases b
    · exact h x ⟨h₂, h₁⟩
    · exact h x ⟨h₁, h₂⟩

/-- **Correctness of the SCC-based 2-SAT procedure** on 2-CNF formulas. -/
theorem decide2SAT_eq_true_iff {φ : CNF} (h2 : IsTwoCNF φ) :
    decide2SAT φ = true ↔ CNFSat φ := by
  rw [decide2SAT_eq_true_iff_aux, cnfSat_iff_of_isTwoCNF h2]

end Cslib.Algorithms.SAT.TwoSAT
