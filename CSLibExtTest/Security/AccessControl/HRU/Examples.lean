/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Security.AccessControl.HRU.Basic
import Cslib.Foundations.Semantics.LTS.Relation
import Mathlib.Data.Fin.VecNotation

/-!
Tests for the access-matrix model of Harrison, Ruzzo and Ullman: primitive operations are
deterministic, reachability is the reflexive-transitive closure of command runs, a failed condition
is an identity step, and the commands of the paper's Examples 1, 2 and 5 behave as the paper says.
-/

open Cslib
open Cslib.Security.AccessControl.HRU

namespace Cslib.Security.AccessControl.HRU.Tests

variable {R N : Type*}

/-! ### General checks -/

/-- A cell outside `S × O` is empty. -/
theorem matrix_eq_empty (Q : Configuration R N) {s o : N}
    (h : s ∉ Q.subjects ∨ o ∉ Q.objects) : Q.matrix s o = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hr => by
    obtain ⟨hs, ho⟩ := Q.mem_of_mem_matrix hr
    exact h.elim (· hs) (· ho)

/-- Two configurations with the same subjects and objects and the same cells on `S × O` are
equal. -/
theorem configuration_ext {Q Q' : Configuration R N} (hS : Q'.subjects = Q.subjects)
    (hO : Q'.objects = Q.objects)
    (hP : ∀ s ∈ Q'.subjects, ∀ o ∈ Q'.objects, Q'.matrix s o = Q.matrix s o) : Q' = Q := by
  ext1
  · exact hS
  · exact hO
  · funext s o
    by_cases hso : s ∈ Q'.subjects ∧ o ∈ Q'.objects
    · exact hP s hso.1 o hso.2
    · rw [not_and_or] at hso
      rw [matrix_eq_empty Q' hso, matrix_eq_empty Q (by rwa [← hS, ← hO])]

/-- The relation `Q ⇒_op Q'` determines `Q'`: the paper's clauses, with the matrix empty outside
`S × O`, leave no freedom. -/
theorem primOp_yields_unique {op : PrimOp R N} {Q Q₁ Q₂ : Configuration R N}
    (h₁ : op.Yields Q Q₁) (h₂ : op.Yields Q Q₂) : Q₁ = Q₂ := by
  cases op with
  | enter r s o =>
    obtain ⟨-, -, hS₁, hO₁, hc₁, hr₁⟩ := h₁
    obtain ⟨-, -, hS₂, hO₂, hc₂, hr₂⟩ := h₂
    ext1
    · rw [hS₁, hS₂]
    · rw [hO₁, hO₂]
    · funext s₁ o₁
      by_cases hso : (s₁, o₁) = (s, o)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hso
        rw [hc₁, hc₂]
      · rw [hr₁ s₁ o₁ hso, hr₂ s₁ o₁ hso]
  | delete r s o =>
    obtain ⟨-, -, hS₁, hO₁, hc₁, hr₁⟩ := h₁
    obtain ⟨-, -, hS₂, hO₂, hc₂, hr₂⟩ := h₂
    ext1
    · rw [hS₁, hS₂]
    · rw [hO₁, hO₂]
    · funext s₁ o₁
      by_cases hso : (s₁, o₁) = (s, o)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hso
        rw [hc₁, hc₂]
      · rw [hr₁ s₁ o₁ hso, hr₂ s₁ o₁ hso]
  | createSubject s =>
    obtain ⟨-, hS₁, hO₁, hk₁, hrow₁, hcol₁⟩ := h₁
    obtain ⟨-, hS₂, hO₂, hk₂, hrow₂, hcol₂⟩ := h₂
    refine configuration_ext (hS₁.trans hS₂.symm) (hO₁.trans hO₂.symm) fun s₁ hs₁ o₁ ho₁ => ?_
    have hs₂ : s₁ ∈ Q₂.subjects := by rw [hS₂, ← hS₁]; exact hs₁
    have ho₂ : o₁ ∈ Q₂.objects := by rw [hO₂, ← hO₁]; exact ho₁
    by_cases hss : s₁ = s
    · subst hss
      rw [hrow₁ o₁ ho₁, hrow₂ o₁ ho₂]
    by_cases hos : o₁ = s
    · subst hos
      rw [hcol₁ s₁ hs₁, hcol₂ s₁ hs₂]
    rw [hS₁, Set.mem_insert_iff] at hs₁
    rw [hO₁, Set.mem_insert_iff] at ho₁
    rw [hk₁ s₁ (hs₁.resolve_left hss) o₁ (ho₁.resolve_left hos),
      hk₂ s₁ (hs₁.resolve_left hss) o₁ (ho₁.resolve_left hos)]
  | createObject o =>
    obtain ⟨-, hS₁, hO₁, hk₁, hcol₁⟩ := h₁
    obtain ⟨-, hS₂, hO₂, hk₂, hcol₂⟩ := h₂
    refine configuration_ext (hS₁.trans hS₂.symm) (hO₁.trans hO₂.symm) fun s₁ hs₁ o₁ ho₁ => ?_
    have hs₂ : s₁ ∈ Q₂.subjects := by rw [hS₂, ← hS₁]; exact hs₁
    by_cases hoo : o₁ = o
    · subst hoo
      rw [hcol₁ s₁ hs₁, hcol₂ s₁ hs₂]
    rw [hO₁, Set.mem_insert_iff] at ho₁
    rw [hS₁] at hs₁
    rw [hk₁ s₁ hs₁ o₁ (ho₁.resolve_left hoo), hk₂ s₁ hs₁ o₁ (ho₁.resolve_left hoo)]
  | destroySubject s =>
    obtain ⟨-, hS₁, hO₁, hk₁⟩ := h₁
    obtain ⟨-, hS₂, hO₂, hk₂⟩ := h₂
    refine configuration_ext (hS₁.trans hS₂.symm) (hO₁.trans hO₂.symm) fun s₁ hs₁ o₁ ho₁ => ?_
    rw [hk₁ s₁ hs₁ o₁ ho₁,
      hk₂ s₁ (by rw [hS₂, ← hS₁]; exact hs₁) o₁ (by rw [hO₂, ← hO₁]; exact ho₁)]
  | destroyObject o =>
    obtain ⟨-, -, hS₁, hO₁, hk₁⟩ := h₁
    obtain ⟨-, -, hS₂, hO₂, hk₂⟩ := h₂
    refine configuration_ext (hS₁.trans hS₂.symm) (hO₁.trans hO₂.symm) fun s₁ hs₁ o₁ ho₁ => ?_
    rw [hk₁ s₁ hs₁ o₁ ho₁,
      hk₂ s₁ (by rw [hS₂, ← hS₁]; exact hs₁) o₁ (by rw [hO₂, ← hO₁]; exact ho₁)]

/-- The precondition of a primitive operation, as the paper states it. -/
def Precondition : PrimOp R N → Configuration R N → Prop
  | .enter _ s o, Q => s ∈ Q.subjects ∧ o ∈ Q.objects
  | .delete _ s o, Q => s ∈ Q.subjects ∧ o ∈ Q.objects
  | .createSubject s, Q => s ∉ Q.objects
  | .createObject o, Q => o ∉ Q.objects
  | .destroySubject s, Q => s ∈ Q.subjects
  | .destroyObject o, Q => o ∈ Q.objects ∧ o ∉ Q.subjects

open Classical in
/-- A primitive operation yields a configuration exactly when its precondition holds: the paper's
clauses are consistent with the matrix being empty outside `S × O`. -/
theorem exists_yields_iff (op : PrimOp R N) (Q : Configuration R N) :
    (∃ Q', op.Yields Q Q') ↔ Precondition op Q := by
  constructor
  · rintro ⟨Q', h⟩
    cases op with
    | enter => exact ⟨h.1, h.2.1⟩
    | delete => exact ⟨h.1, h.2.1⟩
    | createSubject => exact h.1
    | createObject => exact h.1
    | destroySubject => exact h.1
    | destroyObject => exact ⟨h.1, h.2.1⟩
  · intro h
    cases op with
    | enter r s o =>
      refine ⟨{ Q with
        matrix := fun s₁ o₁ => if (s₁, o₁) = (s, o) then insert r (Q.matrix s o) else Q.matrix s₁ o₁
        mem_of_mem_matrix := fun {s₁ o₁ r₁} hr => ?_ }, h.1, h.2, rfl, rfl, by simp, ?_⟩
      · split_ifs at hr with hso
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hso
          exact h
        · exact Q.mem_of_mem_matrix hr
      · intro s₁ o₁ hso
        simp only [hso, ite_false]
    | delete r s o =>
      refine ⟨{ Q with
        matrix := fun s₁ o₁ => if (s₁, o₁) = (s, o) then Q.matrix s o \ {r} else Q.matrix s₁ o₁
        mem_of_mem_matrix := fun {s₁ o₁ r₁} hr => ?_ }, h.1, h.2, rfl, rfl, by simp, ?_⟩
      · split_ifs at hr with hso
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hso
          exact h
        · exact Q.mem_of_mem_matrix hr
      · intro s₁ o₁ hso
        simp only [hso, ite_false]
    | createSubject s =>
      have hsS : s ∉ Q.subjects := fun hs => h (Q.subjects_subset_objects hs)
      refine ⟨⟨insert s Q.subjects, insert s Q.objects, Q.objects_finite.insert s,
        Set.insert_subset_insert Q.subjects_subset_objects, Q.matrix, fun hr => ?_⟩,
        h, rfl, rfl, fun _ _ _ _ => rfl, fun o₁ _ => matrix_eq_empty Q (.inl hsS),
        fun s₁ _ => matrix_eq_empty Q (.inr h)⟩
      exact ⟨Set.mem_insert_of_mem _ (Q.mem_of_mem_matrix hr).1,
        Set.mem_insert_of_mem _ (Q.mem_of_mem_matrix hr).2⟩
    | createObject o =>
      refine ⟨⟨Q.subjects, insert o Q.objects, Q.objects_finite.insert o,
        Q.subjects_subset_objects.trans (Set.subset_insert _ _), Q.matrix, fun hr => ?_⟩,
        h, rfl, rfl, fun _ _ _ _ => rfl, fun s₁ _ => matrix_eq_empty Q (.inr h)⟩
      exact ⟨(Q.mem_of_mem_matrix hr).1, Set.mem_insert_of_mem _ (Q.mem_of_mem_matrix hr).2⟩
    | destroySubject s =>
      refine ⟨⟨Q.subjects \ {s}, Q.objects \ {s}, Q.objects_finite.sdiff,
        Set.sdiff_subset_sdiff_left Q.subjects_subset_objects,
        fun s₁ o₁ => if s₁ = s ∨ o₁ = s then ∅ else Q.matrix s₁ o₁, fun {s₁ o₁ r₁} hr => ?_⟩,
        h, rfl, rfl, fun s₁ hs₁ o₁ ho₁ => ?_⟩
      · split_ifs at hr with hso
        · exact absurd hr (Set.notMem_empty _)
        · rw [not_or] at hso
          exact ⟨⟨(Q.mem_of_mem_matrix hr).1, hso.1⟩, ⟨(Q.mem_of_mem_matrix hr).2, hso.2⟩⟩
      · simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hs₁ ho₁
        simp only [hs₁.2, ho₁.2, or_self, ite_false]
    | destroyObject o =>
      refine ⟨⟨Q.subjects, Q.objects \ {o}, Q.objects_finite.sdiff,
        fun x hx => ⟨Q.subjects_subset_objects hx, fun hxo => h.2 (hxo ▸ hx)⟩,
        fun s₁ o₁ => if o₁ = o then ∅ else Q.matrix s₁ o₁, fun {s₁ o₁ r₁} hr => ?_⟩,
        h.1, h.2, rfl, rfl, fun s₁ _ o₁ ho₁ => ?_⟩
      · split_ifs at hr with ho
        · exact absurd hr (Set.notMem_empty _)
        · exact ⟨(Q.mem_of_mem_matrix hr).1, ⟨(Q.mem_of_mem_matrix hr).2, ho⟩⟩
      · simp only [Set.mem_sdiff, Set.mem_singleton_iff] at ho₁
        simp only [ho₁.2, ite_false]

/-- Reachability in `ProtectionSystem.lts` is the relation `⊢*` of the paper: the reflexive and
transitive closure of `Q ⊢ Q'`, which holds when some command of the system with some actual
parameters yields `Q'` from `Q`. -/
theorem canReach_iff_reflTransGen (ps : ProtectionSystem R) (Q₀ Q : Configuration R N) :
    ps.lts.CanReach Q₀ Q ↔
      Relation.ReflTransGen (fun Q Q' => ∃ α ∈ ps.commands, ∃ x, α.Yields x Q Q') Q₀ Q := by
  rw [← LTS.reflTransGen_unlabelledTr_iff]
  have : ps.lts.UnlabelledTr = fun Q Q' : Configuration R N =>
      ∃ α ∈ ps.commands, ∃ x, α.Yields x Q Q' := by
    funext Q Q'
    exact propext ⟨fun ⟨a, ha, hy⟩ => ⟨a.1, ha, a.2, hy⟩,
      fun ⟨α, hα, x, hy⟩ => ⟨⟨α, x⟩, hα, hy⟩⟩
  rw [this]

/-- The condition of a command with no tests always holds. -/
theorem holds_of_condition_eq_nil {α : Command R} (h : α.condition = []) (x : Fin α.arity → N)
    (Q : Configuration R N) : α.Holds x Q :=
  fun _ ht => absurd (h ▸ ht) List.not_mem_nil

/-- An operation in the body of a command, split as `pre ++ op :: post`. -/
theorem mem_body {α : Command R} {pre post : List (PrimOp R (Fin α.arity))}
    {op : PrimOp R (Fin α.arity)} (h : α.body = pre ++ op :: post) : op ∈ α.body := by
  simp [h]

/-! ### Examples 1 and 2 of the paper: creating a file and conferring a right -/

/-- The processes and files of the examples. -/
inductive Name
  | sam
  | joe
  | code
  deriving DecidableEq

/-- Generic rights: ownership and reading. -/
inductive Right
  | own
  | read
  deriving DecidableEq

/-- `command CREATE(process, file) create object file; enter own into (process, file) end`. -/
abbrev create : Command Right where
  arity := 2
  condition := []
  body := [(.createObject 1 : PrimOp Right (Fin 2)), .enter .own 0 1]

/-- `command CONFER_read(owner, friend, file) if own in (owner, file) then enter read into
(friend, file) end`. -/
abbrev conferRead : Command Right where
  arity := 3
  condition := [(.own, (0 : Fin 3), (2 : Fin 3))]
  body := [(.enter .read 1 2 : PrimOp Right (Fin 3))]

/-- The protection system with the commands `CREATE` and `CONFER_read`. -/
def files : ProtectionSystem Right := ⟨{create, conferRead}⟩

theorem create_mem : create ∈ files.commands := Finset.mem_insert_self _ _

theorem conferRead_mem : conferRead ∈ files.commands :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Example 2: the processes `Sam` and `Joe`, with no rights and no files. -/
def start : Configuration Right Name where
  subjects := {.sam, .joe}
  objects := {.sam, .joe}
  objects_finite := Set.toFinite _
  subjects_subset_objects := subset_rfl
  matrix _ _ := ∅
  mem_of_mem_matrix h := absurd h (Set.notMem_empty _)

/-- After `create object Code`. -/
def created : Configuration Right Name where
  subjects := {.sam, .joe}
  objects := insert .code {.sam, .joe}
  objects_finite := Set.toFinite _
  subjects_subset_objects := Set.subset_insert _ _
  matrix _ _ := ∅
  mem_of_mem_matrix h := absurd h (Set.notMem_empty _)

/-- After `CREATE(Sam, Code)`: Sam owns Code. -/
def owned : Configuration Right Name where
  subjects := {.sam, .joe}
  objects := insert .code {.sam, .joe}
  objects_finite := Set.toFinite _
  subjects_subset_objects := Set.subset_insert _ _
  matrix s o := if s = .sam ∧ o = .code then {.own} else ∅
  mem_of_mem_matrix {s o r} h := by
    split_ifs at h with hso
    · obtain ⟨rfl, rfl⟩ := hso
      simp
    · exact absurd h (Set.notMem_empty _)

/-- After `CONFER_read(Sam, Joe, Code)`: Joe may also read Code. -/
def shared : Configuration Right Name where
  subjects := {.sam, .joe}
  objects := insert .code {.sam, .joe}
  objects_finite := Set.toFinite _
  subjects_subset_objects := Set.subset_insert _ _
  matrix s o :=
    if s = .sam ∧ o = .code then {.own} else if s = .joe ∧ o = .code then {.read} else ∅
  mem_of_mem_matrix {s o r} h := by
    split_ifs at h with h₁ h₂
    · obtain ⟨rfl, rfl⟩ := h₁
      simp
    · obtain ⟨rfl, rfl⟩ := h₂
      simp
    · exact absurd h (Set.notMem_empty _)

/-- `create object Code` turns the initial configuration into `created`. -/
theorem createObject_yields : (PrimOp.createObject Name.code : PrimOp Right Name).Yields start
    created :=
  ⟨by simp [start], rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- `enter own into (Sam, Code)` turns `created` into `owned`. -/
theorem enterOwn_yields : (PrimOp.enter Right.own Name.sam Name.code).Yields created owned := by
  refine ⟨by simp [created], by simp [created], rfl, rfl, by simp [owned, created], ?_⟩
  intro s₁ o₁ h
  simp only [owned, created, ite_eq_right_iff]
  rintro ⟨rfl, rfl⟩
  exact absurd rfl h

/-- `CREATE(Sam, Code)` turns the initial configuration into the one where Sam owns Code. -/
theorem create_yields : create.Yields ![.sam, .code] start owned :=
  Or.inr ⟨holds_of_condition_eq_nil rfl _ _, .stepL createObject_yields (.single _ enterOwn_yields)⟩

/-- A failed condition is an identity step: Joe owns nothing, so `CONFER_read(Joe, Sam, Sam)`
leaves the initial configuration unchanged. -/
theorem conferRead_identity : files.lts.Tr start ⟨conferRead, ![.joe, .sam, .sam]⟩ start :=
  ⟨conferRead_mem, Or.inl ⟨fun h => by simpa [start] using h _ List.mem_cons_self, rfl⟩⟩

/-- `CONFER_read` leaks `read` from the configuration where Sam owns Code. -/
theorem conferRead_leaks : conferRead.Leaks .read owned := by
  refine ⟨![.sam, .joe, .code], ?_, [], (.enter .read 1 2 : PrimOp Right (Fin 3)), [], rfl, owned,
    shared, .refl, ?_, .joe, .code, by simp [owned], by simp [shared]⟩
  · intro t ht
    simp only [conferRead, List.mem_singleton] at ht
    subst ht
    simp [owned]
  · refine ⟨by simp [owned], by simp [owned], rfl, rfl, by simp [shared, owned], ?_⟩
    intro s₁ o₁ h
    have h' : ¬(s₁ = .joe ∧ o₁ = .code) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp only [shared, owned, h', ite_false]

/-- The initial configuration of Example 2 is unsafe for `read`. -/
theorem start_unsafe_read : files.Unsafe .read start :=
  ProtectionSystem.Unsafe.of_canReach
    ⟨[⟨create, ![.sam, .code]⟩], .single _ ⟨create_mem, create_yields⟩⟩
    (ProtectionSystem.Leaks.unsafe ⟨conferRead, conferRead_mem, conferRead_leaks⟩)

/-- `CREATE` leaks `own` from the initial configuration, through the second operation of its
body. -/
theorem start_leaks_own : files.Leaks .own start :=
  ⟨create, create_mem, ![.sam, .code], holds_of_condition_eq_nil rfl _ _,
    [(.createObject 1 : PrimOp Right (Fin 2))], (.enter .own 0 1 : PrimOp Right (Fin 2)), [], rfl,
    created, owned, .single _ createObject_yields, enterOwn_yields, .sam, .code,
    by simp [created], by simp [owned]⟩

/-- The initial configuration itself does not leak `read`, although it is unsafe for `read`:
`CREATE` enters only `own`, and the condition of `CONFER_read` fails. -/
theorem start_not_leaks_read : ¬files.Leaks .read start := by
  rintro ⟨α, hα, x, hx, pre, op, post, hbody, Q₁, Q₂, -, hop, s, o, hQ₁, hQ₂⟩
  have heq := hop.eq_enter_of_notMem_of_mem hQ₁ hQ₂
  simp only [files, Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl
  · have hmem := mem_body hbody
    simp [create] at hmem
    rcases hmem with rfl | rfl <;> simp [PrimOp.map] at heq
  · exact absurd (hx _ List.mem_cons_self) (by simp [start])

/-! ### Example 5 of the paper: a command that can leak without completing -/

/-- Two generic rights `r₁` and `r₂`. -/
inductive Right₅
  | r₁
  | r₂
  deriving DecidableEq

/-- `command α(X, Y, Z) enter r₁ into (X, X); destroy subject X; enter r₂ into (Y, Z) end`. -/
abbrev alpha : Command Right₅ where
  arity := 3
  condition := []
  body := [(.enter .r₁ 0 0 : PrimOp Right₅ (Fin 3)), .destroySubject 0, .enter .r₂ 1 2]

/-- The protection system whose only command is `α`. -/
def single : ProtectionSystem Right₅ := ⟨{alpha}⟩

/-- Exactly one subject and no other objects. -/
def lone : Configuration Right₅ Name where
  subjects := {.sam}
  objects := {.sam}
  objects_finite := Set.toFinite _
  subjects_subset_objects := subset_rfl
  matrix _ _ := ∅
  mem_of_mem_matrix h := absurd h (Set.notMem_empty _)

/-- `lone` after `enter r₁ into (Sam, Sam)`. -/
def loneEntered : Configuration Right₅ Name where
  subjects := {.sam}
  objects := {.sam}
  objects_finite := Set.toFinite _
  subjects_subset_objects := subset_rfl
  matrix s o := if s = .sam ∧ o = .sam then {.r₁} else ∅
  mem_of_mem_matrix {s o r} h := by
    split_ifs at h with hso
    · obtain ⟨rfl, rfl⟩ := hso
      simp
    · exact absurd h (Set.notMem_empty _)

/-- From `lone`, the first two operations of `α` leave no subject. -/
theorem subjects_eq_empty {a : Name} {Q : Configuration Right₅ Name}
    (h : PrimOp.lts.MTr lone [.enter .r₁ a a, .destroySubject a] Q) : Q.subjects = ∅ := by
  obtain ⟨Q₁, ⟨ha, -, hS₁, -⟩, hm⟩ := LTS.MTr.cons_iff.mp h
  obtain ⟨Q₂, ⟨-, hS₂, -⟩, hm⟩ := LTS.MTr.cons_iff.mp hm
  rw [← LTS.MTr.nil_eq _ hm, hS₂, hS₁]
  simp only [lone, Set.mem_singleton_iff] at ha ⊢
  simp [ha]

/-- No run of `α` from `lone` completes: after `destroy subject X` there is no subject left for
`enter r₂ into (Y, Z)`. -/
theorem lone_isTerminal : single.lts.IsTerminal lone := by
  rintro ⟨α, x⟩ Q ⟨hα, hy⟩
  obtain rfl := Finset.mem_singleton.mp hα
  rcases hy with ⟨hn, -⟩ | ⟨-, hm⟩
  · exact hn (holds_of_condition_eq_nil rfl _ _)
  · have hm' : PrimOp.lts.MTr lone
        ([.enter .r₁ (x 0) (x 0), .destroySubject (x 0)] ++ [.enter .r₂ (x 1) (x 2)]) Q := hm
    obtain ⟨Q₂, hm₂, hm₃⟩ := LTS.MTr.split hm'
    obtain ⟨-, ⟨hy, -⟩, -⟩ := LTS.MTr.cons_iff.mp hm₃
    rw [subjects_eq_empty hm₂] at hy
    exact hy

/-- Only `lone` itself is reachable from `lone`. -/
theorem eq_of_canReach {Q : Configuration Right₅ Name} (h : single.lts.CanReach lone Q) :
    Q = lone := by
  obtain ⟨_ | ⟨a, as⟩, hm⟩ := h
  · exact (LTS.MTr.nil_eq _ hm).symm
  · obtain ⟨Q₁, htr, -⟩ := LTS.MTr.cons_iff.mp hm
    exact absurd htr (lone_isTerminal a Q₁)

/-- Example 5: `lone` is unsafe for `r₁`, through the first operation of `α`, even though `α`
never runs to completion from it. -/
theorem lone_unsafe_r₁ : single.Unsafe .r₁ lone := by
  refine ProtectionSystem.Leaks.unsafe ⟨alpha, Finset.mem_singleton_self _, fun _ => .sam,
    holds_of_condition_eq_nil rfl _ _, [], (.enter .r₁ 0 0 : PrimOp Right₅ (Fin 3)), _, rfl, lone,
    loneEntered, .refl, ?_, .sam, .sam, by simp [lone], by simp [loneEntered]⟩
  refine ⟨by simp [lone], by simp [lone], rfl, rfl, by simp [loneEntered, lone], ?_⟩
  intro s₁ o₁ h
  have h' : ¬(s₁ = .sam ∧ o₁ = .sam) := by
    rintro ⟨rfl, rfl⟩
    exact h rfl
  simp only [loneEntered, lone, h', ite_false]

/-- Example 5: `lone` is safe for `r₂`. -/
theorem lone_safe_r₂ : ¬single.Unsafe .r₂ lone := by
  rintro ⟨Q, hQ, α, hα, x, -, pre, op, post, hbody, Q₁, Q₂, hpre, hop, s, o, hQ₁, hQ₂⟩
  obtain rfl := eq_of_canReach hQ
  obtain rfl := Finset.mem_singleton.mp hα
  have heq := hop.eq_enter_of_notMem_of_mem hQ₁ hQ₂
  match pre, hbody with
  | [], hbody =>
    simp only [alpha, List.nil_append, List.cons.injEq] at hbody
    obtain ⟨rfl, -⟩ := hbody
    simp [PrimOp.map] at heq
  | [_], hbody =>
    simp only [alpha, List.cons_append, List.nil_append, List.cons.injEq] at hbody
    obtain ⟨-, rfl, -⟩ := hbody
    simp [PrimOp.map] at heq
  | [_, _], hbody =>
    simp only [alpha, List.cons_append, List.nil_append, List.cons.injEq] at hbody
    obtain ⟨rfl, rfl, rfl, -⟩ := hbody
    obtain ⟨hy, -⟩ := hop
    rw [subjects_eq_empty hpre] at hy
    exact hy
  | _ :: _ :: _ :: _, hbody =>
    simp only [alpha, List.cons_append, List.cons.injEq] at hbody
    obtain ⟨-, -, -, h⟩ := hbody
    simp at h

end Cslib.Security.AccessControl.HRU.Tests
