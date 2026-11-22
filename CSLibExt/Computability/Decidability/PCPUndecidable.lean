/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Post correspondence problem is undecidable
-/
module

public import CSLibExt.Computability.Decidability.TM0Halting
public import CSLibExt.Computability.Decidability.StringRewriting
public import MathlibExt.Computability.TuringMachine.Translation.TM0Restrict
public import Mathlib.Tactic.DeriveFintype
public import Cslib.Foundations.Relation.Confluence

/-!
# The Post correspondence problem is undecidable

A single-tape machine (`Turing.TM0`) with finitely many states and tape symbols is simulated by a
finite string rewriting system (`rules M`) over the symbols `TMSym Γ Λ`: tape symbols, states, two
end markers `⊢ ⊣` and a halting symbol `H`.

* A configuration with state `q`, head symbol `h`, left part `L` and right part `R` is spelled
  `⊢ L q h R ⊣` (`spell`, `Spells`). Tape padding by blanks is absorbed by `ListBlank`.
* Each transition is one rule around the state symbol (`rulesFor`): `q a → q' b` writes,
  `q a c → a q' c` and `q a ⊣ → a q' _ ⊣` move right, `c q a → q' c a` and
  `⊢ q a → ⊢ q' _ a` move left. A halting pair gives `q a → H`, and `H` then erases the tape
  (`eraseRules`) down to `⊢ H ⊣` (`haltWord`).

`tm0HaltsOn_iff_derives`: `M` halts on `l` iff the start word rewrites to `⊢ H ⊣`. The forward
direction simulates the run step by step (`exists_step_of_spells`) and then erases. The backward
direction keeps an invariant (`Inv`): every word reachable from the start word spells a reachable
configuration, or else the machine halts and the word is in the erasing phase. A word of either
kind has exactly one state or halting symbol, and every rule has exactly one such symbol in its
left side, so a rewrite must happen at that symbol (`eq_of_append_cons_eq`) and follows the
machine.

Composed with the undecidable single-tape halting problem (`exists_not_tm2Decidable_tm0HaltsOn`,
restricted to a finite state type by `MetaMathlibExt.TM0Restrict.restrict`), the reduction to
MPCP (`Rewriting.manyOneReducible_sr_mpcp`) and the reduction of MPCP to PCP, this shows that
reachability for string rewriting, MPCP and PCP are undecidable over finite alphabets
(`exists_not_tm2Decidable_sr`, `exists_not_tm2Decidable_mpcp`, `exists_not_tm2Decidable_pcp`).

**Thue systems.** Every rule has exactly one control symbol on each side, so rewriting in either
direction keeps a single control symbol (`ctlCount_eq_of_step`). At a state symbol the rewrite is
determined by the machine (`nextState`), and the two erasures at the halting symbol commute
(`step_confluent`). The halting word rewrites to nothing (`not_step_haltWord`). So the rewrites from
words with one control symbol are confluent (`confluent_ctlStep`, by Mathlib's
`Relation.church_rosser`), and a start word that is equivalent to `⊢ H ⊣` under the symmetric
closure of the rules also rewrites to it (`tm0HaltsOn_iff_eqvGen`, by CSLib's
`Relation.ChurchRosser.normal_eqvGen_reflTransGen`). So a fixed finite Thue system has an
undecidable word problem (`exists_not_tm2Decidable_eqvGen`), and so does the uniform problem
(`exists_not_tm2Decidable_thueWP`).

## Main results

- `rules`, `tm0HaltsOn_iff_derives`, `manyOneReducible_tm0HaltsOn_sr`.
- `tm0HaltsOn_iff_eqvGen`, `manyOneReducible_tm0HaltsOn_eqvGen`,
  `exists_not_tm2Decidable_eqvGen`, `exists_not_tm2Decidable_thueWP`.
- `exists_not_tm2Decidable_sr`, `exists_not_tm2Decidable_mpcp`, `exists_not_tm2Decidable_pcp`.

## References

* E. L. Post, *A variant of a recursively unsolvable problem*, Bull. AMS 52 (1946), 264–268.
* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 5.15.
* Y. Forster, E. Heiter, G. Smolka, *Verification of PCP-related computational reductions in
  Coq*, ITP 2018, LNCS 10895, 253–269.
* E. L. Post, *Recursive unsolvability of a problem of Thue*, J. Symbolic Logic 12 (1947), 1–11.
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative
  systems*, Dokl. Akad. Nauk SSSR 55 (1947), 583–586.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.TMRewriting

open Turing Rewriting

/-- The symbols of the rewriting system simulating a single-tape machine. -/
inductive TMSym (Γ Λ : Type*) where
  /-- A tape symbol. -/
  | tape (a : Γ)
  /-- A state, written just left of the head symbol. -/
  | state (q : Λ)
  /-- The left end marker `⊢`. -/
  | lend
  /-- The right end marker `⊣`. -/
  | rend
  /-- The halting symbol `H`. -/
  | halt
  deriving DecidableEq, Fintype

open TMSym

/-! ### Words with one marked symbol -/

section Words

variable {Γ Λ : Type*}

/-- The state and halting symbols. -/
def IsCtl : TMSym Γ Λ → Prop
  | state _ => True
  | halt => True
  | _ => False

/-- A word with a single marked symbol is split at that symbol in only one way. -/
theorem eq_of_append_cons_eq {α : Type*} {P : α → Prop} {A B : List α} {y : α}
    (hA : ∀ s ∈ A, ¬P s) (hB : ∀ s ∈ B, ¬P s) :
    ∀ {C D : List α} {x : α}, P x → C ++ x :: D = A ++ y :: B → C = A ∧ x = y ∧ D = B := by
  induction A with
  | nil =>
    intro C D x hx h
    cases C with
    | nil => exact ⟨rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩
    | cons c C =>
      obtain ⟨-, hB'⟩ := List.cons.inj h
      exact absurd hx (hB x (hB' ▸ by simp))
  | cons a A ih =>
    intro C D x hx h
    cases C with
    | nil => exact absurd ((List.cons.inj h).1 ▸ hx) (hA a List.mem_cons_self)
    | cons c C =>
      obtain ⟨rfl, h'⟩ := List.cons.inj h
      obtain ⟨rfl, rfl, rfl⟩ := ih (fun s hs ↦ hA s (List.mem_cons_of_mem _ hs)) hx h'
      exact ⟨rfl, rfl, rfl⟩

theorem not_isCtl_tape (a : Γ) : ¬IsCtl (tape a : TMSym Γ Λ) := id

theorem notCtl_lend_map (L : List Γ) : ∀ s ∈ (lend :: L.map tape : List (TMSym Γ Λ)), ¬IsCtl s := by
  intro s hs
  simp only [List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | ⟨a, -, rfl⟩
  · exact id
  · exact id

theorem notCtl_map_rend (L : List Γ) :
    ∀ s ∈ (L.map tape ++ [rend] : List (TMSym Γ Λ)), ¬IsCtl s := by
  intro s hs
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hs
  rcases hs with ⟨a, -, rfl⟩ | rfl
  · exact id
  · exact id

/-- Splitting at the marked symbol of a rewrite site `u (p x s) v`. -/
theorem split_site {A B u v p s : List (TMSym Γ Λ)} {x y : TMSym Γ Λ}
    (hA : ∀ s ∈ A, ¬IsCtl s) (hB : ∀ s ∈ B, ¬IsCtl s) (hx : IsCtl x)
    (h : u ++ (p ++ x :: s) ++ v = A ++ y :: B) : u ++ p = A ∧ x = y ∧ s ++ v = B :=
  eq_of_append_cons_eq hA hB hx (by simpa [List.append_assoc] using h)

theorem eq_of_append_tape_eq {u : List (TMSym Γ Λ)} {c : Γ} {L : List Γ}
    (h : u ++ [tape c] = lend :: L.map tape) :
    ∃ L₀, L = L₀ ++ [c] ∧ u = lend :: L₀.map tape := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L₀, c₀, rfl⟩
  · cases u with
    | nil => cases h
    | cons x u => simp at h
  · have := List.append_inj' (s₁ := u) (s₂ := lend :: L₀.map tape) (t₁ := [tape c])
      (t₂ := [tape c₀]) (by simpa using h) rfl
    obtain ⟨h₁, h₂⟩ := this
    simp only [List.cons.injEq, TMSym.tape.injEq, and_true] at h₂
    exact ⟨L₀, by rw [h₂, List.concat_eq_append], h₁⟩

theorem eq_of_append_lend_eq {u : List (TMSym Γ Λ)} {L : List Γ}
    (h : u ++ [lend] = lend :: L.map tape) : L = [] ∧ u = [] := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L₀, c₀, rfl⟩
  · cases u with
    | nil => exact ⟨rfl, rfl⟩
    | cons x u => simp at h
  · have := List.append_inj' (s₁ := u) (s₂ := lend :: L₀.map tape) (t₁ := [lend])
      (t₂ := [tape c₀]) (by simpa using h) rfl
    simp at this

theorem eq_of_tape_cons_eq {c : Γ} {v : List (TMSym Γ Λ)} {Y : List Γ}
    (h : tape c :: v = Y.map tape ++ [rend]) : ∃ Y₀, Y = c :: Y₀ ∧ v = Y₀.map tape ++ [rend] := by
  cases Y with
  | nil => simp at h
  | cons d Y₀ =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq, TMSym.tape.injEq] at h
    exact ⟨Y₀, by rw [h.1], h.2⟩

theorem eq_of_rend_cons_eq {v : List (TMSym Γ Λ)} {Y : List Γ}
    (h : rend :: v = Y.map tape ++ [rend]) : Y = [] ∧ v = [] := by
  cases Y with
  | nil => exact ⟨rfl, (List.cons.inj h).2⟩
  | cons d Y₀ => simp at h

end Words

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-! ### Spelling configurations -/

/-- The word `⊢ L q h R ⊣` of a configuration; `Lw` is the left part in reading order. -/
def spell (q : Λ) (Lw : List Γ) (h : Γ) (R : List Γ) : List (TMSym Γ Λ) :=
  lend :: (Lw.map tape ++ state q :: tape h :: (R.map tape ++ [rend]))

/-- The target word `⊢ H ⊣`. -/
def haltWord : List (TMSym Γ Λ) := [lend, halt, rend]

/-- `w` spells the configuration `c`. -/
def Spells (w : List (TMSym Γ Λ)) (c : TM0.Cfg Γ Λ) : Prop :=
  ∃ q h Lw R, c = ⟨q, ⟨h, ListBlank.mk Lw.reverse, ListBlank.mk R⟩⟩ ∧ w = spell q Lw h R

/-- The start word of the input `l`. -/
def initWord (l : List Γ) : List (TMSym Γ Λ) := spell default [] l.headI l.tail

theorem spells_init (l : List Γ) : Spells (initWord l) (TM0.init l : TM0.Cfg Γ Λ) := by
  refine ⟨default, l.headI, [], l.tail, ?_, rfl⟩
  simp [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.head_mk, ListBlank.tail_mk]

/-! ### Steps of the machine -/

section Steps

variable {M : TM0.Machine Γ Λ}

theorem step_none {q : Λ} {h : Γ} {L R : ListBlank Γ} (hM : M q h = none) :
    TM0.step M ⟨q, ⟨h, L, R⟩⟩ = none := by
  simp [TM0.step, hM]

theorem step_write {q q' : Λ} {h b : Γ} {L R : ListBlank Γ} (hM : M q h = some (q', .write b)) :
    TM0.step M ⟨q, ⟨h, L, R⟩⟩ = some ⟨q', ⟨b, L, R⟩⟩ := by
  simp [TM0.step, hM, Tape.write]

theorem step_right {q q' : Λ} {h : Γ} {L R : ListBlank Γ} (hM : M q h = some (q', .move .right)) :
    TM0.step M ⟨q, ⟨h, L, R⟩⟩ = some ⟨q', ⟨R.head, L.cons h, R.tail⟩⟩ := by
  simp [TM0.step, hM, Tape.move]

theorem step_left {q q' : Λ} {h : Γ} {L R : ListBlank Γ} (hM : M q h = some (q', .move .left)) :
    TM0.step M ⟨q, ⟨h, L, R⟩⟩ = some ⟨q', ⟨L.head, L.tail, R.cons h⟩⟩ := by
  simp [TM0.step, hM, Tape.move]

end Steps

/-! ### The rules -/

variable [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ)

/-- The rules for the state `q` reading `a`. -/
noncomputable def rulesFor (q : Λ) (a : Γ) : List (Rule (TMSym Γ Λ)) :=
  match M q a with
  | none => [([state q, tape a], [halt])]
  | some (q', .write b) => [([state q, tape a], [state q', tape b])]
  | some (q', .move .right) => ([state q, tape a, rend], [tape a, state q', tape default, rend]) ::
      (Finset.univ : Finset Γ).toList.map fun c ↦
        ([state q, tape a, tape c], [tape a, state q', tape c])
  | some (q', .move .left) => ([lend, state q, tape a], [lend, state q', tape default, tape a]) ::
      (Finset.univ : Finset Γ).toList.map fun c ↦
        ([tape c, state q, tape a], [state q', tape c, tape a])

/-- The rules by which the halting symbol erases the tape. -/
noncomputable def eraseRules : List (Rule (TMSym Γ Λ)) :=
  (Finset.univ : Finset Γ).toList.flatMap fun c ↦
    [([tape c, halt], [halt]), ([halt, tape c], [halt])]

/-- The rewriting system simulating `M`. -/
noncomputable def rules : List (Rule (TMSym Γ Λ)) :=
  ((Finset.univ : Finset Λ).toList.flatMap fun q ↦
    (Finset.univ : Finset Γ).toList.flatMap fun a ↦ rulesFor M q a) ++ eraseRules

section Membership

variable {M}

theorem mem_rules_of_mem_rulesFor {q : Λ} {a : Γ} {r : Rule (TMSym Γ Λ)}
    (h : r ∈ rulesFor M q a) : r ∈ rules M := by
  simp only [rules, List.mem_append, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ,
    true_and]
  exact Or.inl ⟨q, a, h⟩

theorem mem_rules_halt {q : Λ} {a : Γ} (hM : M q a = none) :
    ([state q, tape a], [halt]) ∈ rules M :=
  mem_rules_of_mem_rulesFor (q := q) (a := a) (by simp [rulesFor, hM])

theorem mem_rules_write {q q' : Λ} {a b : Γ} (hM : M q a = some (q', .write b)) :
    ([state q, tape a], [state q', tape b]) ∈ rules M :=
  mem_rules_of_mem_rulesFor (q := q) (a := a) (by simp [rulesFor, hM])

theorem mem_rules_right_end {q q' : Λ} {a : Γ} (hM : M q a = some (q', .move .right)) :
    ([state q, tape a, rend], [tape a, state q', tape default, rend]) ∈ rules M :=
  mem_rules_of_mem_rulesFor (q := q) (a := a) (by simp [rulesFor, hM])

theorem mem_rules_right {q q' : Λ} {a : Γ} (c : Γ) (hM : M q a = some (q', .move .right)) :
    ([state q, tape a, tape c], [tape a, state q', tape c]) ∈ rules M :=
  mem_rules_of_mem_rulesFor (q := q) (a := a) (by simp [rulesFor, hM])

theorem mem_rules_left_end {q q' : Λ} {a : Γ} (hM : M q a = some (q', .move .left)) :
    ([lend, state q, tape a], [lend, state q', tape default, tape a]) ∈ rules M :=
  mem_rules_of_mem_rulesFor (q := q) (a := a) (by simp [rulesFor, hM])

theorem mem_rules_left {q q' : Λ} {a : Γ} (c : Γ) (hM : M q a = some (q', .move .left)) :
    ([tape c, state q, tape a], [state q', tape c, tape a]) ∈ rules M :=
  mem_rules_of_mem_rulesFor (q := q) (a := a) (by simp [rulesFor, hM])

theorem mem_rules_erase_left (c : Γ) : ([tape c, halt], [halt]) ∈ rules M := by
  simp [rules, eraseRules]

theorem mem_rules_erase_right (c : Γ) : ([halt, tape c], [halt]) ∈ rules M := by
  simp [rules, eraseRules]

/-- The eight kinds of rules. -/
theorem cases_of_mem_rules {l r : List (TMSym Γ Λ)} (h : (l, r) ∈ rules M) :
    (∃ q a, M q a = none ∧ l = [state q, tape a] ∧ r = [halt]) ∨
    (∃ q a q' b, M q a = some (q', .write b) ∧ l = [state q, tape a] ∧
      r = [state q', tape b]) ∨
    (∃ q a q', M q a = some (q', .move .right) ∧ l = [state q, tape a, rend] ∧
      r = [tape a, state q', tape default, rend]) ∨
    (∃ q a q' c, M q a = some (q', .move .right) ∧ l = [state q, tape a, tape c] ∧
      r = [tape a, state q', tape c]) ∨
    (∃ q a q', M q a = some (q', .move .left) ∧ l = [lend, state q, tape a] ∧
      r = [lend, state q', tape default, tape a]) ∨
    (∃ q a q' c, M q a = some (q', .move .left) ∧ l = [tape c, state q, tape a] ∧
      r = [state q', tape c, tape a]) ∨
    (∃ c, l = [tape c, halt] ∧ r = [halt]) ∨
    (∃ c, l = [halt, tape c] ∧ r = [halt]) := by
  simp only [rules, eraseRules, List.mem_append, List.mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, true_and] at h
  rcases h with ⟨q, a, h⟩ | ⟨c, h⟩
  · unfold rulesFor at h
    split at h
    · rename_i hM
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      exact Or.inl ⟨q, a, hM, h.1, h.2⟩
    · rename_i q' b hM
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      exact Or.inr (Or.inl ⟨q, a, q', b, hM, h.1, h.2⟩)
    · rename_i q' hM
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_map, Finset.mem_toList,
        Finset.mem_univ, true_and] at h
      rcases h with h | ⟨c, h⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, a, q', hM, h.1, h.2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, a, q', c, hM, h.1.symm, h.2.symm⟩)))
    · rename_i q' hM
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_map, Finset.mem_toList,
        Finset.mem_univ, true_and] at h
      rcases h with h | ⟨c, h⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, a, q', hM, h.1, h.2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨q, a, q', c, hM, h.1.symm, h.2.symm⟩)))))
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, h.1, h.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, h.1, h.2⟩))))))

theorem nonemptyRules_rules : NonemptyRules (rules M) := by
  rintro ⟨l, r⟩ h
  rcases cases_of_mem_rules h with
    ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl⟩ |
    ⟨_, _, _, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl⟩ | ⟨_, _, _, _, _, rfl, rfl⟩ |
    ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> simp

end Membership

/-! ### Simulating the machine -/

section Forward

variable {M}

/-- **One machine step is one rewrite.** -/
theorem exists_step_of_spells {w : List (TMSym Γ Λ)} {c c' : TM0.Cfg Γ Λ} (hw : Spells w c)
    (hc : c' ∈ TM0.step M c) : ∃ w', Step (rules M) w w' ∧ Spells w' c' := by
  obtain ⟨q, h, Lw, R, rfl, rfl⟩ := hw
  rcases hM : M q h with _ | ⟨q', s⟩
  · rw [step_none hM] at hc
    cases hc
  rcases s with (_ | _) | b
  · -- move left
    rw [step_left hM] at hc
    obtain rfl := (Option.some.inj hc).symm
    rcases List.eq_nil_or_concat Lw with rfl | ⟨Lw₀, c₀, rfl⟩
    · refine ⟨spell q' [] default (h :: R), ?_, ⟨q', default, [], h :: R, ?_, rfl⟩⟩
      · simpa [spell] using Step.mk [] (R.map tape ++ [rend]) (mem_rules_left_end hM)
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
    · refine ⟨spell q' Lw₀ c₀ (h :: R), ?_, ⟨q', c₀, Lw₀, h :: R, ?_, rfl⟩⟩
      · simpa [spell] using Step.mk (lend :: Lw₀.map tape) (R.map tape ++ [rend])
          (mem_rules_left c₀ hM)
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
  · -- move right
    rw [step_right hM] at hc
    obtain rfl := (Option.some.inj hc).symm
    rcases R with _ | ⟨c₀, R₀⟩
    · refine ⟨spell q' (Lw ++ [h]) default [], ?_, ⟨q', default, Lw ++ [h], [], ?_, rfl⟩⟩
      · simpa [spell] using Step.mk (lend :: Lw.map tape) [] (mem_rules_right_end hM)
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
    · refine ⟨spell q' (Lw ++ [h]) c₀ R₀, ?_, ⟨q', c₀, Lw ++ [h], R₀, ?_, rfl⟩⟩
      · simpa [spell] using Step.mk (lend :: Lw.map tape) (R₀.map tape ++ [rend])
          (mem_rules_right c₀ hM)
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
  · -- write
    rw [step_write hM] at hc
    obtain rfl := (Option.some.inj hc).symm
    refine ⟨spell q' Lw b R, ?_, ⟨q', b, Lw, R, rfl, rfl⟩⟩
    simpa [spell] using Step.mk (lend :: Lw.map tape) (R.map tape ++ [rend]) (mem_rules_write hM)

/-- The halting symbol erases the tape. -/
theorem derives_erase (X Y : List Γ) :
    Derives (rules M) (lend :: (X.map tape ++ halt :: (Y.map tape ++ [rend]))) haltWord := by
  have hY : ∀ (P : List (TMSym Γ Λ)) (Y : List Γ),
      Derives (rules M) (P ++ halt :: (Y.map tape ++ [rend])) (P ++ [halt, rend]) := by
    intro P Y
    induction Y with
    | nil => exact Derives.refl _
    | cons c Y ih =>
      refine (Derives.single ?_).trans ih
      simpa using Step.mk P (Y.map tape ++ [rend]) (mem_rules_erase_right (M := M) c)
  have hX : ∀ X : List Γ, Derives (rules M) (lend :: (X.map tape ++ [halt, rend])) haltWord := by
    intro X
    induction X using List.reverseRecOn with
    | nil => exact Derives.refl _
    | append_singleton X c ih =>
      refine (Derives.single ?_).trans ih
      simpa using Step.mk (lend :: X.map tape) [rend] (mem_rules_erase_left (M := M) c)
  simpa using (hY (lend :: X.map tape) Y).trans (hX X)

/-- A halted configuration rewrites to `⊢ H ⊣`. -/
theorem derives_of_spells_of_step_eq_none {w : List (TMSym Γ Λ)} {c : TM0.Cfg Γ Λ}
    (hw : Spells w c) (hc : TM0.step M c = none) : Derives (rules M) w haltWord := by
  obtain ⟨q, h, Lw, R, rfl, rfl⟩ := hw
  have hM : M q h = none := by
    cases e : M q h with
    | none => rfl
    | some p => simp [TM0.step, e] at hc
  refine (Derives.single ?_).trans (derives_erase Lw R)
  simpa [spell] using Step.mk (lend :: Lw.map tape) (R.map tape ++ [rend]) (mem_rules_halt hM)

theorem derives_of_reaches {c c' : TM0.Cfg Γ Λ} (h : StateTransition.Reaches (TM0.step M) c c')
    (hc' : TM0.step M c' = none) :
    ∀ {w : List (TMSym Γ Λ)}, Spells w c → Derives (rules M) w haltWord := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hw ↦ derives_of_spells_of_step_eq_none hw hc'
  | head hstep _ ih =>
    intro w hw
    obtain ⟨w', hww', hw'⟩ := exists_step_of_spells hw hstep
    exact (Derives.single hww').trans (ih hw')

end Forward

/-! ### The rewrites follow the machine -/

section Backward

/-- The invariant of words reachable from the start word `initWord l`. -/
def Inv (l : List Γ) (w : List (TMSym Γ Λ)) : Prop :=
  (∃ c, StateTransition.Reaches (TM0.step M) (TM0.init l) c ∧ Spells w c) ∨
    (TM0HaltsOn M l ∧ ∃ X Y : List Γ, w = lend :: (X.map tape ++ halt :: (Y.map tape ++ [rend])))

variable {M}

omit [Fintype Γ] [Fintype Λ] in
theorem tm0HaltsOn_of_reaches {l : List Γ} {c : TM0.Cfg Γ Λ}
    (h : StateTransition.Reaches (TM0.step M) (TM0.init l) c) (hc : TM0.step M c = none) :
    TM0HaltsOn M l :=
  Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (StateTransition.mem_eval.2 ⟨h, hc⟩)⟩

/-- **Every rewrite preserves the invariant.** -/
theorem Inv.step {l : List Γ} {w w' : List (TMSym Γ Λ)} (hw : Inv M l w)
    (hs : Step (rules M) w w') : Inv M l w' := by
  obtain ⟨u, v, hr⟩ := hs
  rename_i lhs rhs
  rcases hw with ⟨c, hreach, q₀, h, Lw, R, rfl, hw⟩ | ⟨hhalt, X, Y, hw⟩
  · -- the word spells a reachable configuration: `A q₀ B`
    have hA := notCtl_lend_map (Λ := Λ) Lw
    have hB : ∀ s ∈ (tape h :: (R.map tape ++ [rend]) : List (TMSym Γ Λ)), ¬IsCtl s := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact id
      · exact notCtl_map_rend R s hs
    have hw' : u ++ lhs ++ v = (lend :: Lw.map tape) ++ state q₀ :: (tape h :: (R.map tape ++
        [rend])) := by
      simpa [spell] using hw
    rcases cases_of_mem_rules hr with
      ⟨q, a, hM, rfl, rfl⟩ | ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ |
      ⟨q, a, q', c₀, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ | ⟨q, a, q', c₀, hM, rfl, rfl⟩ |
      ⟨c₀, rfl, rfl⟩ | ⟨c₀, rfl, rfl⟩
    · -- halting: the machine halts here, and the erasing phase starts
      obtain ⟨hu, hq, hsv⟩ := split_site (p := []) (x := state q) (s := [tape a]) hA hB trivial hw'
      obtain rfl := TMSym.state.inj hq
      simp only [List.append_nil] at hu
      subst hu
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨ha, rfl⟩ := List.cons.inj hsv
      obtain rfl := TMSym.tape.inj ha
      refine Or.inr ⟨tm0HaltsOn_of_reaches hreach (step_none hM), Lw, R, ?_⟩
      simp
    · -- write
      obtain ⟨hu, hq, hsv⟩ := split_site (p := []) (x := state q) (s := [tape a]) hA hB trivial hw'
      obtain rfl := TMSym.state.inj hq
      simp only [List.append_nil] at hu
      subst hu
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨ha, rfl⟩ := List.cons.inj hsv
      obtain rfl := TMSym.tape.inj ha
      refine Or.inl ⟨_, hreach.tail (step_write hM), q', b, Lw, R, rfl, ?_⟩
      simp [spell]
    · -- move right at the right end
      obtain ⟨hu, hq, hsv⟩ :=
        split_site (p := []) (x := state q) (s := [tape a, rend]) hA hB trivial hw'
      obtain rfl := TMSym.state.inj hq
      simp only [List.append_nil] at hu
      subst hu
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨ha, hsv₁⟩ := List.cons.inj hsv
      obtain rfl := TMSym.tape.inj ha
      obtain ⟨rfl, rfl⟩ := eq_of_rend_cons_eq hsv₁
      refine Or.inl ⟨_, hreach.tail (step_right hM), q', default, Lw ++ [a], [], ?_, ?_⟩
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
      · simp [spell]
    · -- move right
      obtain ⟨hu, hq, hsv⟩ :=
        split_site (p := []) (x := state q) (s := [tape a, tape c₀]) hA hB trivial hw'
      obtain rfl := TMSym.state.inj hq
      simp only [List.append_nil] at hu
      subst hu
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨ha, hsv₁⟩ := List.cons.inj hsv
      obtain rfl := TMSym.tape.inj ha
      obtain ⟨R₀, rfl, rfl⟩ := eq_of_tape_cons_eq hsv₁
      refine Or.inl ⟨_, hreach.tail (step_right hM), q', c₀, Lw ++ [a], R₀, ?_, ?_⟩
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
      · simp [spell]
    · -- move left at the left end
      obtain ⟨hup, hq, hsv⟩ :=
        split_site (p := [lend]) (x := state q) (s := [tape a]) hA hB trivial hw'
      obtain rfl := TMSym.state.inj hq
      obtain ⟨rfl, rfl⟩ := eq_of_append_lend_eq hup
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨ha, rfl⟩ := List.cons.inj hsv
      obtain rfl := TMSym.tape.inj ha
      refine Or.inl ⟨_, hreach.tail (step_left hM), q', default, [], a :: R, ?_, ?_⟩
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
      · simp [spell]
    · -- move left
      obtain ⟨hup, hq, hsv⟩ :=
        split_site (p := [tape c₀]) (x := state q) (s := [tape a]) hA hB trivial hw'
      obtain rfl := TMSym.state.inj hq
      obtain ⟨L₀, rfl, rfl⟩ := eq_of_append_tape_eq hup
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨ha, rfl⟩ := List.cons.inj hsv
      obtain rfl := TMSym.tape.inj ha
      refine Or.inl ⟨_, hreach.tail (step_left hM), q', c₀, L₀, a :: R, ?_, ?_⟩
      · simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
      · simp [spell]
    · obtain ⟨-, hq, -⟩ := split_site (p := [tape c₀]) (x := halt) (s := []) hA hB trivial hw'
      cases hq
    · obtain ⟨-, hq, -⟩ := split_site (p := []) (x := halt) (s := [tape c₀]) hA hB trivial hw'
      cases hq
  · -- the erasing phase: `A H B`
    have hA := notCtl_lend_map (Λ := Λ) X
    have hB := notCtl_map_rend (Λ := Λ) Y
    have hw' : u ++ lhs ++ v = (lend :: X.map tape) ++ halt :: (Y.map tape ++ [rend]) := by
      simpa using hw
    rcases cases_of_mem_rules hr with
      ⟨q, a, hM, rfl, rfl⟩ | ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ |
      ⟨q, a, q', c₀, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ | ⟨q, a, q', c₀, hM, rfl, rfl⟩ |
      ⟨c₀, rfl, rfl⟩ | ⟨c₀, rfl, rfl⟩
    · obtain ⟨-, hq, -⟩ :=
        split_site (p := []) (x := state q) (s := [tape a]) hA hB trivial hw'
      cases hq
    · obtain ⟨-, hq, -⟩ :=
        split_site (p := []) (x := state q) (s := [tape a]) hA hB trivial hw'
      cases hq
    · obtain ⟨-, hq, -⟩ :=
        split_site (p := []) (x := state q) (s := [tape a, rend]) hA hB trivial hw'
      cases hq
    · obtain ⟨-, hq, -⟩ :=
        split_site (p := []) (x := state q) (s := [tape a, tape c₀]) hA hB trivial hw'
      cases hq
    · obtain ⟨-, hq, -⟩ := split_site (p := [lend]) (x := state q) (s := [tape a]) hA hB trivial hw'
      cases hq
    · obtain ⟨-, hq, -⟩ :=
        split_site (p := [tape c₀]) (x := state q) (s := [tape a]) hA hB trivial hw'
      cases hq
    · obtain ⟨hup, -, hsv⟩ := split_site (p := [tape c₀]) (x := halt) (s := []) hA hB trivial hw'
      simp only [List.nil_append] at hsv
      subst hsv
      obtain ⟨X₀, rfl, rfl⟩ := eq_of_append_tape_eq hup
      exact Or.inr ⟨hhalt, X₀, Y, by simp⟩
    · obtain ⟨hu, -, hsv⟩ := split_site (p := []) (x := halt) (s := [tape c₀]) hA hB trivial hw'
      simp only [List.append_nil] at hu
      subst hu
      simp only [List.cons_append, List.nil_append] at hsv
      obtain ⟨Y₀, rfl, rfl⟩ := eq_of_tape_cons_eq hsv
      exact Or.inr ⟨hhalt, X, Y₀, by simp⟩

omit [Inhabited Λ] [Fintype Γ] [Fintype Λ] in
theorem not_spells_haltWord (c : TM0.Cfg Γ Λ) : ¬Spells (haltWord : List (TMSym Γ Λ)) c := by
  rintro ⟨q, h, Lw, R, -, hw⟩
  have := congrArg List.length hw
  simp [haltWord, spell] at this
  omega

end Backward

/-- **A single-tape machine halts iff its start word rewrites to `⊢ H ⊣`.** -/
theorem tm0HaltsOn_iff_derives (l : List Γ) :
    TM0HaltsOn M l ↔ Derives (rules M) (initWord l) haltWord := by
  constructor
  · intro h
    obtain ⟨_, hb⟩ := Part.dom_iff_mem.mp h
    obtain ⟨c, hc, -⟩ := (Part.mem_map_iff _).mp hb
    obtain ⟨hreach, hstop⟩ := StateTransition.mem_eval.1 hc
    exact derives_of_reaches hreach hstop (spells_init l)
  · intro h
    have hinv : ∀ {w}, Derives (rules M) (initWord l) w → Inv M l w := by
      intro w hw
      induction hw with
      | refl => exact Or.inl ⟨_, Relation.ReflTransGen.refl, spells_init l⟩
      | tail _ hs ih => exact ih.step hs
    rcases hinv h with ⟨c, -, hc⟩ | ⟨hhalt, -⟩
    · exact absurd hc (not_spells_haltWord c)
    · exact hhalt

/-! ### The reductions -/

omit [Fintype Γ] [Fintype Λ] in
theorem primrec_initWord [Finite Γ] [Primcodable Γ] [Primcodable (TMSym Γ Λ)] :
    Primrec (initWord (Γ := Γ) (Λ := Λ)) := by
  have htape : Primrec (tape : Γ → TMSym Γ Λ) := Primrec.dom_finite _
  refine (Primrec.list_cons.comp (Primrec.const lend) (Primrec.list_cons.comp
    (Primrec.const (state default)) (Primrec.list_cons.comp (htape.comp Primrec.list_headI)
      (Primrec.list_append.comp (Primrec.list_map Primrec.list_tail (htape.comp Primrec.snd).to₂)
        (Primrec.const [rend]))))).of_eq fun l ↦ ?_
  simp [initWord, spell]

omit [Fintype Γ] [Fintype Λ] in
/-- **Single-tape halting many-one reduces to string rewriting reachability**, with rules with
nonempty sides. -/
theorem manyOneReducible_tm0HaltsOn_sr [Finite Γ] [Finite Λ] [Primcodable Γ]
    [Primcodable (TMSym Γ Λ)] :
    ManyOneReducible (TM0HaltsOn M) fun I : List (Rule (TMSym Γ Λ)) × List (TMSym Γ Λ) ×
      List (TMSym Γ Λ) ↦ NonemptyRules I.1 ∧ SR I :=
  let _ := Fintype.ofFinite Γ
  let _ := Fintype.ofFinite Λ
  ⟨fun l ↦ (rules M, initWord l, haltWord),
    (Primrec.pair (Primrec.const _) (Primrec.pair primrec_initWord (Primrec.const _))).to_comp,
    fun l ↦ ⟨fun h ↦ ⟨nonemptyRules_rules, (tm0HaltsOn_iff_derives M l).mp h⟩,
      fun h ↦ (tm0HaltsOn_iff_derives M l).mpr h.2⟩⟩

end Cslib.Decidability.TMRewriting

/-! ### Undecidability -/

namespace Cslib.Decidability

open Turing Rewriting TMRewriting

/-- **Reachability for string rewriting is undecidable**, over a finite alphabet and for rules
with nonempty sides. -/
theorem exists_not_tm2Decidable_sr :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
      ¬TM2Decidable fun I : List (Rule α) × List α × List α ↦ NonemptyRules I.1 ∧ SR I := by
  obtain ⟨Γ, Λ, _, _, _, _, _, M, S, hS, hund⟩ := exists_not_tm2Decidable_tm0HaltsOn
  classical
  let _ : Inhabited (↑S : Set Λ) := ⟨⟨default, hS.1⟩⟩
  let _ : Fintype (↑S : Set Λ) := inferInstanceAs (Fintype {x // x ∈ S})
  let _ : Primcodable (TMSym Γ (↑S : Set Λ)) := primcodableOfFintype _
  have hM : TM0HaltsOn (MetaMathlibExt.TM0Restrict.restrict hS) = TM0HaltsOn M := funext fun l ↦ by
    simp only [TM0HaltsOn, MetaMathlibExt.TM0Restrict.eval_restrict hS rfl l]
  refine ⟨TMSym Γ (↑S : Set Λ), inferInstance, inferInstance, fun h ↦ hund ?_⟩
  rw [← hM]
  exact tm2Decidable_of_manyOneReducible
    (manyOneReducible_tm0HaltsOn_sr (MetaMathlibExt.TM0Restrict.restrict hS)) h

/-- **MPCP is undecidable**, over a finite alphabet and on instances with nonempty words. -/
theorem exists_not_tm2Decidable_mpcp :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
      ¬TM2Decidable fun P : List (Post.Domino α) ↦ Post.NonemptyWords P ∧ Post.MPCP P := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_sr
  exact ⟨Post.Sym α, inferInstance, inferInstance, fun hd ↦
    h (tm2Decidable_of_manyOneReducible manyOneReducible_sr_mpcp hd)⟩

/-- **The Post correspondence problem is undecidable** over a finite alphabet. -/
theorem exists_not_tm2Decidable_pcp :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α), ¬TM2Decidable (Post.PCP (α := α)) := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_sr
  exact ⟨Post.Sym (Post.Sym α), inferInstance, inferInstance, fun hd ↦
    h (tm2Decidable_of_manyOneReducible manyOneReducible_sr_pcp hd)⟩

end Cslib.Decidability

/-! ### Thue systems -/

namespace Cslib.Decidability.TMRewriting

open Turing Rewriting TMSym Relation

variable {Γ Λ : Type*}

/-- The state and halting symbols, as a Boolean test. -/
def isCtlB : TMSym Γ Λ → Bool
  | state _ => true
  | halt => true
  | _ => false

theorem isCtlB_iff {x : TMSym Γ Λ} : isCtlB x = true ↔ IsCtl x := by
  cases x <;> simp [isCtlB, IsCtl]

/-- The number of state and halting symbols in a word. -/
def ctlCount (w : List (TMSym Γ Λ)) : ℕ := w.countP isCtlB

theorem ctlCount_append (u v : List (TMSym Γ Λ)) :
    ctlCount (u ++ v) = ctlCount u + ctlCount v := List.countP_append ..

theorem notCtl_of_ctlCount_eq_zero {w : List (TMSym Γ Λ)} (h : ctlCount w = 0) :
    ∀ y ∈ w, ¬IsCtl y := fun y hy hc ↦
  (List.countP_eq_zero.mp h) y hy (isCtlB_iff.mpr hc)

/-- A word with exactly one control symbol splits at it. -/
theorem exists_split_of_ctlCount_eq_one :
    ∀ {w : List (TMSym Γ Λ)}, ctlCount w = 1 → ∃ pre x post, w = pre ++ x :: post ∧ IsCtl x ∧
      (∀ y ∈ pre, ¬IsCtl y) ∧ (∀ y ∈ post, ¬IsCtl y)
  | [], h => by simp [ctlCount] at h
  | y :: w, h => by
    by_cases hy : isCtlB y = true
    · have hw : ctlCount w = 0 := by
        simp only [ctlCount, List.countP_cons, hy, ite_true] at h
        simpa [ctlCount] using h
      exact ⟨[], y, w, rfl, isCtlB_iff.mp hy, by simp, notCtl_of_ctlCount_eq_zero hw⟩
    · have hw : ctlCount w = 1 := by
        simp only [ctlCount, List.countP_cons, hy] at h
        simpa [ctlCount] using h
      obtain ⟨pre, x, post, rfl, hx, hpre, hpost⟩ := exists_split_of_ctlCount_eq_one hw
      refine ⟨y :: pre, x, post, rfl, hx, fun z hz ↦ ?_, hpost⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact fun hc ↦ hy (isCtlB_iff.mpr hc)
      · exact hpre z hz

variable [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ)

/-- The successor of a word `pre q post` under the rules for state `q`, if any. -/
def nextState (pre : List (TMSym Γ Λ)) (q : Λ) : List (TMSym Γ Λ) → Option (List (TMSym Γ Λ))
  | tape a :: post' =>
    match M q a with
    | none => some (pre ++ halt :: post')
    | some (q', .write b) => some (pre ++ state q' :: tape b :: post')
    | some (q', .move .right) =>
      match post' with
      | rend :: post'' => some (pre ++ tape a :: state q' :: tape default :: rend :: post'')
      | tape c :: post'' => some (pre ++ tape a :: state q' :: tape c :: post'')
      | _ => none
    | some (q', .move .left) =>
      match pre.getLast? with
      | some lend => some (pre.dropLast ++ lend :: state q' :: tape default :: tape a :: post')
      | some (tape c) => some (pre.dropLast ++ state q' :: tape c :: tape a :: post')
      | _ => none
  | _ => none

variable {M}

/-- **A rewrite at the control symbol.** At a state symbol the result is `nextState`; at the
halting symbol it erases the letter on the left or the letter on the right. -/
theorem step_result {pre post w' : List (TMSym Γ Λ)} {x : TMSym Γ Λ} (hx : IsCtl x)
    (hpre : ∀ y ∈ pre, ¬IsCtl y) (hpost : ∀ y ∈ post, ¬IsCtl y)
    (h : Step (rules M) (pre ++ x :: post) w') :
    (∃ q, x = state q ∧ nextState M pre q post = some w') ∨
      (x = halt ∧ ((∃ pre' c, pre = pre' ++ [tape c] ∧ w' = pre' ++ halt :: post) ∨
        (∃ c post', post = tape c :: post' ∧ w' = pre ++ halt :: post'))) := by
  generalize hw : pre ++ x :: post = w at h
  rcases h with @⟨l, r, u, v, hr⟩
  rcases cases_of_mem_rules hr with
    ⟨q, a, hM, rfl, rfl⟩ | ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ |
    ⟨q, a, q', c₀, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ | ⟨q, a, q', c₀, hM, rfl, rfl⟩ |
    ⟨c₀, rfl, rfl⟩ | ⟨c₀, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := []) (x := state q) (s := [tape a]) hpre hpost
      trivial hw.symm
    exact Or.inl ⟨q, rfl, by simp [nextState, hM]⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := []) (x := state q) (s := [tape a]) hpre hpost
      trivial hw.symm
    exact Or.inl ⟨q, rfl, by simp [nextState, hM]⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := []) (x := state q) (s := [tape a, rend]) hpre
      hpost trivial hw.symm
    exact Or.inl ⟨q, rfl, by simp [nextState, hM]⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := []) (x := state q) (s := [tape a, tape c₀]) hpre
      hpost trivial hw.symm
    exact Or.inl ⟨q, rfl, by simp [nextState, hM]⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := [lend]) (x := state q) (s := [tape a]) hpre hpost
      trivial hw.symm
    exact Or.inl ⟨q, rfl, by simp [nextState, hM]⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := [tape c₀]) (x := state q) (s := [tape a]) hpre
      hpost trivial hw.symm
    exact Or.inl ⟨q, rfl, by simp [nextState, hM]⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := [tape c₀]) (x := halt) (s := []) hpre hpost
      trivial hw.symm
    exact Or.inr ⟨rfl, Or.inl ⟨u, c₀, rfl, by simp⟩⟩
  · obtain ⟨rfl, rfl, rfl⟩ := split_site (p := []) (x := halt) (s := [tape c₀]) hpre hpost
      trivial hw.symm
    exact Or.inr ⟨rfl, Or.inr ⟨c₀, v, rfl, by simp⟩⟩

/-- Every rewrite keeps the number of control symbols. -/
theorem ctlCount_eq_of_step {w w' : List (TMSym Γ Λ)} (h : Step (rules M) w w') :
    ctlCount w = ctlCount w' := by
  rcases h with @⟨l, r, u, v, hr⟩
  have hlr : ctlCount l = ctlCount r := by
    rcases cases_of_mem_rules hr with
      ⟨q, a, hM, rfl, rfl⟩ | ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ |
      ⟨q, a, q', c₀, hM, rfl, rfl⟩ | ⟨q, a, q', hM, rfl, rfl⟩ | ⟨q, a, q', c₀, hM, rfl, rfl⟩ |
      ⟨c₀, rfl, rfl⟩ | ⟨c₀, rfl, rfl⟩ <;> rfl
  simp only [ctlCount_append, hlr]

/-- **Local confluence on words with one control symbol.** Rewriting at a state symbol is
deterministic, and the two erasures at the halting symbol commute. -/
theorem step_confluent {w w₁ w₂ : List (TMSym Γ Λ)} (hc : ctlCount w = 1)
    (h₁ : Step (rules M) w w₁) (h₂ : Step (rules M) w w₂) :
    ∃ d, ReflGen (Step (rules M)) w₁ d ∧ ReflTransGen (Step (rules M)) w₂ d := by
  obtain ⟨pre, x, post, rfl, hx, hpre, hpost⟩ := exists_split_of_ctlCount_eq_one hc
  have heq : w₁ = w₂ → ∃ d, ReflGen (Step (rules M)) w₁ d ∧ ReflTransGen (Step (rules M)) w₂ d :=
    fun h ↦ ⟨w₁, ReflGen.refl, h ▸ ReflTransGen.refl⟩
  rcases step_result hx hpre hpost h₁ with ⟨q₁, rfl, hq₁⟩ | ⟨rfl, hL₁ | hR₁⟩ <;>
    rcases step_result hx hpre hpost h₂ with ⟨q₂, hq, hq₂⟩ | ⟨hh, hL₂ | hR₂⟩
  · obtain rfl := TMSym.state.inj hq
    exact heq (Option.some.inj (hq₁.symm.trans hq₂))
  · cases hh
  · cases hh
  · cases hq
  · obtain ⟨p₁, c₁, rfl, rfl⟩ := hL₁
    obtain ⟨p₂, c₂, hp, rfl⟩ := hL₂
    obtain ⟨rfl, hc'⟩ := List.append_inj' hp rfl
    obtain rfl := TMSym.tape.inj (List.cons.inj hc').1
    exact heq rfl
  · -- erase on the left, then on the right
    obtain ⟨p₁, c₁, rfl, rfl⟩ := hL₁
    obtain ⟨c₂, q₂, rfl, rfl⟩ := hR₂
    refine ⟨p₁ ++ halt :: q₂, ReflGen.single ?_, ReflTransGen.single ?_⟩
    · simpa using Step.mk p₁ q₂ (mem_rules_erase_right (M := M) c₂)
    · simpa using Step.mk p₁ q₂ (mem_rules_erase_left (M := M) c₁)
  · cases hq
  · -- erase on the right, then on the left
    obtain ⟨c₁, q₁, rfl, rfl⟩ := hR₁
    obtain ⟨p₂, c₂, rfl, rfl⟩ := hL₂
    refine ⟨p₂ ++ halt :: q₁, ReflGen.single ?_, ReflTransGen.single ?_⟩
    · simpa using Step.mk p₂ q₁ (mem_rules_erase_left (M := M) c₂)
    · simpa using Step.mk p₂ q₁ (mem_rules_erase_right (M := M) c₁)
  · obtain ⟨c₁, q₁, rfl, rfl⟩ := hR₁
    obtain ⟨c₂, q₂, hp, rfl⟩ := hR₂
    obtain ⟨hc', rfl⟩ := List.cons.inj hp
    obtain rfl := TMSym.tape.inj hc'
    exact heq rfl

/-- The halting word `⊢ H ⊣` rewrites to nothing. -/
theorem not_step_haltWord (w : List (TMSym Γ Λ)) : ¬Step (rules M) haltWord w := by
  intro h
  rcases step_result (pre := [lend]) (x := halt) (post := [rend]) trivial (by simp [IsCtl])
    (by simp [IsCtl]) h with ⟨q, hq, -⟩ | ⟨-, ⟨p, c, hp, -⟩ | ⟨c, p, hp, -⟩⟩
  · cases hq
  · have := congrArg List.getLast? hp
    simp at this
  · cases hp

omit [Fintype Γ] [Fintype Λ] in
theorem ctlCount_initWord (l : List Γ) : ctlCount (initWord l : List (TMSym Γ Λ)) = 1 := by
  have h0 : List.countP isCtlB ((l.tail.map tape : List (TMSym Γ Λ)) ++ [rend]) = 0 :=
    List.countP_eq_zero.mpr fun y hy ↦ by
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
        simp [isCtlB]
      · rw [List.mem_singleton.mp hy]
        simp [isCtlB]
  change List.countP isCtlB (lend :: ((([] : List Γ).map tape) ++ state default :: tape l.headI ::
    ((l.tail.map tape : List (TMSym Γ Λ)) ++ [rend]))) = 1
  rw [List.countP_cons, List.map_nil, List.nil_append, List.countP_cons, List.countP_cons, h0]
  rfl

variable (M) in
/-- A rewrite from a word with exactly one control symbol. -/
def CtlStep (w w' : List (TMSym Γ Λ)) : Prop := ctlCount w = 1 ∧ Step (rules M) w w'

/-- A Thue chain from a word with one control symbol consists of such rewrites. -/
theorem eqvGen_ctlStep {w w' : List (TMSym Γ Λ)} (h : EqvGen (Step (rules M)) w w')
    (hw : ctlCount w = 1) : EqvGen (CtlStep M) w w' := by
  have key : ∀ {x y}, EqvGen (Step (rules M)) x y →
      (ctlCount x = 1 ↔ ctlCount y = 1) ∧ (ctlCount x = 1 → EqvGen (CtlStep M) x y) := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      exact ⟨by rw [ctlCount_eq_of_step hr], fun hx ↦ EqvGen.rel _ _ ⟨hx, hr⟩⟩
    | refl x => exact ⟨Iff.rfl, fun _ ↦ EqvGen.refl _⟩
    | symm x y _ ih => exact ⟨ih.1.symm, fun hy ↦ EqvGen.symm _ _ (ih.2 (ih.1.mpr hy))⟩
    | trans x y z _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.trans ih₂.1, fun hx ↦ EqvGen.trans _ _ _ (ih₁.2 hx) (ih₂.2 (ih₁.1.mp hx))⟩
  exact (key h).2 hw

/-- **The rewrites from words with one control symbol are confluent**, by Mathlib's
Church–Rosser lemma from `step_confluent`. -/
theorem confluent_ctlStep : Confluent (CtlStep M) := by
  have hlift : ∀ {x y}, ctlCount x = 1 → ReflTransGen (Step (rules M)) x y →
      ReflTransGen (CtlStep M) x y := by
    intro x y hx hxy
    induction hxy using ReflTransGen.head_induction_on with
    | refl => exact ReflTransGen.refl
    | head hst _ ih =>
      exact ReflTransGen.head ⟨hx, hst⟩ (ih (by rw [← ctlCount_eq_of_step hst, hx]))
  intro a b c hab hac
  refine church_rosser (fun x y z hxy hxz ↦ ?_) hab hac
  obtain ⟨hx, hxy⟩ := hxy
  obtain ⟨d, hyd, hzd⟩ := step_confluent hx hxy hxz.2
  refine ⟨d, ?_, hlift (by rw [← ctlCount_eq_of_step hxz.2, hx]) hzd⟩
  rcases hyd with _ | hyd
  · exact ReflGen.refl
  · exact ReflGen.single ⟨by rw [← ctlCount_eq_of_step hxy, hx], hyd⟩

/-- **A single-tape machine halts iff its start word is equivalent to `⊢ H ⊣`** under the Thue
system of `rules M`. -/
theorem tm0HaltsOn_iff_eqvGen (l : List Γ) :
    TM0HaltsOn M l ↔ EqvGen (Step (rules M)) (initWord l) haltWord := by
  rw [tm0HaltsOn_iff_derives]
  refine ⟨eqvGen_of_derives, fun h ↦ ?_⟩
  have hn : Normal (CtlStep M) haltWord := fun ⟨w, _, hw⟩ ↦ not_step_haltWord w hw
  exact ReflTransGen.mono (r := CtlStep M) (p := Step (rules M)) (fun _ _ h ↦ h.2) _ _
    (ChurchRosser.normal_eqvGen_reflTransGen confluent_ctlStep.to_churchRosser hn
      (eqvGen_ctlStep h (ctlCount_initWord l)))

variable (M) in
/-- **Single-tape halting many-one reduces to the word problem of the fixed Thue system
`rules M`.** -/
theorem manyOneReducible_tm0HaltsOn_eqvGen [Primcodable Γ] [Primcodable (TMSym Γ Λ)] :
    ManyOneReducible (TM0HaltsOn M)
      fun p : List (TMSym Γ Λ) × List (TMSym Γ Λ) ↦ EqvGen (Step (rules M)) p.1 p.2 :=
  ⟨fun l ↦ (initWord l, haltWord), (Primrec.pair primrec_initWord (Primrec.const _)).to_comp,
    fun l ↦ tm0HaltsOn_iff_eqvGen l⟩

end Cslib.Decidability.TMRewriting

namespace Cslib.Decidability

open Turing Rewriting TMRewriting Relation

/-- **Some finite Thue system has an undecidable word problem** (Post, Markov): over a finite
alphabet, a fixed finite list of rules `R` whose equivalence `x ~ y` is undecidable. -/
theorem exists_not_tm2Decidable_eqvGen :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α) (R : List (Rule α)),
      ¬TM2Decidable fun p : List α × List α ↦ EqvGen (Step R) p.1 p.2 := by
  obtain ⟨Γ, Λ, _, _, _, _, _, M, S, hS, hund⟩ := exists_not_tm2Decidable_tm0HaltsOn
  classical
  let _ : Inhabited (↑S : Set Λ) := ⟨⟨default, hS.1⟩⟩
  let _ : Fintype (↑S : Set Λ) := inferInstanceAs (Fintype {x // x ∈ S})
  let _ : Primcodable (TMSym Γ (↑S : Set Λ)) := primcodableOfFintype _
  have hM : TM0HaltsOn (MetaMathlibExt.TM0Restrict.restrict hS) = TM0HaltsOn M := funext fun l ↦ by
    simp only [TM0HaltsOn, MetaMathlibExt.TM0Restrict.eval_restrict hS rfl l]
  refine ⟨TMSym Γ (↑S : Set Λ), inferInstance, inferInstance,
    rules (MetaMathlibExt.TM0Restrict.restrict hS), fun h ↦ hund ?_⟩
  rw [← hM]
  exact tm2Decidable_of_manyOneReducible
    (manyOneReducible_tm0HaltsOn_eqvGen (MetaMathlibExt.TM0Restrict.restrict hS)) h

/-- **The uniform word problem for Thue systems is undecidable**, over a finite alphabet. -/
theorem exists_not_tm2Decidable_thueWP :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α), ¬TM2Decidable (ThueWP (α := α)) := by
  obtain ⟨α, _, _, R, h⟩ := exists_not_tm2Decidable_eqvGen
  exact ⟨α, inferInstance, inferInstance, fun hd ↦ h (tm2Decidable_of_manyOneReducible
    ⟨fun p ↦ (R, p), (Primrec.pair (Primrec.const R) Primrec.id).to_comp, fun _ ↦ Iff.rfl⟩ hd)⟩

end Cslib.Decidability
