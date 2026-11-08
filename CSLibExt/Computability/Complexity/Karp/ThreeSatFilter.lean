/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatCheck
public import CSLibExt.Computability.Complexity.Karp.ThreeSat

/-!
# A clause-length filter on the SAT token stack

A `TM2` machine for the 3SAT verifier: on the token stack `(toks φ).reverse` of the SAT verifier
(`SatVerifierSpec`) it checks that every clause has at most three literals (`is3`). It walks the
token stack onto a side stack `U`, counting literals since the last `cl` token, and on success
moves everything back, so the stacks end as they started (`run`). With `cap = false` it never
fails, which lets one host machine serve both SAT and 3SAT.

`run`: from `start`, reach `pass` if `!cap || is3 φ` and `fail` otherwise, within
`2 |toks φ| + 2` steps, with the stacks unchanged on `pass`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.Filter3

open Turing MetaMathlibExt TM2Program Function Cslib.CookLevin Cslib.Logic.PL Computability
open Cslib.Complexity.SatVerifier Cslib.Complexity.SatVerifier.Check

/-- Stacks: the token stack `T` and the side stack `U`. -/
inductive K | T | U
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.T, .U], by decide⟩
  complete := fun k => by cases k <;> decide

/-- Labels: `w0`-`w3` walk the token stack having seen that many literals of the current clause
(`w3`: three or more); `back` moves the tokens back; `pass` and `fail` are the exits. -/
inductive Lab | w0 | w1 | w2 | w3 | back | pass | fail
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.w0, .w1, .w2, .w3, .back, .pass, .fail], by decide⟩
  complete := fun l => by cases l <;> decide

/-- Statements of the filter. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- The walking label after `n` literals of the current clause. -/
def wl : ℕ → Lab
  | 0 => .w0
  | 1 => .w1
  | 2 => .w2
  | _ => .w3

/-- The label after one more literal; past three literals a capped filter fails. -/
def nxt (cap : Bool) : Lab → Lab
  | .w0 => .w1
  | .w1 => .w2
  | .w2 => .w3
  | .w3 => if cap then .fail else .w3
  | l => l

open TM2.Stmt in
/-- If the top of `a` is `s`, move it to `b` and go to `l`; otherwise run `q`. -/
def mvIf (a b : K) (s : Sym) (l : Lab) (q : Stmt) : Stmt :=
  peek a (fun _ o => decide (o = some s)) <| branch id
    (pop a (fun v _ => v) <| push b (fun _ => s) <| goto fun _ => l) q

open TM2.Stmt in
/-- One step of the walk at walking label `l`: an empty `T` ends the walk; a token moves to `U`,
`cl` resetting the literal count and `lit` advancing it. -/
def walk (cap : Bool) (l : Lab) : Stmt :=
  peek .T (fun _ o => o.isNone) <| branch id (goto fun _ => .back) <|
    mvIf .T .U .cl .w0 <| mvIf .T .U (.lit true) (nxt cap l) <|
    mvIf .T .U (.lit false) (nxt cap l) <| mvIf .T .U (.bit true) l <|
    mvIf .T .U (.bit false) l <| goto fun _ => .fail

open TM2.Stmt in
/-- The program. -/
def prog (cap : Bool) : Lab → Stmt
  | .w0 => walk cap .w0
  | .w1 => walk cap .w1
  | .w2 => walk cap .w2
  | .w3 => walk cap .w3
  | .back => peek .U (fun _ o => o.isNone) <| branch id (goto fun _ => .pass) <|
      mvIf .U .T .cl .back <| mvIf .U .T (.lit true) .back <| mvIf .U .T (.lit false) .back <|
      mvIf .U .T (.bit true) .back <| mvIf .U .T (.bit false) .back <| goto fun _ => .fail
  | .pass => halt
  | .fail => halt

/-- The start label. -/
def start : Lab := .w0

/-- Symbols that occur on token stacks. -/
def IsTok : Sym → Prop
  | .cl | .lit _ | .bit _ => True
  | _ => False

/-- The label a walking label moves to on a token. -/
def tgt (cap : Bool) (l : Lab) : Sym → Lab
  | .cl => .w0
  | .lit _ => nxt cap l
  | _ => l

theorem nxt_wl (cap : Bool) (n : ℕ) :
    nxt cap (wl n) = if cap && 3 ≤ n then .fail else wl (n + 1) := by
  rcases n with _ | _ | _ | n <;> cases cap <;> simp [wl, nxt]

theorem prog_wl (cap : Bool) (n : ℕ) : prog cap (wl n) = walk cap (wl n) := by
  rcases n with _ | _ | _ | n <;> rfl

/-- The stacks, given the token stack and the side stack. -/
def st (t u : List Sym) : ∀ _ : K, List Sym
  | .T => t
  | .U => u

theorem st_eta (S : ∀ _ : K, List Sym) : st (S .T) (S .U) = S := by
  funext k; cases k <;> rfl

/-- One walking step on a token. -/
theorem walk_step (cap : Bool) (n : ℕ) (s : Sym) (hs : IsTok s) (R U : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some (wl n), v, st (s :: R) U⟩
      ⟨some (tgt cap (wl n) s), true, st R (s :: U)⟩ := by
  refine Run.single ?_
  rw [prog_wl]
  have e : ∀ t u : List Sym, update (update (st (s :: R) U) .T t) .U u = st t u := by
    intro t u; funext k; cases k <;> rfl
  rcases s with b | p | _ | _ | _ <;> simp only [IsTok] at hs
  · cases b <;> simp [walk, mvIf, TM2.stepAux, st, tgt, e]
  · cases p <;> simp [walk, mvIf, TM2.stepAux, st, tgt, e]
  · simp [walk, mvIf, TM2.stepAux, st, tgt, e]

/-- A walk over bits keeps the label. -/
theorem walk_bits (cap : Bool) (n : ℕ) (R : List Sym) :
    ∀ (bs : List Bool) (U : List Sym) (v : Bool), ∃ v',
      Run (prog cap) bs.length ⟨some (wl n), v, st (bs.map Sym.bit ++ R) U⟩
        ⟨some (wl n), v', st R ((bs.map Sym.bit).reverse ++ U)⟩ := by
  intro bs
  induction bs with
  | nil => intro U v; exact ⟨v, Run.zero _⟩
  | cons b bs ih =>
      intro U v
      obtain ⟨v₂, r₂⟩ := ih (.bit b :: U) true
      refine ⟨v₂, ?_⟩
      have h := ((walk_step cap n (.bit b) trivial (bs.map Sym.bit ++ R) U v).trans r₂).of_eq
        (show 1 + bs.length = (b :: bs).length by simp [Nat.add_comm])
      simpa using h

theorem litRev_ne_nil (l : ℕ × Bool) : litRev l ≠ [] := by simp [litRev]

/-- A walk over one literal's tokens advances the literal count. -/
theorem walk_lit (cap : Bool) (n : ℕ) (hn : (cap && 3 ≤ n) = false) (l : ℕ × Bool)
    (R U : List Sym) (v : Bool) : ∃ v',
      Run (prog cap) (litRev l).length ⟨some (wl n), v, st (litRev l ++ R) U⟩
        ⟨some (wl (n + 1)), v', st R ((litRev l).reverse ++ U)⟩ := by
  have h1 := walk_step cap n (.lit l.2) trivial (((encodeNat l.1).map Sym.bit).reverse ++ R) U v
  simp only [tgt, nxt_wl, hn, Bool.false_eq_true, ↓reduceIte] at h1
  obtain ⟨v₂, r₂⟩ := walk_bits cap (n + 1) R (encodeNat l.1).reverse (.lit l.2 :: U) true
  rw [List.map_reverse] at r₂
  refine ⟨v₂, ?_⟩
  have h := (h1.trans r₂).of_eq (show 1 + (encodeNat l.1).reverse.length = (litRev l).length by
    simp [litRev, Nat.add_comm])
  simpa [litRev, List.map_reverse] using h

/-- A capped walk fails on a fourth literal. -/
theorem walk_lit_fail (n : ℕ) (hn : 3 ≤ n) (l : ℕ × Bool) (R U : List Sym) (v : Bool) :
    ∃ v' S', Run (prog true) 1 ⟨some (wl n), v, st (litRev l ++ R) U⟩ ⟨some .fail, v', S'⟩ := by
  have h1 := walk_step true n (.lit l.2) trivial (((encodeNat l.1).map Sym.bit).reverse ++ R) U v
  simp only [tgt, nxt_wl, Bool.true_and, decide_eq_true hn, ↓reduceIte] at h1
  exact ⟨_, _, by simpa [litRev] using h1⟩

/-- The literals of a clause, within the cap. -/
theorem lits_ok (cap : Bool) (R : List Sym) : ∀ (ls : List (ℕ × Bool)) (n : ℕ) (U : List Sym)
    (v : Bool), (cap = false ∨ n + ls.length ≤ 3) → ∃ v',
      Run (prog cap) (ls.flatMap litRev).length ⟨some (wl n), v, st (ls.flatMap litRev ++ R) U⟩
        ⟨some (wl (n + ls.length)), v', st R ((ls.flatMap litRev).reverse ++ U)⟩ := by
  intro ls
  induction ls with
  | nil => intro n U v _; exact ⟨v, Run.zero _⟩
  | cons l ls ih =>
      intro n U v h
      have hn : (cap && 3 ≤ n) = false := by
        rcases h with h | h
        · simp [h]
        · have : n ≤ 2 := by simp only [List.length_cons] at h; omega
          cases cap
          · simp
          · simp; omega
      obtain ⟨v₁, r₁⟩ := walk_lit cap n hn l (ls.flatMap litRev ++ R) U v
      obtain ⟨v₂, r₂⟩ := ih (n + 1) ((litRev l).reverse ++ U) v₁
        (by rcases h with h | h <;> [exact .inl h; (right; simp at h; omega)])
      refine ⟨v₂, ?_⟩
      have h3 := (r₁.trans r₂).of_eq (show _ = ((l :: ls).flatMap litRev).length by simp)
      simpa [Nat.add_assoc, Nat.add_comm 1] using h3

/-- The literals of a clause, past the cap. -/
theorem lits_fail (R : List Sym) : ∀ (ls : List (ℕ × Bool)) (n : ℕ) (U : List Sym) (v : Bool),
    n ≤ 3 → 3 < n + ls.length → ∃ v' S',
      RunLe (prog true) (ls.flatMap litRev).length ⟨some (wl n), v, st (ls.flatMap litRev ++ R) U⟩
        ⟨some .fail, v', S'⟩ := by
  intro ls
  induction ls with
  | nil => intro n U v h0 h; simp at h; omega
  | cons l ls ih =>
      intro n U v h0 h
      rw [List.flatMap_cons, List.append_assoc]
      by_cases hn : 3 ≤ n
      · obtain ⟨v', S', r⟩ := walk_lit_fail n hn l (ls.flatMap litRev ++ R) U v
        refine ⟨v', S', r.le ?_⟩
        have := List.length_pos_of_ne_nil (litRev_ne_nil l)
        simp only [List.length_append]; omega
      · obtain ⟨v₁, r₁⟩ := walk_lit true n (by simp; omega) l (ls.flatMap litRev ++ R) U v
        obtain ⟨v', S', r₂⟩ := ih (n + 1) ((litRev l).reverse ++ U) v₁ (by omega)
          (by simp at h; omega)
        exact ⟨v', S', ((r₁.le le_rfl).trans r₂).mono (by simp)⟩

/-- One clause within the cap: `cl` resets the count, then its literals. -/
theorem clause_ok (cap : Bool) (C : CNFClause) (hC : cap = false ∨ C.length ≤ 3) (n : ℕ)
    (R U : List Sym) (v : Bool) : ∃ v',
      Run (prog cap) (clRev C).length ⟨some (wl n), v, st (clRev C ++ R) U⟩
        ⟨some (wl C.length), v', st R ((clRev C).reverse ++ U)⟩ := by
  have h1 := walk_step cap n .cl trivial (C.reverse.flatMap litRev ++ R) U v
  obtain ⟨v₂, r₂⟩ := lits_ok cap R C.reverse 0 (.cl :: U) true (by simpa using hC)
  refine ⟨v₂, ?_⟩
  have h := (h1.trans r₂).of_eq (show _ = (clRev C).length by simp [clRev, Nat.add_comm])
  simpa [clRev, tgt, wl] using h

/-- One clause past the cap. -/
theorem clause_fail (C : CNFClause) (hC : 3 < C.length) (n : ℕ) (R U : List Sym) (v : Bool) :
    ∃ v' S', RunLe (prog true) (clRev C).length ⟨some (wl n), v, st (clRev C ++ R) U⟩
      ⟨some .fail, v', S'⟩ := by
  have h1 := walk_step true n .cl trivial (C.reverse.flatMap litRev ++ R) U v
  obtain ⟨v', S', r₂⟩ := lits_fail R C.reverse 0 (.cl :: U) true (by omega) (by simpa using hC)
  refine ⟨v', S', ((h1.le le_rfl).trans (by simpa [tgt, wl] using r₂)).mono ?_⟩
  simp [clRev, Nat.add_comm]

/-- All clauses within the cap. -/
theorem cls_ok (cap : Bool) (R : List Sym) : ∀ (cs : List CNFClause),
    (∀ C ∈ cs, cap = false ∨ C.length ≤ 3) → ∀ (n : ℕ) (U : List Sym) (v : Bool), ∃ m v',
      Run (prog cap) (cs.flatMap clRev).length ⟨some (wl n), v, st (cs.flatMap clRev ++ R) U⟩
        ⟨some (wl m), v', st R ((cs.flatMap clRev).reverse ++ U)⟩ := by
  intro cs
  induction cs with
  | nil => intro _ n U v; exact ⟨n, v, Run.zero _⟩
  | cons C cs ih =>
      intro h n U v
      obtain ⟨v₁, r₁⟩ := clause_ok cap C (h C (by simp)) n (cs.flatMap clRev ++ R) U v
      obtain ⟨m, v₂, r₂⟩ := ih (fun C' hC' => h C' (List.mem_cons_of_mem _ hC')) C.length
        ((clRev C).reverse ++ U) v₁
      refine ⟨m, v₂, ?_⟩
      have h3 := (r₁.trans r₂).of_eq (show _ = ((C :: cs).flatMap clRev).length by simp)
      simpa using h3

/-- Some clause past the cap. -/
theorem cls_fail (R : List Sym) : ∀ (cs : List CNFClause), (∃ C ∈ cs, 3 < C.length) →
    ∀ (n : ℕ) (U : List Sym) (v : Bool), ∃ v' S',
      RunLe (prog true) (cs.flatMap clRev).length ⟨some (wl n), v, st (cs.flatMap clRev ++ R) U⟩
        ⟨some .fail, v', S'⟩ := by
  intro cs
  induction cs with
  | nil => intro h; simp at h
  | cons C cs ih =>
      intro h n U v
      rw [List.flatMap_cons, List.append_assoc]
      by_cases hC : 3 < C.length
      · obtain ⟨v', S', r⟩ := clause_fail C hC n (cs.flatMap clRev ++ R) U v
        exact ⟨v', S', r.mono (by simp)⟩
      · obtain ⟨v₁, r₁⟩ := clause_ok true C (.inr (by omega)) n (cs.flatMap clRev ++ R) U v
        obtain ⟨C', hC', h'⟩ := h
        have hC'' : C' ∈ cs := (List.mem_cons.1 hC').resolve_left fun e => hC (e ▸ h')
        obtain ⟨v', S', r₂⟩ := ih ⟨C', hC'', h'⟩ C.length ((clRev C).reverse ++ U) v₁
        exact ⟨v', S', ((r₁.le le_rfl).trans r₂).mono (by simp)⟩

/-- An empty token stack ends the walk. -/
theorem walk_end (cap : Bool) (n : ℕ) (U : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some (wl n), v, st [] U⟩ ⟨some .back, true, st [] U⟩ :=
  Run.single (by rw [prog_wl]; simp [walk, TM2.stepAux, st])

/-- One token moves back. -/
theorem back_step (cap : Bool) (s : Sym) (hs : IsTok s) (R M : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some .back, v, st R (s :: M)⟩ ⟨some .back, true, st (s :: R) M⟩ := by
  refine Run.single ?_
  have e : ∀ t u : List Sym, update (update (st R (s :: M)) .U u) .T t = st t u := by
    intro t u; funext k; cases k <;> rfl
  rcases s with b | p | _ | _ | _ <;> simp only [IsTok] at hs
  · cases b <;> simp [prog, mvIf, TM2.stepAux, st, e]
  · cases p <;> simp [prog, mvIf, TM2.stepAux, st, e]
  · simp [prog, mvIf, TM2.stepAux, st, e]

/-- Moving every token back. -/
theorem back_run (cap : Bool) : ∀ (M R : List Sym), (∀ s ∈ M, IsTok s) → ∀ v : Bool, ∃ v',
    Run (prog cap) M.length ⟨some .back, v, st R M⟩ ⟨some .back, v', st (M.reverse ++ R) []⟩ := by
  intro M
  induction M with
  | nil => intro R _ v; exact ⟨v, Run.zero _⟩
  | cons s M ih =>
      intro R h v
      obtain ⟨v', r⟩ := ih (s :: R) (fun s' hs' => h s' (by simp [hs'])) true
      refine ⟨v', ?_⟩
      have h3 := ((back_step cap s (h s (by simp)) R M v).trans r).of_eq
        (show 1 + M.length = (s :: M).length by simp [Nat.add_comm])
      simpa using h3

/-- An empty side stack passes. -/
theorem back_end (cap : Bool) (R : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some .back, v, st R []⟩ ⟨some .pass, true, st R []⟩ :=
  Run.single (by simp [prog, TM2.stepAux, st])

theorem isTok_of_mem (φ : CNF) : ∀ s ∈ φ.reverse.flatMap clRev, IsTok s := by
  intro s hs
  simp only [List.mem_flatMap, clRev, List.mem_cons, litRev, List.mem_reverse,
    List.mem_map] at hs
  obtain ⟨_, _, rfl | ⟨_, _, rfl | ⟨_, _, rfl⟩⟩⟩ := hs <;> trivial

/-- **The filter**: from `start` on the token stack of `φ`, reach `pass` when `!cap || is3 φ`
(stacks unchanged) and `fail` otherwise, within `2 |toks φ| + 2` steps. -/
theorem run (cap : Bool) (φ : CNF) (v : Bool) (St : ∀ _ : K, List Sym)
    (hT : St .T = (toks φ).reverse) (hU : St .U = []) :
    ∃ v' S', RunLe (prog cap) (2 * (toks φ).length + 2) ⟨some start, v, St⟩
      ⟨some (if (!cap || is3 φ) then .pass else .fail), v', S'⟩ ∧
      ((!cap || is3 φ) = true → S' = St) := by
  have hS : St = st (φ.reverse.flatMap clRev ++ []) [] := by
    rw [← st_eta St, hT, hU, toks_reverse, List.append_nil]
  have hlen : (toks φ).length = (φ.reverse.flatMap clRev).length := by
    rw [← List.length_reverse, toks_reverse]
  subst hS
  by_cases h : (!cap || is3 φ) = true
  · have hall : ∀ C ∈ φ.reverse, cap = false ∨ C.length ≤ 3 := by
      intro C hC
      cases cap
      · exact .inl rfl
      · right; simp only [is3, Bool.not_true, Bool.false_or, List.all_eq_true,
          decide_eq_true_eq] at h; exact h C (List.mem_reverse.1 hC)
    obtain ⟨m, v₁, r₁⟩ := cls_ok cap [] φ.reverse hall 0 [] v
    obtain ⟨v₂, r₂⟩ := back_run cap ((φ.reverse.flatMap clRev).reverse ++ []) []
      (fun s hs => isTok_of_mem φ s (by simpa using hs)) true
    refine ⟨true, st (φ.reverse.flatMap clRev ++ []) [], ?_, fun _ => rfl⟩
    simp only [h, ↓reduceIte]
    refine ((((r₁.trans (walk_end cap m _ v₁)).trans r₂).trans (back_end cap _ v₂)).le ?_).mono
      le_rfl |> fun r => by simpa [start, wl] using r
    simp [hlen]; omega
  · have hc : cap = true := by cases cap <;> simp_all
    subst hc
    have hbad : ∃ C ∈ φ.reverse, 3 < C.length := by
      simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true, is3, List.all_eq_false,
        decide_eq_false_iff_not, not_le] at h
      obtain ⟨C, hC, h⟩ := h
      exact ⟨C, List.mem_reverse.2 hC, h⟩
    obtain ⟨v', S', r⟩ := cls_fail [] φ.reverse hbad 0 [] v
    refine ⟨v', S', ?_, fun h' => absurd h' h⟩
    simp only [h]
    simpa [start, wl] using r.mono (show _ ≤ 2 * (toks φ).length + 2 by omega)

end Cslib.Complexity.Karp.Filter3
