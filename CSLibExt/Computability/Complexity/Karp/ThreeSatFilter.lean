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

/-- **Stacks of the 3SAT clause-length filter.** The filter has exactly two stacks: the token
stack $T$ and the side stack $U$. -/
inductive K | T | U
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.T, .U], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Labels of the 3SAT clause-length filter.** The filter has exactly seven labels: the walking
labels $w_0, w_1, w_2, w_3$, at which it walks the token stack having seen that many literals of
the current clause ($w_3$: three or more); the return label $\mathsf{back}$, at which it moves
the tokens back; and the exits $\mathsf{pass}$ and $\mathsf{fail}$. -/
inductive Lab | w0 | w1 | w2 | w3 | back | pass | fail
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.w0, .w1, .w2, .w3, .back, .pass, .fail], by decide⟩
  complete := fun l => by cases l <;> decide

/-- **Statements of the filter.** The statements of a multi-stack Turing machine (Mathlib's TM2
model) with the two stacks $T$ and $U$, each over the symbol alphabet of the SAT verifier, the
labels of the filter, and a Boolean internal state. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- **Walking label for a literal count.** The walking label after $n$ literals of the current
clause: $w_0$, $w_1$, $w_2$ for $n = 0, 1, 2$, and $w_3$ for every $n \ge 3$. -/
def wl : ℕ → Lab
  | 0 => .w0
  | 1 => .w1
  | 2 => .w2
  | _ => .w3

/-- **Next walking label.** Write $w_i$ for the walking label after $i$ literals of the current
clause ($w_3$: three or more). For a Boolean $c$ (whether the filter is capped), the label after
one more literal sends $w_0$ to $w_1$, $w_1$ to $w_2$ and $w_2$ to $w_3$; it sends $w_3$ to the
failure label when $c$ is true and to $w_3$ when $c$ is false; every other label is unchanged. -/
def nxt (cap : Bool) : Lab → Lab
  | .w0 => .w1
  | .w1 => .w2
  | .w2 => .w3
  | .w3 => if cap then .fail else .w3
  | l => l

open TM2.Stmt in
/-- **Conditional move between stacks.** For stacks $a$ and $b$ of the filter, a symbol $s$, a
label $\ell$ and a statement $q$: the statement that tests whether the top of stack $a$ is $s$ and
sets the internal state to the outcome; if it is, it pops $a$, pushes $s$ onto $b$ and jumps to
$\ell$, and otherwise it runs $q$. -/
def mvIf (a b : K) (s : Sym) (l : Lab) (q : Stmt) : Stmt :=
  peek a (fun _ o => decide (o = some s)) <| branch id
    (pop a (fun v _ => v) <| push b (fun _ => s) <| goto fun _ => l) q

open TM2.Stmt in
/-- **One step of the clause-length walk.** Write $w_0, w_1, w_2, w_3$ for the walking labels
after zero, one, two, and three or more literals of the current clause. For a Boolean cap flag
$\mathrm{cap}$ and a label $\ell$, the filter statement run at $\ell$: if the token stack is
empty, go to the label $\mathrm{back}$; if its top is the clause marker, move it onto the side
stack and go to $w_0$; if its top is a polarity marker, move it onto the side stack and go to
$w_1$, $w_2$, $w_3$ when $\ell$ is $w_0$, $w_1$, $w_2$ respectively, to $\mathrm{fail}$ when
$\ell = w_3$ and $\mathrm{cap}$ is true, and to $\ell$ otherwise; if its top is a name bit, move
it onto the side stack and stay at $\ell$; on any other symbol, go to $\mathrm{fail}$ without
moving it. Each test stores its outcome in the local variable. -/
def walk (cap : Bool) (l : Lab) : Stmt :=
  peek .T (fun _ o => o.isNone) <| branch id (goto fun _ => .back) <|
    mvIf .T .U .cl .w0 <| mvIf .T .U (.lit true) (nxt cap l) <|
    mvIf .T .U (.lit false) (nxt cap l) <| mvIf .T .U (.bit true) l <|
    mvIf .T .U (.bit false) l <| goto fun _ => .fail

open TM2.Stmt in
/-- **The clause-length filter program.** For a Boolean $c$ (whether the filter is capped), the
program on the labels of the filter: at a walking label it runs one walking step with cap $c$; at
the label back it moves the top of the side stack $U$ onto the token stack $T$ and stays at back
when that top is a token (a clause marker, a literal marker or a name bit), goes to the label pass
when $U$ is empty, and goes to the label fail otherwise; at pass and at fail it halts. Each test
records its outcome in the internal state. -/
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

/-- **Start label of the filter.** The filter starts at the walking label $w_0$, the label for
having seen no literal of the current clause. -/
def start : Lab := .w0

/-- **Token symbols of the 3SAT filter.** A symbol of the SAT verifier's alphabet is a token
symbol when it is the clause marker, a literal marker of either polarity, or a name bit. The value
markers and the dead marker are not token symbols. -/
def IsTok : Sym → Prop
  | .cl | .lit _ | .bit _ => True
  | _ => False

/-- **Label after a token.** Write $w_i$ for the walking label after $i$ literals of the current
clause ($w_3$: three or more). For a Boolean $c$ (whether the filter is capped) and a label
$\ell$, the label reached from $\ell$ on a symbol $s$ is: $w_0$ if $s$ is a clause marker; if $s$
is a literal marker, $w_1$, $w_2$ or $w_3$ when $\ell$ is $w_0$, $w_1$ or $w_2$ respectively, the
failure label when $\ell = w_3$ and $c$ is true, and $\ell$ itself otherwise; and $\ell$ itself
for every other symbol. -/
def tgt (cap : Bool) (l : Lab) : Sym → Lab
  | .cl => .w0
  | .lit _ => nxt cap l
  | _ => l

theorem nxt_wl (cap : Bool) (n : ℕ) :
    nxt cap (wl n) = if cap && 3 ≤ n then .fail else wl (n + 1) := by
  rcases n with _ | _ | _ | n <;> cases cap <;> simp [wl, nxt]

theorem prog_wl (cap : Bool) (n : ℕ) : prog cap (wl n) = walk cap (wl n) := by
  rcases n with _ | _ | _ | n <;> rfl

/-- **Filter stacks from two lists.** For lists of symbols $t$ and $u$, the stack contents that
put $t$ on the token stack $T$ and $u$ on the side stack $U$. -/
def st (t u : List Sym) : ∀ _ : K, List Sym
  | .T => t
  | .U => u

theorem st_eta (S : ∀ _ : K, List Sym) : st (S .T) (S .U) = S := by
  funext k; cases k <;> rfl

/-- **One step of the clause-length walk on a token.** Let $\mathrm{cap}$ be a Boolean,
$n \in \mathbb{N}$, $s$ a token (a name bit, a polarity marker or the clause marker), $R$ and $U$
lists of symbols and $v$ a Boolean; stacks are lists written top first, and $w_m$ is the walking
label after $m$ literals. Let $t$ be $w_0$ if $s$ is the clause marker, $w_n$ if $s$ is a name
bit, and, if $s$ is a polarity marker, $\mathrm{fail}$ when $\mathrm{cap}$ is true and $n \ge 3$
and $w_{n+1}$ otherwise. The clause-length filter with cap flag $\mathrm{cap}$ goes in exactly
one step from label $w_n$, local variable $v$, token stack $s$ on top of $R$ and side stack $U$
to label $t$, local variable true, token stack $R$ and side stack $s$ on top of $U$. -/
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

/-- **Walking over name bits keeps the label.** Let $\mathrm{cap}$ be a Boolean, $n \in \mathbb{N}$
and $R$ a list of symbols; stacks are lists written top first, $w_n$ is the walking label after
$n$ literals and $\mathrm{bit}(b)$ is the name-bit symbol carrying the Boolean $b$. For all
Booleans $b_1, \dots, b_k$, every list of symbols $U$ and every Boolean $v$ there is a Boolean
$v'$ such that the clause-length filter with cap flag $\mathrm{cap}$ goes in exactly $k$ steps
from label $w_n$, local variable $v$, token stack $\mathrm{bit}(b_1), \dots, \mathrm{bit}(b_k)$
on top of $R$ and side stack $U$ to label $w_n$, local variable $v'$, token stack $R$ and side
stack $\mathrm{bit}(b_k), \dots, \mathrm{bit}(b_1)$ on top of $U$. -/
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

/-- **Walking over a literal advances the literal count.** Let $\mathrm{cap}$ be a Boolean and
$n \in \mathbb{N}$ with $\mathrm{cap}$ false or $n < 3$; stacks are lists written top first,
$w_m$ is the walking label after $m$ literals, $\mathrm{bit}(b)$ is the name-bit symbol carrying
the Boolean $b$ and $\mathrm{lit}(p)$ is the polarity marker of polarity $p$. Let $l = (i, p)$ be
a literal with variable index $i \in \mathbb{N}$ and polarity $p$, let $e_1, \dots, e_k$ be the
binary encoding $\mathrm{encodeNat}(i)$ of $i$, let $R$ and $U$ be lists of symbols and $v$ a
Boolean. Then there is a Boolean $v'$ such that the clause-length filter with cap flag
$\mathrm{cap}$ goes in exactly $k + 1$ steps from label $w_n$, local variable $v$, token stack
$\mathrm{lit}(p), \mathrm{bit}(e_k), \dots, \mathrm{bit}(e_1)$ on top of $R$ and side stack $U$
to label $w_{n+1}$, local variable $v'$, token stack $R$ and side stack
$\mathrm{bit}(e_1), \dots, \mathrm{bit}(e_k), \mathrm{lit}(p)$ on top of $U$. -/
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

/-- **A capped walk fails on a literal past the third.** Let $n \in \mathbb{N}$ with $n \ge 3$
and let $w_n$ be the walking label after $n$ literals; stacks are lists written top first,
$\mathrm{bit}(b)$ is the name-bit symbol carrying the Boolean $b$ and $\mathrm{lit}(p)$ is the
polarity marker of polarity $p$. Let $l = (i, p)$ be a literal with variable index
$i \in \mathbb{N}$ and polarity $p$, let $e_1, \dots, e_m$ be the binary encoding
$\mathrm{encodeNat}(i)$ of $i$, let $R$ and $U$ be lists of symbols and $v$ a Boolean. Then
there are a Boolean $v'$ and stacks $S'$ such that the capped clause-length filter (cap flag
true) goes in exactly one step from label $w_n$, local variable $v$, token stack
$\mathrm{lit}(p), \mathrm{bit}(e_m), \dots, \mathrm{bit}(e_1)$ on top of $R$ and side stack $U$
to the label $\mathrm{fail}$ with local variable $v'$ and stacks $S'$. -/
theorem walk_lit_fail (n : ℕ) (hn : 3 ≤ n) (l : ℕ × Bool) (R U : List Sym) (v : Bool) :
    ∃ v' S', Run (prog true) 1 ⟨some (wl n), v, st (litRev l ++ R) U⟩ ⟨some .fail, v', S'⟩ := by
  have h1 := walk_step true n (.lit l.2) trivial (((encodeNat l.1).map Sym.bit).reverse ++ R) U v
  simp only [tgt, nxt_wl, Bool.true_and, decide_eq_true hn, ↓reduceIte] at h1
  exact ⟨_, _, by simpa [litRev] using h1⟩

/-- **The filter walks a clause's literals within the cap.** Let $c$ be a Boolean (whether the
filter is capped), let $\ell_1, \dots, \ell_k$ be literals (pairs of a variable index and a
polarity), let $n$ be a natural number with $c$ false or $n + k \le 3$, and let $w$ be the
concatenation of the stack tokens of $\ell_1, \dots, \ell_k$. For all lists of symbols $R$ and $U$
and every internal state $v$, the filter program with cap $c$, started at the walking label for $n$
literals with internal state $v$, token stack $wR$ (top first) and side stack $U$, reaches in
exactly $|w|$ steps the walking label for $n + k$ literals, with some internal state, token stack
$R$ and side stack $w^{\mathrm{rev}} U$, where $w^{\mathrm{rev}}$ is $w$ reversed. -/
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

/-- **The capped filter fails on a clause with too many literals.** Let $n \le 3$, let
$\ell_1, \dots, \ell_k$ be literals (pairs of a variable index and a polarity) with $3 < n + k$,
and let $w$ be the concatenation of the stack tokens of $\ell_1, \dots, \ell_k$. For all lists of
symbols $R$ and $U$ and every internal state $v$, the capped filter program, started at the
walking label for $n$ literals with internal state $v$, token stack $wR$ (top first) and side
stack $U$, reaches the failure label, with some internal state and some stacks, in at most $|w|$
steps. -/
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

/-- **The 3SAT filter walks one clause within the cap.** Let $C$ be a clause, and suppose the cap
flag is off or $C$ has at most three literals. Let $\overline{C}$ be the tokens of $C$ as they
lie on the token stack (the clause marker on top, then the literals' tokens, last literal first),
and let $w_n$ be the walking label after $n$ literals. For every $n$, all lists of symbols $R$
and $U$ and every value $v$ of the Boolean variable, there is a value $v'$ such that the 3SAT
clause-length filter takes exactly $|\overline{C}|$ steps from label $w_n$ with variable $v$,
token stack $\overline{C}$ on top of $R$ and side stack $U$ to label $w_{|C|}$ with variable
$v'$, token stack $R$, and side stack the reversal of $\overline{C}$ on top of $U$.

The clause marker resets the literal count, and each literal then advances it. -/
theorem clause_ok (cap : Bool) (C : CNFClause) (hC : cap = false ∨ C.length ≤ 3) (n : ℕ)
    (R U : List Sym) (v : Bool) : ∃ v',
      Run (prog cap) (clRev C).length ⟨some (wl n), v, st (clRev C ++ R) U⟩
        ⟨some (wl C.length), v', st R ((clRev C).reverse ++ U)⟩ := by
  have h1 := walk_step cap n .cl trivial (C.reverse.flatMap litRev ++ R) U v
  obtain ⟨v₂, r₂⟩ := lits_ok cap R C.reverse 0 (.cl :: U) true (by simpa using hC)
  refine ⟨v₂, ?_⟩
  have h := (h1.trans r₂).of_eq (show _ = (clRev C).length by simp [clRev, Nat.add_comm])
  simpa [clRev, tgt, wl] using h

/-- **A clause with more than three literals makes the capped 3SAT filter fail.** Let $C$ be a
clause with more than three literals, let $\overline{C}$ be its tokens as they lie on the token
stack (the clause marker on top, then the literals' tokens, last literal first), and let $w_n$ be
the walking label after $n$ literals. For every $n$, all lists of symbols $R$ and $U$ and every
value $v$ of the Boolean variable, the 3SAT clause-length filter with the cap on reaches label
$\mathsf{fail}$, with some value of the variable and some stacks, in at most $|\overline{C}|$
steps from label $w_n$ with variable $v$, token stack $\overline{C}$ on top of $R$, and side
stack $U$. -/
theorem clause_fail (C : CNFClause) (hC : 3 < C.length) (n : ℕ) (R U : List Sym) (v : Bool) :
    ∃ v' S', RunLe (prog true) (clRev C).length ⟨some (wl n), v, st (clRev C ++ R) U⟩
      ⟨some .fail, v', S'⟩ := by
  have h1 := walk_step true n .cl trivial (C.reverse.flatMap litRev ++ R) U v
  obtain ⟨v', S', r₂⟩ := lits_fail R C.reverse 0 (.cl :: U) true (by omega) (by simpa using hC)
  refine ⟨v', S', ((h1.le le_rfl).trans (by simpa [tgt, wl] using r₂)).mono ?_⟩
  simp [clRev, Nat.add_comm]

/-- **The 3SAT filter walks a list of clauses within the cap.** For a clause $C$ let
$\overline{C}$ be its tokens as they lie on the token stack (the clause marker on top, then the
literals' tokens, last literal first). Let $C_1, \dots, C_k$ be clauses such that, for each $i$,
the cap flag is off or $C_i$ has at most three literals. Let $X$ be the concatenation
$\overline{C_1} \cdots \overline{C_k}$ with $\overline{C_1}$ on top, and let $w_n$ be the walking
label after $n$ literals. For every list of symbols $R$, every $n$, every list of symbols $U$ and
every value $v$ of the Boolean variable, there are $m$ and a value $v'$ such that the 3SAT
clause-length filter takes exactly $|X|$ steps from label $w_n$ with variable $v$, token stack
$X$ on top of $R$ and side stack $U$ to label $w_m$ with variable $v'$, token stack $R$, and side
stack the reversal of $X$ on top of $U$. -/
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

/-- **A long clause makes the capped 3SAT filter fail on a list of clauses.** For a clause $C$ let
$\overline{C}$ be its tokens as they lie on the token stack (the clause marker on top, then the
literals' tokens, last literal first). For a list of clauses $C_1, \dots, C_k$, let $X$ be the
concatenation $\overline{C_1} \cdots \overline{C_k}$ with $\overline{C_1}$ on top, and let $w_n$
be the walking label after $n$ literals. If some $C_i$ has more than three literals, then for
every list of symbols $R$, every $n$, every list of symbols $U$ and every value $v$ of the Boolean
variable, the 3SAT clause-length filter with the cap on reaches label $\mathsf{fail}$, with some
value of the variable and some stacks, in at most $|X|$ steps from label $w_n$ with variable $v$,
token stack $X$ on top of $R$, and side stack $U$. -/
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

/-- **An empty token stack ends the walk.** Let $\mathrm{cap}$ be a Boolean, $n \in \mathbb{N}$,
$U$ a list of symbols and $v$ a Boolean, and let $w_n$ be the walking label after $n$ literals.
The clause-length filter with cap flag $\mathrm{cap}$ goes in exactly one step from label $w_n$,
local variable $v$, empty token stack and side stack $U$ to the label $\mathrm{back}$, local
variable true, empty token stack and side stack $U$. -/
theorem walk_end (cap : Bool) (n : ℕ) (U : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some (wl n), v, st [] U⟩ ⟨some .back, true, st [] U⟩ :=
  Run.single (by rw [prog_wl]; simp [walk, TM2.stepAux, st])

/-- **One step of the 3SAT filter's return phase.** For either value of the cap flag, every token
symbol $s$, all lists of symbols $R$ and $M$ and every value $v$ of the Boolean variable, the 3SAT
clause-length filter takes exactly one step from label $\mathsf{back}$ with variable $v$, token
stack $R$ and side stack $s$ on top of $M$ to label $\mathsf{back}$ with variable true, token
stack $s$ on top of $R$, and side stack $M$. -/
theorem back_step (cap : Bool) (s : Sym) (hs : IsTok s) (R M : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some .back, v, st R (s :: M)⟩ ⟨some .back, true, st (s :: R) M⟩ := by
  refine Run.single ?_
  have e : ∀ t u : List Sym, update (update (st R (s :: M)) .U u) .T t = st t u := by
    intro t u; funext k; cases k <;> rfl
  rcases s with b | p | _ | _ | _ <;> simp only [IsTok] at hs
  · cases b <;> simp [prog, mvIf, TM2.stepAux, st, e]
  · cases p <;> simp [prog, mvIf, TM2.stepAux, st, e]
  · simp [prog, mvIf, TM2.stepAux, st, e]

/-- **The 3SAT filter's return phase moves the side stack back.** For either value of the cap
flag, all lists of symbols $M$ and $R$ such that every symbol of $M$ is a token symbol, and every
value $v$ of the Boolean variable, there is a value $v'$ such that the 3SAT clause-length filter
takes exactly $|M|$ steps from label $\mathsf{back}$ with variable $v$, token stack $R$ and side
stack $M$ to label $\mathsf{back}$ with variable $v'$, token stack the reversal of $M$ on top of
$R$, and empty side stack. -/
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

/-- **The return phase ends on an empty side stack.** For either value of the cap flag, every
list of symbols $R$ and every value $v$ of the Boolean variable, the 3SAT clause-length filter
takes exactly one step from label $\mathsf{back}$ with variable $v$, token stack $R$ and empty
side stack to label $\mathsf{pass}$ with variable true, token stack $R$ and empty side stack. -/
theorem back_end (cap : Bool) (R : List Sym) (v : Bool) :
    Run (prog cap) 1 ⟨some .back, v, st R []⟩ ⟨some .pass, true, st R []⟩ :=
  Run.single (by simp [prog, TM2.stepAux, st])

theorem isTok_of_mem (φ : CNF) : ∀ s ∈ φ.reverse.flatMap clRev, IsTok s := by
  intro s hs
  simp only [List.mem_flatMap, clRev, List.mem_cons, litRev, List.mem_reverse,
    List.mem_map] at hs
  obtain ⟨_, _, rfl | ⟨_, _, rfl | ⟨_, _, rfl⟩⟩⟩ := hs <;> trivial

/-- **Correctness of the clause-length filter.** Let $c$ be a Boolean (whether the filter is
capped), $\varphi$ a CNF formula and $v$ an internal state, and let $S$ be stacks holding the
reversed token list of $\varphi$ on the token stack $T$ and nothing on the side stack $U$. Let $b$
be the condition that $c$ is false or every clause of $\varphi$ has at most three literals, and
let $N$ be the number of tokens of $\varphi$. Then the filter program with cap $c$, started at its
start label with internal state $v$ and stacks $S$, reaches within $2N + 2$ steps the label pass
if $b$ holds and the label fail otherwise, with some internal state $v'$ and stacks $S'$; and if
$b$ holds, then $S' = S$. -/
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
