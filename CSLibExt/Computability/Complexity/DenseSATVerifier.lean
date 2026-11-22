/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `CookLevin.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/CookLevin.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.DenseSAT.Verifier` namespace, the local run predicate replaced by
`MetaMathlibExt.TM2Program.Run`, the source repository's pair encoding replaced by the explicit
`pairEncode`, and the `InNondeterministicPolynomialTime` corollary dropped (formal-math's `NP`
uses a different input encoding; see the module docstring).
-/

module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Tactic.Linarith
public import MathlibExt.Computability.TuringMachine.Program
public import CSLibExt.Computability.Complexity.DenseSAT

/-!
# A polynomial-time verifier machine for dense CNF-SAT

An explicit `Turing.FinTM2`, `Cslib.Complexity.DenseSAT.Verifier.tm`, that reads a formula `w`
and a candidate assignment `y` in the `w # y` form `pairEncode (w, y)` and outputs
`check w y`, in at most `2 (n + 5)²` steps for an input of length `n`
(`Cslib.Complexity.DenseSAT.Verifier.verifier`). With `sat_iff_check` this is the verifier
half of SAT ∈ NP.

The machine stashes `w` and `y` on two work stacks, restores them in order, and makes one
left-to-right pass over the formula bits: per clause it walks the assignment from a second stack,
records whether some literal is satisfied, and restores the assignment at the clause terminator.

formal-math's `MetaMathlibExt.ComplexityTheory.NP` feeds a verifier the canonical
`BitstringEncoding` of the pair (a `delimit`-framed formula followed by the certificate, each bit
written as three bits), not `w # y`; connecting the two needs an encoding-converter machine
composed in front of this one.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT

namespace Verifier

open Turing Function MetaMathlibExt

/-- **Work stacks of the dense CNF-SAT verifier.** The verifier has four work stacks: the input
stack, a stack $F$ that stashes the formula, and two stacks $A$ and $B$ for the assignment. -/
inductive W | inp | F | A | B
  deriving DecidableEq
instance W.instFintypeEnumFix : Fintype W where
  elems := ⟨↑[W.inp, W.F, W.A, W.B], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Work alphabet of the dense-SAT verifier.** The work alphabet $G$ is the disjoint union of
the Booleans and the optional Booleans. Its elements are the left symbols $\mathrm{inl}(b)$ and
the right symbols $\mathrm{inr}(o)$, where $b$ is a Boolean and $o$ is either
$\mathrm{some}\ b$ or $\mathrm{none}$. This is the alphabet of the pair encoding, in which
$\mathrm{inr}(\mathrm{none})$ is the separator $\#$.

Formula and assignment bits are stored on the work stacks as left symbols $\mathrm{inl}(b)$. -/
abbrev G := Bool ⊕ Option Bool

/-- **Pair encoding $w \# y$.** For bit strings $w$ and $y$, the word over the pair alphabet
$G = \mathrm{Bool} \oplus \mathrm{Option}\,\mathrm{Bool}$ consisting of the bits $b$ of $w$ in
order, each tagged on the left as $\mathrm{inl}\,b$, then the separator
$\# = \mathrm{inr}\,\mathrm{none}$, then the bits $b$ of $y$ in order, each tagged on the right as
$\mathrm{inr}(\mathrm{some}\,b)$. This is the input of the dense CNF-SAT verifier. -/
def pairEncode (p : List Bool × List Bool) : List G :=
  p.1.map Sum.inl ++ Sum.inr none :: p.2.map fun b => Sum.inr (some b)

/-- **Stack alphabets of the dense CNF-SAT verifier.** The stacks of the verifier are the output
stack and one stack for each work stack name (input, formula stash $F$, assignment stacks $A$
and $B$). The output stack has the Booleans as alphabet, and every work stack has the alphabet
$G$, the disjoint union of the Booleans and the Booleans extended by a separator $\#$. -/
@[reducible] def Γ : Option W → Type
  | none => Bool
  | some _ => G

/-- **Labels of the dense-SAT verifier.** The labels of the verifier's program are
$\mathrm{read1}$, $\mathrm{read2}$, $\mathrm{back1}$ and $\mathrm{back2}$; $\mathrm{c0}(f)$ and
$\mathrm{c1}(f, b)$ for Booleans $f$ and $b$; $\mathrm{adv}(f, o)$ for a Boolean $f$ and an
optional Boolean $o$; $\mathrm{restore}(f)$ for a Boolean $f$; and $\mathrm{drainI}(a)$,
$\mathrm{drainA}(a)$, $\mathrm{drainB}(a)$ and $\mathrm{finish}(a)$ for a Boolean $a$. There are
finitely many labels, and equality of labels is decidable.

The labels $\mathrm{c0}(f)$ and $\mathrm{c1}(f, b)$ read the two bits of a token, with $f$
recording whether the current clause is already satisfied. $\mathrm{adv}(f, o)$ moves one
assignment bit from stack $B$ to stack $A$ ($o = \mathrm{some}\ s$ for the literal token $1s$),
and $\mathrm{restore}(f)$ moves the used assignment bits back from $A$ to $B$. -/
inductive Lab
  | read1 | read2 | back1 | back2
  | c0 (fl : Bool) | c1 (fl b : Bool) | adv (fl : Bool) (o : Option Bool) | restore (fl : Bool)
  | drainI (ans : Bool) | drainA (ans : Bool) | drainB (ans : Bool) | finish (ans : Bool)
  deriving DecidableEq, Fintype

/-- **Machine states of the verifier.** The machine state of the dense CNF-SAT verifier is an
element of $\mathrm{Option}\,G$: either nothing or a work symbol in $G$.

The program uses it to hold the last popped symbol. -/
abbrev St := Option G

/-- **Statements of the dense CNF-SAT verifier.** The statements of the verifier are the
statements of Mathlib's multi-stack Turing machine model with stack alphabets $\Gamma$, labels in
the verifier's label type and machine states in $\mathrm{Option}\,G$. -/
abbrev Stmt := TM2.Stmt Γ Lab St
/-- **Configurations of the dense-SAT verifier.** A configuration of the verifier is a
configuration of the multi-stack Turing machine model with the verifier's labels, states and
stack alphabets. It consists of an optional current label (absent once the machine has halted),
a state, which is either a symbol of the work alphabet $G$ or nothing, and for each stack the
list of symbols on it: Booleans on the output stack and symbols of $G$ on each of the four work
stacks. -/
abbrev Cfg := TM2.Cfg Γ Lab St

/-- **Generic copy loop of the dense-SAT verifier.** For a work stack $s$, a partial map $g$ on
the work alphabet $G$, an optional target work stack $t$, and labels $\ell$ (the loop's own
label) and $\ell'$ (its exit), the generic loop is the program statement that does the following.
It pops the top of $s$ and stores the popped symbol $x$ as the machine state (nothing if $s$ is
empty). If $x$ exists and $g(x) = y$ is defined, it pushes $y$ onto $t$ (or pushes nothing when
there is no target stack) and jumps to $\ell$. Otherwise, when $s$ was empty or $g$ is undefined
at $x$, it jumps to $\ell'$. -/
def loop (s : W) (g : G → Option G) (t : Option W) (self next : Lab) : Stmt :=
  .pop (some s) (fun _ o => o) <|
    .branch (fun v => (v.bind g).isSome)
      (match t with
        | some t => .push (some t) (fun v => (v.bind g).getD (.inl false)) (.goto fun _ => self)
        | none => .goto fun _ => self)
      (.goto fun _ => next)

/-- **Formula filter of the dense-SAT verifier.** The partial map on the work alphabet $G$ that
sends each left symbol $\mathrm{inl}(b)$ to itself and is undefined on every right symbol
$\mathrm{inr}(o)$, including the separator $\mathrm{inr}(\mathrm{none})$, written $\#$.

The verifier's first copying loop uses it, so on the pair encoding of a formula and a
certificate it stops at the separator $\#$. -/
def gRead1 : G → Option G
  | .inl b => some (.inl b)
  | .inr _ => none

/-- **Certificate filter of the dense-SAT verifier.** The partial map on the work alphabet $G$
that sends each right symbol $\mathrm{inr}(\mathrm{some}\ b)$ to the left symbol
$\mathrm{inl}(b)$ and is undefined on every other symbol, that is on the left symbols and on the
separator $\mathrm{inr}(\mathrm{none})$. -/
def gRead2 : G → Option G
  | .inr (some b) => some (.inl b)
  | _ => none

/-- **The dense CNF-SAT verifier program.** The program assigns a statement to each label. Every
pop stores the popped symbol, or nothing if the stack was empty, as the machine state.

* $\mathsf{read1}$: pop the input stack; while the popped symbol is some $\mathrm{inl}\,b$, push
  $\mathrm{inl}\,b$ onto $F$ and pop again; otherwise go to $\mathsf{read2}$.
* $\mathsf{read2}$: pop the input stack; while the popped symbol is some
  $\mathrm{inr}(\mathrm{some}\,b)$, push $\mathrm{inl}\,b$ onto $A$ and pop again; otherwise go
  to $\mathsf{back1}$.
* $\mathsf{back1}$: pop $F$ and push each popped symbol onto the input stack until $F$ is empty,
  then go to $\mathsf{back2}$.
* $\mathsf{back2}$: pop $A$ and push each popped symbol onto $B$ until $A$ is empty, then go to
  $\mathsf{c0}(\mathrm{false})$.
* $\mathsf{c0}(fl)$: pop the input stack; if the popped symbol is $\mathrm{inl}\,b$, go to
  $\mathsf{c1}(fl, b)$, otherwise go to $\mathsf{drainI}(\mathrm{true})$.
* $\mathsf{c1}(fl, \mathrm{false})$: pop the input stack; on $\mathrm{inl}\,\mathrm{false}$ go to
  $\mathsf{restore}(fl)$, on $\mathrm{inl}\,\mathrm{true}$ go to
  $\mathsf{adv}(fl, \mathrm{none})$, otherwise go to $\mathsf{drainI}(\mathrm{true})$.
* $\mathsf{c1}(fl, \mathrm{true})$: pop the input stack; on $\mathrm{inl}\,s$ go to
  $\mathsf{adv}(fl, \mathrm{some}\,s)$, otherwise go to $\mathsf{drainI}(\mathrm{true})$.
* $\mathsf{adv}(fl, o)$: pop $B$; if a symbol $x$ was popped, push $x$ onto $A$ and go to
  $\mathsf{c0}(fl')$, where $fl'$ is true when $fl$ is true, or when $o = \mathrm{some}\,s$ for a
  bit $s$ with $x = \mathrm{inl}(\lnot s)$; if $B$ was empty, go to $\mathsf{c0}(fl)$.
* $\mathsf{restore}(fl)$: pop $A$ and push each popped symbol onto $B$ until $A$ is empty, then
  go to $\mathsf{c0}(\mathrm{false})$ if $fl$ is true and to $\mathsf{drainI}(\mathrm{false})$
  otherwise.
* $\mathsf{drainI}(ans)$, $\mathsf{drainA}(ans)$, $\mathsf{drainB}(ans)$: pop and discard the
  input stack, $A$, $B$ respectively until it is empty, then go to $\mathsf{drainA}(ans)$,
  $\mathsf{drainB}(ans)$, $\mathsf{finish}(ans)$ respectively.
* $\mathsf{finish}(ans)$: push $ans$ onto the output stack, clear the machine state and halt. -/
def prog : Lab → Stmt
  | .read1 => loop .inp gRead1 (some .F) .read1 .read2
  | .read2 => loop .inp gRead2 (some .A) .read2 .back1
  | .back1 => loop .F some (some .inp) .back1 .back2
  | .back2 => loop .A some (some .B) .back2 (.c0 false)
  | .c0 fl => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl b) => .c1 fl b
      | _ => .drainI true
  | .c1 fl false => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl false) => .restore fl
      | some (.inl true) => .adv fl none
      | _ => .drainI true
  | .c1 fl true => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl s) => .adv fl (some s)
      | _ => .drainI true
  | .adv fl o => .pop (some .B) (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push (some .A) (fun v => v.getD (.inl false)) <|
          .goto fun v => .c0 (fl || decide (v = o.map fun s => .inl (!s))))
        (.goto fun _ => .c0 fl)
  | .restore fl => loop .A some (some .B) (.restore fl) (if fl then .c0 false else .drainI false)
  | .drainI ans => loop .inp some none (.drainI ans) (.drainA ans)
  | .drainA ans => loop .A some none (.drainA ans) (.drainB ans)
  | .drainB ans => loop .B some none (.drainB ans) (.finish ans)
  | .finish ans => .push none (fun _ => ans) <| .load (fun _ => none) .halt

/-- **The dense CNF-SAT verifier machine.** The finite multi-stack Turing machine with an output
stack over the Booleans and four work stacks (the input stack, a formula stash $F$ and two
assignment stacks $A$ and $B$) over the alphabet $G$, the disjoint union of the Booleans and the
Booleans extended by a separator $\#$. It reads its input from the input stack, writes its
result to the output stack, starts at the first label of the verifier program with empty
internal state, and runs that program: on input $w \# y$ it moves the formula bits $w$ onto $F$
and the assignment bits $y$ onto $A$, moves them back so that $w$ is on the input stack and $y$
on $B$, then scans $w$ clause by clause, moving assignment bits from $B$ to $A$ to test the
literals of a clause and back from $A$ to $B$ at the end of the clause, and finally empties the
work stacks and pushes the computed bit onto the output stack. -/
def tm : FinTM2 where
  K := Option W
  k₀ := some .inp
  k₁ := none
  Γ := Γ
  Λ := Lab
  main := .read1
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype G)
  m := prog

/-! ### Configurations -/

/-- **All stacks of the verifier from work stacks and output.** Given work-stack contents $V$ (a
list $V(s)$ of work symbols for each work stack $s$) and a list $o$ of bits, the stack contents of
the verifier that give the output stack $o$ and each work stack $s$ the list $V(s)$. -/
def stk (V : W → List G) (o : List Bool) : ∀ k, List (Γ k)
  | none => o
  | some w => V w

theorem update_stk_some (V : W → List G) (o : List Bool) (w : W) (l : List G) :
    update (stk V o) (some w) l = stk (update V w l) o := by
  funext k
  rcases k with _ | k
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k = w
    · subst h; simp [stk]
    · rw [update_of_ne (by simpa using h)]
      simp [stk, update_of_ne h]

theorem update_stk_none (V : W → List G) (o l : List Bool) :
    update (stk V o) none l = stk V l := by
  funext k
  rcases k with _ | k
  · simp [stk]
  · rw [update_of_ne (by simp)]; rfl

/-- **Work stacks from four lists.** Given four lists $i$, $f$, $a$, $b$ of work symbols in $G$,
the contents of the verifier's work stacks in which the input stack holds $i$, the formula stash
$F$ holds $f$, and the assignment stacks $A$ and $B$ hold $a$ and $b$. -/
def mkV (i f a b : List G) : W → List G
  | .inp => i
  | .F => f
  | .A => a
  | .B => b

@[simp] theorem update_mkV_inp (i f a b x : List G) :
    update (mkV i f a b) .inp x = mkV x f a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_F (i f a b x : List G) :
    update (mkV i f a b) .F x = mkV i x a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_A (i f a b x : List G) :
    update (mkV i f a b) .A x = mkV i f x b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_B (i f a b x : List G) :
    update (mkV i f a b) .B x = mkV i f a x := by
  funext k; cases k <;> rfl

/-- **Pushing a list onto a verifier work stack.** Given an optional work stack $t$, a list $ys$
of work symbols and work-stack contents $V$ (a list $V(s)$ of symbols for each work stack $s$),
the contents obtained by pushing the elements of $ys$ one at a time onto $t$: if $t$ is a work
stack, $V(t)$ is replaced by the reverse of $ys$ followed by $V(t)$ and every other stack is
unchanged; if $t$ is none, the result is $V$. -/
def pushAll : Option W → List G → (W → List G) → W → List G
  | none, _, V => V
  | some t, ys, V => update V t (ys.reverse ++ V t)

/-- **Running the generic copy loop of the dense-SAT verifier.** Let $s$ be a work stack, $g$ a
partial map on the work alphabet $G$, $t$ an optional target work stack other than $s$, and
$\ell$, $\ell'$ labels such that the verifier's program at $\ell$ is the generic loop with source
$s$, map $g$, target $t$, own label $\ell$ and exit $\ell'$. Let $o$ be a list of output bits.
Let $x = x_1 \dots x_n$, $y = y_1 \dots y_n$ and $r$ be lists of symbols of $G$ with
$g(x_j) = y_j$ defined for every $j$, and with $r$ empty or $g$ undefined at the first symbol of
$r$. Let $V$ be work-stack contents with $V(s) = x r$, and let $v$ be any state. Started at
$\ell$ in state $v$ with work stacks $V$ and output stack $o$, the program runs for exactly
$n + 1$ steps and reaches the label $\ell'$. Its state is then the first symbol of $r$ (nothing
if $r$ is empty) and its output stack is still $o$. Its work stacks are obtained from $V$ by
replacing stack $s$ with $r$ minus its first symbol (empty if $r$ is empty) and then, if $t$ is
a stack, pushing $y_1, \dots, y_n$ onto $t$ one at a time. -/
theorem loop_run (s : W) (g : G → Option G) (t : Option W) (self next : Lab)
    (hp : prog self = loop s g t self next) (hst : t ≠ some s) (o : List Bool) :
    ∀ (xs ys rest : List G) (v : St) (V : W → List G),
      xs.map g = ys.map some → rest.head?.bind g = none → V s = xs ++ rest →
      TM2Program.Run prog (xs.length + 1) ⟨some self, v, stk V o⟩
        ⟨some next, rest.head?, stk (pushAll t ys (update V s rest.tail)) o⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro ys rest v V hg hr hV
      obtain rfl : ys = [] := by simpa using hg.symm
      refine TM2Program.Run.head ?_ (TM2Program.Run.zero _)
      simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
        List.nil_append, hr, Option.isSome_none, Bool.cond_false]
      rw [update_stk_some]
      rcases t with _ | t
      · rfl
      · simp [pushAll]
  | cons x xs ih =>
      intro ys rest v V hg hr hV
      rcases ys with _ | ⟨y, ys⟩
      · simp at hg
      simp only [List.map_cons, List.cons.injEq] at hg
      obtain ⟨hxy, hg⟩ := hg
      rcases t with _ | t
      · have key := ih ys rest (some x) (update V s (xs ++ rest)) hg hr (by simp)
        simp only [pushAll, update_idem] at key ⊢
        refine TM2Program.Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, Bool.cond_true]
        rw [update_stk_some]
      · have hts : t ≠ s := fun h => hst (by rw [h])
        have key := ih ys rest (some x) (update (update V s (xs ++ rest)) t (y :: V t)) hg hr
          (by rw [update_of_ne (Ne.symm hts)]; simp)
        have hfin : pushAll (some t) ys
              (update (update (update V s (xs ++ rest)) t (y :: V t)) s rest.tail) =
            pushAll (some t) (y :: ys) (update V s rest.tail) := by
          funext k
          simp only [pushAll]
          by_cases hk : k = t
          · subst hk; simp [update_of_ne hts]
          · by_cases hk' : k = s
            · subst hk'; simp [update_of_ne hk]
            · simp [update_of_ne hk, update_of_ne hk']
        rw [hfin] at key
        refine TM2Program.Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, Bool.cond_true, Option.getD_some]
        rw [update_stk_some, show stk (update V s (xs ++ rest)) o (some t) =
          update V s (xs ++ rest) t from rfl, update_stk_some, update_of_ne hts]

/-! ### Cleanup and output -/

/-- **Draining the work stacks of the dense-SAT verifier.** Let $\mathit{ans}$ be a Boolean, let
$i$, $a$, $b$ be lists of symbols of the work alphabet $G$, and let $v$ be any state. Start the
verifier's program at the label $\mathrm{drainI}(\mathit{ans})$ in state $v$, with the input
stack holding $i$, the formula stash empty, the assignment stacks $A$ and $B$ holding $a$ and
$b$, and the output stack empty. It then runs for exactly $|i| + |a| + |b| + 3$ steps and reaches
the label $\mathrm{finish}(\mathit{ans})$ with no symbol in its state, all four work stacks empty
and the output stack still empty. -/
theorem drain_run (ans : Bool) (i a b : List G) (v : St) :
    TM2Program.Run prog (i.length + a.length + b.length + 3)
      ⟨some (.drainI ans), v, stk (mkV i [] a b) []⟩
      ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩ := by
  have h₁ := loop_run .inp some none (.drainI ans) (.drainA ans) rfl (by simp) [] i i [] v
    (mkV i [] a b) rfl rfl (by simp [mkV])
  have h₂ := loop_run .A some none (.drainA ans) (.drainB ans) rfl (by simp) [] a a [] none
    (mkV [] [] a b) rfl rfl (by simp [mkV])
  have h₃ := loop_run .B some none (.drainB ans) (.finish ans) rfl (by simp) [] b b [] none
    (mkV [] [] [] b) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_inp, update_mkV_A,
    update_mkV_B] at h₁ h₂ h₃
  exact (h₁.trans (h₂.trans h₃)).of_eq (by omega)

theorem finish_run (ans : Bool) :
    TM2Program.Run prog 1 ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩
      ⟨none, none, stk (mkV [] [] [] []) [ans]⟩ := by
  refine TM2Program.Run.head ?_ (TM2Program.Run.zero _)
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_none]
  rfl

/-! ### The main scan -/

/-- **Left-tagged encoding of a bit list.** For a list $l$ of bits, its encoding on a work stack
of the dense-SAT verifier is the list of symbols of the work alphabet $G$ obtained by replacing
each bit $b$ of $l$ with the left symbol $\mathrm{inl}(b)$. -/
def enc (l : List Bool) : List G := l.map Sum.inl

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (b : Bool) (l : List Bool) : enc (b :: l) = .inl b :: enc l := rfl
@[simp] theorem length_enc (l : List Bool) : (enc l).length = l.length := List.length_map _

theorem step_c0_nil (fl : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c0_cons (fl x : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV (enc (x :: r)) [] a b) []⟩ =
      some ⟨some (.c1 fl x), some (.inl x), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_nil (fl x : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl x), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  cases x <;>
  · simp only [TM2.step, prog, TM2.stepAux]
    rw [update_stk_some]
    simp [stk, mkV]

theorem step_c1_ff (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (false :: r)) [] a b) []⟩ =
      some ⟨some (.restore fl), some (.inl false), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_ft (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (true :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl none), some (.inl true), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_t (fl s : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl true), v, stk (mkV (enc (s :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl (some s)), some (.inl s), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_nil (fl : Bool) (o : Option Bool) (i a : List G) (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a []) []⟩ =
      some ⟨some (.c0 fl), none, stk (mkV i [] a []) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_cons (fl : Bool) (o : Option Bool) (x : Bool) (i a : List G) (bs : List Bool)
    (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || decide (some (Sum.inl x : G) = o.map fun s => .inl (!s)))),
        some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [stk, mkV, update_stk_some]

theorem step_adv_none_cons (fl x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl none), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 fl), some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; simp

theorem step_adv_some_cons (fl s x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl (some s)), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || x == !s)), some (.inl x),
        stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; cases x <;> cases s <;> simp

/-- **Step count of the verifier's main scan.** The number $T(r, bs, as, fl) \in \mathbb{N}$, for
bit strings $r$, $bs$, $as$ and a flag $fl$, is defined by recursion on $r$, where $0$ is false
and $1$ is true, juxtaposition denotes concatenation (so $b\,r$ is $r$ with the bit $b$
prepended), $[\,]$ is the empty string, $\mathrm{rev}$ reverses a string and $|\cdot|$ is length:

* $T(0\,0\,r, bs, as, fl) = |as| + 3 + T(r, \mathrm{rev}(as)\,bs, [\,], \mathrm{false})$ if $fl$
  is true, and $|as| + 3 + (|r| + (|as| + |bs|) + 3)$ otherwise;
* $T(0\,1\,r, [\,], as, fl) = 3 + T(r, [\,], as, fl)$;
* $T(0\,1\,r, x\,bs, as, fl) = 3 + T(r, bs, x\,as, fl)$;
* $T(1\,s\,r, [\,], as, fl) = 3 + T(r, [\,], as, fl)$;
* $T(1\,s\,r, x\,bs, as, fl) = 3 + T(r, bs, x\,as, fl \lor (x = \lnot s))$;
* $T(r, bs, as, fl) = |r| + |as| + |bs| + 4$ when $r$ has fewer than two bits.

The recursion mirrors the dense CNF evaluation scan. -/
def T : List Bool → List Bool → List Bool → Bool → ℕ
  | false :: false :: r, bs, as, fl =>
      as.length + 3 +
        if fl then T r (as.reverse ++ bs) [] false else r.length + (as.length + bs.length) + 3
  | false :: true :: r, [], as, fl => 3 + T r [] as fl
  | false :: true :: r, x :: bs, as, fl => 3 + T r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => 3 + T r [] as fl
  | true :: s :: r, x :: bs, as, fl => 3 + T r bs (x :: as) (fl || x == !s)
  | r, bs, as, _ => r.length + as.length + bs.length + 4

theorem T_nil (bs as : List Bool) (fl : Bool) : T [] bs as fl = 0 + as.length + bs.length + 4 :=
  rfl

theorem T_single (b : Bool) (bs as : List Bool) (fl : Bool) :
    T [b] bs as fl = 1 + as.length + bs.length + 4 := by
  cases b <;> rfl

theorem enc_reverse_append (as bs : List Bool) :
    (enc as).reverse ++ enc bs = enc (as.reverse ++ bs) := by
  simp [enc]

/-- **The verifier's main scan.** For all bit strings $r$, $bs$, $as$, every flag $fl$ and every
machine state $v$, the verifier program leads in exactly $T(r, bs, as, fl)$ steps from the
configuration at label $\mathsf{c0}(fl)$ with machine state $v$, the input stack holding the bits
of $r$, the stack $A$ holding the bits of $as$ and the stack $B$ holding the bits of $bs$ (each bit
$b$ stored as $\mathrm{inl}\,b$, from the top in order), and the stack $F$ and the output stack
empty, to the configuration at label $\mathsf{finish}(\operatorname{evalCNF}(r, bs, as, fl))$
with empty machine state and all stacks empty. -/
theorem scan (r bs as : List Bool) (fl : Bool) (v : St) :
    TM2Program.Run prog (T r bs as fl) ⟨some (.c0 fl), v, stk (mkV (enc r) [] (enc as) (enc bs)) []⟩
      ⟨some (.finish (evalCNF r bs as fl)), none, stk (mkV [] [] [] []) []⟩ := by
  induction r, bs, as, fl using evalCNF.induct generalizing v with
  | case1 r bs as fl ih =>
      have hR := loop_run .A some (some .B) (.restore fl)
        (if fl then .c0 false else .drainI false) rfl (by simp) [] (enc as) (enc as) []
        (some (.inl false)) (mkV (enc r) [] (enc as) (enc bs)) rfl rfl (by simp [mkV])
      simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_A, mkV, update_mkV_B,
        enc_reverse_append] at hR
      have h₀ := step_c0_cons fl false (false :: r) (enc as) (enc bs) v
      have h₁ := step_c1_ff fl r (enc as) (enc bs) (some (.inl false))
      cases fl
      · have hD := drain_run false (enc r) [] (enc (as.reverse ++ bs)) none
        exact (TM2Program.Run.head h₀ (TM2Program.Run.head h₁ (hR.trans hD))).of_eq
          (by simp [T]; omega)
      · have hI := ih none
        exact (TM2Program.Run.head h₀ (TM2Program.Run.head h₁ (hR.trans hI))).of_eq
          (by simp [T]; omega)
  | case2 r as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl false (true :: r) (enc as) [] v)
        (TM2Program.Run.head (step_c1_ft fl r (enc as) [] _)
          (TM2Program.Run.head (step_adv_nil fl none (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case3 r x bs as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl false (true :: r) (enc as) (enc (x :: bs)) v)
        (TM2Program.Run.head (step_c1_ft fl r (enc as) (enc (x :: bs)) _)
          (TM2Program.Run.head (step_adv_none_cons fl x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case4 s r as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl true (s :: r) (enc as) [] v)
        (TM2Program.Run.head (step_c1_t fl s r (enc as) [] _)
          (TM2Program.Run.head (step_adv_nil fl (some s) (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case5 s r x bs as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl true (s :: r) (enc as) (enc (x :: bs)) v)
        (TM2Program.Run.head (step_c1_t fl s r (enc as) (enc (x :: bs)) _)
          (TM2Program.Run.head (step_adv_some_cons fl s x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := TM2Program.Run.head (step_c0_nil fl (enc as) (enc bs) v) hD
        rw [T_nil]
        exact h.of_eq (by simp)
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := TM2Program.Run.head (step_c0_cons fl b [] (enc as) (enc bs) v)
          (TM2Program.Run.head (step_c1_nil fl b (enc as) (enc bs) (some (.inl b))) hD)
        rw [T_single]
        have h' := h.of_eq (m := 1 + as.length + bs.length + 4) (by simp; omega)
        cases b <;> exact h'
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

theorem T_le (r bs as : List Bool) (fl : Bool) :
    T r bs as fl ≤ (r.length + 1) * (bs.length + as.length + 5) := by
  induction r, bs, as, fl using evalCNF.induct with
  | case1 r bs as fl ih =>
      cases fl
      · simp [T]; nlinarith
      · simp [T] at ih ⊢; nlinarith
  | case2 r as fl ih => simp [T] at ih ⊢; nlinarith
  | case3 r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case4 s r as fl ih => simp [T] at ih ⊢; nlinarith
  | case5 s r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · rw [T_nil]; simp; nlinarith
      · rw [T_single]; simp; nlinarith
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

/-! ### Splitting the input `w # y` -/

/-- **Right-tagged encoding of a certificate.** For a list $y$ of bits, its right-tagged encoding
is the list of symbols of the work alphabet $G$ obtained by replacing each bit $b$ of $y$ with
the right symbol $\mathrm{inr}(\mathrm{some}\ b)$. This is how the certificate appears after the
separator in the pair encoding of a formula and a certificate. -/
def encR (y : List Bool) : List G := y.map fun b => .inr (some b)

/-- **Splitting the verifier input.** For all bit strings $w$ and $y$, the verifier program
leads in exactly $(|w| + 1) + (|y| + 1) + (|w| + 1) + (|y| + 1)$ steps from the configuration at
label $\mathsf{read1}$ with empty machine state, the input stack holding (from the top) the bits
$b$ of $w$ as $\mathrm{inl}\,b$, the separator $\mathrm{inr}\,\mathrm{none}$ and the bits $b$ of
$y$ as $\mathrm{inr}(\mathrm{some}\,b)$, and all other stacks empty, to the configuration at label
$\mathsf{c0}(\mathrm{false})$ with empty machine state, the input stack holding the bits $b$ of
$w$ as $\mathrm{inl}\,b$, the stack $B$ holding the bits $b$ of $y$ as $\mathrm{inl}\,b$ (both from
the top in order), and the stacks $F$, $A$ and the output stack empty.

The four phases stash $w$ on $F$ and $y$ on $A$, then move them back onto the input stack and
$B$. -/
theorem prefix_run (w y : List Bool) :
    TM2Program.Run prog (w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1))
      ⟨some .read1, none, stk (mkV (enc w ++ .inr none :: encR y) [] [] []) []⟩
      ⟨some (.c0 false), none, stk (mkV (enc w) [] [] (enc y)) []⟩ := by
  have h₁ := loop_run .inp gRead1 (some .F) .read1 .read2 rfl (by simp) [] (enc w) (enc w)
    (.inr none :: encR y) none (mkV (enc w ++ .inr none :: encR y) [] [] [])
    (by simp [enc, gRead1]) rfl rfl
  have h₂ := loop_run .inp gRead2 (some .A) .read2 .back1 rfl (by simp) [] (encR y) (enc y) []
    (some (.inr none)) (mkV (encR y) (enc w).reverse [] []) (by simp [encR, enc, gRead2]) rfl
    (by simp [mkV])
  have h₃ := loop_run .F some (some .inp) .back1 .back2 rfl (by simp) [] (enc w).reverse
    (enc w).reverse [] none (mkV [] (enc w).reverse (enc y).reverse []) rfl rfl (by simp [mkV])
  have h₄ := loop_run .A some (some .B) .back2 (.c0 false) rfl (by simp) [] (enc y).reverse
    (enc y).reverse [] none (mkV (enc w) [] (enc y).reverse []) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil,
    update_mkV_inp, update_mkV_F, update_mkV_A, update_mkV_B, mkV, List.append_nil,
    List.reverse_reverse] at h₁ h₂ h₃ h₄
  exact (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by simp [encR])

theorem initList_tm (l : List G) :
    initList tm l = ⟨some .read1, none, stk (mkV l [] [] []) []⟩ := by
  simp only [initList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

theorem haltList_tm (l : List Bool) :
    haltList tm l = ⟨none, none, stk (mkV [] [] [] []) l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

/-- **Step count of the dense CNF-SAT verifier.** For bit lists $w$ (a formula) and $y$ (an
assignment), the number $(|w| + 1) + (|y| + 1) + (|w| + 1) + (|y| + 1) + T + 1$, where $T$ is
the step count of the main scan on $w$ started with all of $y$ unused, no assignment bits used
and the clause flag false.

This is the exact number of steps of the verifier machine on input $w \# y$: four passes that
stash and restore $w$ and $y$, the main scan, and one output step. -/
def totalSteps (w y : List Bool) : ℕ :=
  w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1) + T w y [] false + 1

/-- **Time bound of the dense CNF-SAT verifier.** The polynomial $2(n + 5)^2$ over $\mathbb{N}$
in one variable $n$. It bounds the running time of the verifier on inputs of length $n$; for a
formula $w$ and an assignment $y$, the input $w \# y$ has length $n = |w| + 1 + |y|$. -/
noncomputable def time : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.X + Polynomial.C 5) ^ 2

/-- **Polynomial-time verifier for dense CNF-SAT.** The verifier machine computes, in polynomial
time, the map sending a pair $(w, y)$ of bit lists to the Boolean $\mathrm{check}(w, y)$, which
is true exactly when $y$ satisfies the CNF formula decoded from $w$. The pair is given as the
input $w \# y$ (the bits of $w$, a separator $\#$, then the bits of $y$), the output is the
single bit $\mathrm{check}(w, y)$, and the machine halts within $2(n + 5)^2$ steps on an input
of length $n$. -/
noncomputable def verifier :
    TM2ComputableInPolyTime pairEncode (fun b : Bool => [b]) (fun p => check p.1 p.2) where
  tm := tm
  inputAlphabet := Equiv.refl G
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun p => by
    obtain ⟨w, y⟩ := p
    have hin : List.map (Equiv.refl G).invFun (pairEncode (w, y)) =
        enc w ++ .inr none :: encR y := by
      simp [pairEncode, enc, encR]
    have hlen : (pairEncode (w, y)).length = w.length + 1 + y.length := by
      simp only [pairEncode, List.length_append, List.length_map, List.length_cons]
      omega
    have hrun := ((prefix_run w y).trans (scan w y [] false none)).trans (finish_run (check w y))
    unfold TM2OutputsInTime
    refine { steps := totalSteps w y, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [hin, initList_tm, Option.map_some, haltList_tm]
      exact hrun
    · rw [hlen, totalSteps]
      have hT := T_le w y [] false
      simp only [time, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, List.length_nil] at hT ⊢
      nlinarith

end Verifier

end Cslib.Complexity.DenseSAT
