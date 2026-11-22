/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.Ring
public import CSLibExt.Computability.Complexity.DenseToBinary

/-!
# A polynomial-time machine for the dense-to-binary SAT translation

`ToBinary.computable : TM2ComputableInPolyTime id id binConv`, where
`binConv w = conv w.reverse false 0 0 0 []` (`DenseToBinary`): the machine first moves its input
onto a stash (reversing it), then runs `conv` with the clause state in its finite control and the
counters `n`, `k`, `m` on unit stacks, and finally empties every stack but the output. On an input
of length `L` it halts within `2 L² + 10 L + 11` steps.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT.ToBinary

open Turing MetaMathlibExt TM2Program Function

/-- **The dense-to-binary translation on bit strings.** The translation of a bit string $w$ is the
backwards dense-to-binary translation applied to the reversal of $w$, started with no clause open,
with its literal, slot and clause counters all equal to $0$, and with empty output. -/
def binConv (w : List Bool) : List Bool := conv w.reverse false 0 0 0 []

/-- **Stacks of the dense-to-binary machine.** The stack names of the Turing machine for the
dense-to-binary translation form a type with exactly seven elements: the input, a stash, the
output, the three counters $n$, $k$ and $m$, and a scratch stack $t$. -/
inductive Stk | inp | stash | out | N | K | M | T
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, Stk.stash, Stk.out, Stk.N, Stk.K, Stk.M, Stk.T], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Labels of the dense-to-binary converter.** The labels of the dense-to-binary converter
program are the moving label $\mathrm{mv}$; the reading label $\mathrm{rd}(\iota)$ for a Boolean
$\iota$; the second-read label $\mathrm{rd2}(\iota, s)$ for Booleans $\iota$ and $s$; the two
literal labels $\mathrm{litA}$ and $\mathrm{litB}$; the two closing labels $\mathrm{eN}$ and
$\mathrm{eK}$; the clearing label $\mathrm{fK}(\iota)$ for a Boolean $\iota$; the literal-count
label $\mathrm{fN}$; and the clause-count label $\mathrm{fM}$. Equality of labels is decidable.

Here $\iota$ records whether a clause is open, and $s$ is the first bit read of a slot. -/
inductive Lab
  | mv
  | rd (ins : Bool)
  | rd2 (ins s : Bool)
  | litA
  | litB
  | eN
  | eK
  | fK (ins : Bool)
  | fN
  | fM
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.mv, .rd false, .rd true, .rd2 false false, .rd2 false true, .rd2 true false,
    .rd2 true true, .litA, .litB, .eN, .eK, .fK false, .fK true, .fN, .fM], by decide⟩
  complete := fun l => by
    cases l with
    | rd ins => cases ins <;> decide
    | rd2 ins s => cases ins <;> cases s <;> decide
    | fK ins => cases ins <;> decide
    | _ => decide

/-- **Stack contents of the converter.** For bit strings $i$, $a$, $o$ and natural numbers
$n, k, m, t$, this stack assignment gives the input stack $i$, the stash $a$, the output stack $o$,
and the counter stacks $N$, $K$, $M$ and the scratch stack $T$ respectively $n$, $k$, $m$ and $t$
copies of $1$ (true). -/
def stk (i a o : List Bool) (n k m t : ℕ) : Stk → List Bool
  | .inp => i
  | .stash => a
  | .out => o
  | .N => List.replicate n true
  | .K => List.replicate k true
  | .M => List.replicate m true
  | .T => List.replicate t true

section Upd

variable (i a o l : List Bool) (n k m t j : ℕ)

@[simp] theorem upd_inp : update (stk i a o n k m t) .inp l = stk l a o n k m t := by
  funext s; cases s <;> rfl
@[simp] theorem upd_stash : update (stk i a o n k m t) .stash l = stk i l o n k m t := by
  funext s; cases s <;> rfl
@[simp] theorem upd_out : update (stk i a o n k m t) .out l = stk i a l n k m t := by
  funext s; cases s <;> rfl
@[simp] theorem upd_N : update (stk i a o n k m t) .N (List.replicate j true) =
    stk i a o j k m t := by funext s; cases s <;> rfl
@[simp] theorem upd_K : update (stk i a o n k m t) .K (List.replicate j true) =
    stk i a o n j m t := by funext s; cases s <;> rfl
@[simp] theorem upd_M : update (stk i a o n k m t) .M (List.replicate j true) =
    stk i a o n k j t := by funext s; cases s <;> rfl
@[simp] theorem upd_T : update (stk i a o n k m t) .T (List.replicate j true) =
    stk i a o n k m j := by funext s; cases s <;> rfl
@[simp] theorem upd_N' : update (stk i a o n k m t) .N (true :: List.replicate j true) =
    stk i a o (j + 1) k m t := by funext s; cases s <;> rfl
@[simp] theorem upd_K' : update (stk i a o n k m t) .K (true :: List.replicate j true) =
    stk i a o n (j + 1) m t := by funext s; cases s <;> rfl
@[simp] theorem upd_M' : update (stk i a o n k m t) .M (true :: List.replicate j true) =
    stk i a o n k (j + 1) t := by funext s; cases s <;> rfl
@[simp] theorem upd_T' : update (stk i a o n k m t) .T (true :: List.replicate j true) =
    stk i a o n k m (j + 1) := by funext s; cases s <;> rfl

@[simp] theorem upd_N0 : update (stk i a o n k m t) .N [] = stk i a o 0 k m t := by
  funext s; cases s <;> rfl
@[simp] theorem upd_K0 : update (stk i a o n k m t) .K [] = stk i a o n 0 m t := by
  funext s; cases s <;> rfl
@[simp] theorem upd_M0 : update (stk i a o n k m t) .M [] = stk i a o n k 0 t := by
  funext s; cases s <;> rfl
@[simp] theorem upd_T0 : update (stk i a o n k m t) .T [] = stk i a o n k m 0 := by
  funext s; cases s <;> rfl

@[simp] theorem stk_inp : stk i a o n k m t .inp = i := rfl
@[simp] theorem stk_stash : stk i a o n k m t .stash = a := rfl
@[simp] theorem stk_out : stk i a o n k m t .out = o := rfl
@[simp] theorem stk_N : stk i a o n k m t .N = List.replicate n true := rfl
@[simp] theorem stk_K : stk i a o n k m t .K = List.replicate k true := rfl
@[simp] theorem stk_M : stk i a o n k m t .M = List.replicate m true := rfl
@[simp] theorem stk_T : stk i a o n k m t .T = List.replicate t true := rfl

end Upd

open TM2.Stmt in
/-- **The dense-to-binary converter program.** The program uses an input stack, a stash, an
output stack, unary counter stacks $N$, $K$, $M$ and a scratch stack $T$; each label first pops
one stack and keeps the popped bit (or nothing, if the stack was empty) as its internal state.
Below, $\iota$ says whether a clause is open, $0$ is false and $1$ is true.

Moving: pop the input; if a bit $b$ was popped, push $b$ onto the stash and repeat, otherwise go to
reading with $\iota$ false.

Reading with $\iota$: pop the stash; if a bit $s$ was popped, go to the second read with $\iota$
and $s$, otherwise go to clearing with $\iota$.

Second read with $\iota$ and $s$: pop the stash. If it was empty, go to clearing with $\iota$. If
it gave $0$: when $s = 1$, push $1$ onto $K$ and go to reading with $\iota$; when $s = 0$ and
$\iota$ is true, push $0$ onto the output and go to the first closing label; when $s = 0$ and
$\iota$ is false, go to the second closing label. If it gave $1$: when $\iota$ is true, push
$\lnot s$ and then $0$ onto the output and go to the first literal label; otherwise go to reading
with $\iota$ false.

First literal label: pop $K$; if a bit was popped, push $1$ twice onto the output and $1$ onto $T$
and repeat, otherwise go to the second literal label.

Second literal label: pop $T$; if a bit was popped, push $1$ onto $K$ and repeat, otherwise push
$1$ onto $N$, then $1$ onto $K$, and go to reading with $\iota$ true.

First closing label: pop $N$; if a bit was popped, push $1$ onto the output and repeat, otherwise
go to the second closing label.

Second closing label: pop $K$; if a bit was popped, repeat, otherwise push $1$ onto $M$ and go to
reading with $\iota$ true.

Clearing with $\iota$: pop $K$; if a bit was popped, repeat, otherwise push $0$ onto the output and
go to the literal-count label if $\iota$ is true and to the clause-count label otherwise.

Literal-count label: pop $N$; if a bit was popped, push $1$ onto the output and repeat, otherwise
push $0$ onto the output and go to the clause-count label.

Clause-count label: pop $M$; if a bit was popped, push $1$ onto the output and repeat, otherwise
halt. -/
def prog : Lab → TM2.Stmt (fun _ : Stk => Bool) Lab (Option Bool)
  | .mv => pop .inp (fun _ o => o) <| branch (fun s => s.isSome)
      (push .stash (fun s => s.getD false) <| goto fun _ => .mv) (goto fun _ => .rd false)
  | .rd ins => pop .stash (fun _ o => o) <| branch (fun s => s.isSome)
      (goto fun s => .rd2 ins (s.getD false)) (goto fun _ => .fK ins)
  | .rd2 ins s => pop .stash (fun _ o => o) <| branch (fun v => v.isNone) (goto fun _ => .fK ins) <|
      branch (fun v => v == some false)
        (if s then (push .K (fun _ => true) <| goto fun _ => .rd ins)
          else if ins then (push .out (fun _ => false) <| goto fun _ => .eN)
          else goto fun _ => .eK)
        (if ins then (push .out (fun _ => !s) <| push .out (fun _ => false) <| goto fun _ => .litA)
          else goto fun _ => .rd false)
  | .litA => pop .K (fun _ o => o) <| branch (fun v => v.isSome)
      (push .out (fun _ => true) <| push .out (fun _ => true) <| push .T (fun _ => true) <|
        goto fun _ => .litA)
      (goto fun _ => .litB)
  | .litB => pop .T (fun _ o => o) <| branch (fun v => v.isSome)
      (push .K (fun _ => true) <| goto fun _ => .litB)
      (push .N (fun _ => true) <| push .K (fun _ => true) <| goto fun _ => .rd true)
  | .eN => pop .N (fun _ o => o) <| branch (fun v => v.isSome)
      (push .out (fun _ => true) <| goto fun _ => .eN) (goto fun _ => .eK)
  | .eK => pop .K (fun _ o => o) <| branch (fun v => v.isSome)
      (goto fun _ => .eK) (push .M (fun _ => true) <| goto fun _ => .rd true)
  | .fK ins => pop .K (fun _ o => o) <| branch (fun v => v.isSome)
      (goto fun _ => .fK ins)
      (push .out (fun _ => false) <| goto fun _ => if ins then .fN else .fM)
  | .fN => pop .N (fun _ o => o) <| branch (fun v => v.isSome)
      (push .out (fun _ => true) <| goto fun _ => .fN)
      (push .out (fun _ => false) <| goto fun _ => .fM)
  | .fM => pop .M (fun _ o => o) <| branch (fun v => v.isSome)
      (push .out (fun _ => true) <| goto fun _ => .fM) halt

/-- **Exact runs of the dense-to-binary converter.** For a natural number $n$ and configurations
$c$ and $d$ of the converter program, $c$ leads to $d$ in exactly $n$ steps when the program,
started at $c$, is at configuration $d$ after exactly $n$ steps. -/
abbrev Run (n : ℕ) (c d : TM2.Cfg (fun _ : Stk => Bool) Lab (Option Bool)) : Prop :=
  TM2Program.Run prog n c d

/-! ### Loops -/

/-- **Moving the input onto the stash.** Let $l$, $a$, $o$ be bit strings and $v$ an optional
bit, and list stacks top first. Started at the moving label with internal state $v$, input stack
$l$, stash $a$, output stack $o$, empty counter stacks $N$, $K$, $M$ and empty scratch stack $T$,
the dense-to-binary converter reaches, in exactly $|l| + 1$ steps, the label for reading with no
clause open, with no internal state, an empty input stack, the reversal of $l$ followed by $a$ on
the stash, output stack $o$, and $N$, $K$, $M$, $T$ still empty. -/
theorem mv_run (l : List Bool) : ∀ (a o : List Bool) (v : Option Bool),
    Run (l.length + 1) ⟨some .mv, v, stk l a o 0 0 0 0⟩
      ⟨some (.rd false), none, stk [] (l.reverse ++ a) o 0 0 0 0⟩ := by
  induction l with
  | nil => intro a o v; exact Run.single (by simp [prog, TM2.stepAux])
  | cons b l ih =>
      intro a o v
      have h := ih (b :: a) o (some b)
      rw [show l.reverse ++ b :: a = (b :: l).reverse ++ a by simp] at h
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux]) h

theorem litA_run (i a o : List Bool) (n m : ℕ) : ∀ (k t : ℕ) (v : Option Bool),
    Run (k + 1) ⟨some .litA, v, stk i a o n k m t⟩
      ⟨some .litB, none, stk i a (rep [true, true] k ++ o) n 0 m (t + k)⟩ := by
  intro k
  induction k generalizing o with
  | zero => intro t v; exact Run.single (by simp [prog, TM2.stepAux, rep])
  | succ k ih =>
      intro t v
      have h := ih (true :: true :: o) (t + 1) (some true)
      rw [show rep [true, true] k ++ true :: true :: o = rep [true, true] (k + 1) ++ o by
        rw [rep_succ']; simp, show t + 1 + k = t + (k + 1) by omega] at h
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) h

theorem litB_run (i a o : List Bool) (n m : ℕ) : ∀ (t k : ℕ) (v : Option Bool),
    Run (t + 1) ⟨some .litB, v, stk i a o n k m t⟩
      ⟨some (.rd true), none, stk i a o (n + 1) (k + t + 1) m 0⟩ := by
  intro t
  induction t with
  | zero => intro k v; exact Run.single (by simp [prog, TM2.stepAux, ← List.replicate_succ])
  | succ t ih =>
      intro k v
      have h := ih (k + 1) (some true)
      rw [show k + 1 + t + 1 = k + (t + 1) + 1 by omega] at h
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) h


theorem eN_run (i a : List Bool) (k m t : ℕ) : ∀ (n : ℕ) (o : List Bool) (v : Option Bool),
    Run (n + 1) ⟨some .eN, v, stk i a o n k m t⟩
      ⟨some .eK, none, stk i a (List.replicate n true ++ o) 0 k m t⟩ := by
  intro n
  induction n with
  | zero => intro o v; exact Run.single (by simp [prog, TM2.stepAux])
  | succ n ih =>
      intro o v
      have h := ih (true :: o) (some true)
      rw [show List.replicate n true ++ true :: o = List.replicate (n + 1) true ++ o by
        simp [List.replicate_succ']] at h
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) h

theorem eK_run (i a o : List Bool) (n m t : ℕ) : ∀ (k : ℕ) (v : Option Bool),
    Run (k + 1) ⟨some .eK, v, stk i a o n k m t⟩
      ⟨some (.rd true), none, stk i a o n 0 (m + 1) t⟩ := by
  intro k
  induction k with
  | zero => intro v; exact Run.single (by simp [prog, TM2.stepAux, ← List.replicate_succ])
  | succ k ih =>
      intro v
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) (ih (some true))

theorem fK_run (i a o : List Bool) (n m t : ℕ) (ins : Bool) : ∀ (k : ℕ) (v : Option Bool),
    Run (k + 1) ⟨some (.fK ins), v, stk i a o n k m t⟩
      ⟨some (if ins then .fN else .fM), none, stk i a (false :: o) n 0 m t⟩ := by
  intro k
  induction k with
  | zero => intro v; exact Run.single (by simp [prog, TM2.stepAux])
  | succ k ih =>
      intro v
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) (ih (some true))

theorem fN_run (i a : List Bool) (k m t : ℕ) : ∀ (n : ℕ) (o : List Bool) (v : Option Bool),
    Run (n + 1) ⟨some .fN, v, stk i a o n k m t⟩
      ⟨some .fM, none, stk i a (false :: (List.replicate n true ++ o)) 0 k m t⟩ := by
  intro n
  induction n with
  | zero => intro o v; exact Run.single (by simp [prog, TM2.stepAux])
  | succ n ih =>
      intro o v
      have h := ih (true :: o) (some true)
      rw [show List.replicate n true ++ true :: o = List.replicate (n + 1) true ++ o by
        simp [List.replicate_succ']] at h
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) h

theorem fM_run (i a : List Bool) (n k t : ℕ) : ∀ (m : ℕ) (o : List Bool) (v : Option Bool),
    Run (m + 1) ⟨some .fM, v, stk i a o n k m t⟩
      ⟨none, none, stk i a (List.replicate m true ++ o) n k 0 t⟩ := by
  intro m
  induction m with
  | zero => intro o v; exact Run.single (by simp [prog, TM2.stepAux])
  | succ m ih =>
      intro o v
      have h := ih (true :: o) (some true)
      rw [show List.replicate m true ++ true :: o = List.replicate (m + 1) true ++ o by
        simp [List.replicate_succ']] at h
      exact Run.head (by simp [TM2.step, prog, TM2.stepAux, List.replicate_succ]) h

/-- **The converter's final phase.** Write $0$ for false, $1$ for true and $1^j$ for $j$ copies
of $1$. Let $o$ be a bit string, $\iota$ a flag saying whether a clause is open, and $n, k, m$
natural numbers with $n = 0$ if no clause is open; let $c = n + 1$ if a clause is open and $c = 0$
otherwise. Started at the label that clears the slot counter at the end, for the flag $\iota$, with
empty internal state, empty input and stash, output $o$, literal, slot and clause counter stacks
holding $n$, $k$ and $m$ ones respectively, and an empty scratch stack, the converter reaches in
exactly $(k + 1) + c + (m + 1)$ steps the halting configuration with empty internal state, every
stack but the output empty, and output $1^m 0 1^n 0 o$ if a clause is open and $1^m 0 o$ otherwise
(listed from the top of the stack). -/
theorem fin_run (o : List Bool) (ins : Bool) (n k m : ℕ) (hn : ins = false → n = 0) :
    Run ((k + 1) + (if ins then n + 1 else 0) + (m + 1))
      ⟨some (.fK ins), none, stk [] [] o n k m 0⟩
      ⟨none, none, stk [] [] (List.replicate m true ++ false ::
        (if ins then endClause n o else o)) 0 0 0 0⟩ := by
  have r1 := fK_run [] [] o n m 0 ins k none
  cases ins with
  | false =>
      obtain rfl := hn rfl
      have r3 := fM_run [] [] 0 0 0 m (false :: o) none
      simpa using r1.trans r3
  | true =>
      have r2 := fN_run [] [] 0 m 0 n (false :: o) none
      have r3 := fM_run [] [] 0 0 0 m (false :: (List.replicate n true ++ false :: o)) none
      simpa [endClause, Nat.add_assoc] using (r1.trans r2).trans r3

/-! ### The main loop -/

/-- **Step count of the main loop.** Write $0$ for false, $1$ for true, and $xyr$ for the bit
string whose first two bits are $x, y$ followed by $r$. For a bit string $l$, a flag $\iota$
(whether a clause is open) and natural numbers $n, k, m$, let $c = n + 1$ if $\iota$ is true and
$c = 0$ otherwise. The step count $T(l, \iota, n, k, m)$ is defined by recursion on $l$:
$T(00r, \iota, n, k, m) = 2 + c + (k + 1) + T(r, 1, 0, 0, m + 1)$;
$T(10r, \iota, n, k, m) = 2 + T(r, \iota, n, k + 1, m)$;
for every bit $s$, $T(s1r, \iota, n, k, m)$ is $2 + 2(k + 1) + T(r, 1, n + 1, k + 1, m)$ if $\iota$
is true and $2 + T(r, 0, n, k, m)$ otherwise; on a one-bit string $T = 2 + (k + 1) + c + (m + 1)$;
and on the empty string $T = 1 + (k + 1) + c + (m + 1)$. -/
def convT : List Bool → Bool → ℕ → ℕ → ℕ → ℕ
  | false :: false :: r, ins, n, k, m =>
      2 + (if ins then n + 1 else 0) + (k + 1) + convT r true 0 0 (m + 1)
  | true :: false :: r, ins, n, k, m => 2 + convT r ins n (k + 1) m
  | _ :: true :: r, ins, n, k, m =>
      if ins then 2 + 2 * (k + 1) + convT r true (n + 1) (k + 1) m else 2 + convT r false n k m
  | [_], ins, n, k, m => 2 + ((k + 1) + (if ins then n + 1 else 0) + (m + 1))
  | _, ins, n, k, m => 1 + ((k + 1) + (if ins then n + 1 else 0) + (m + 1))

theorem main_run : ∀ (l : List Bool) (ins : Bool) (n k m : ℕ) (o : List Bool) (v : Option Bool),
    (ins = false → n = 0) →
    Run (convT l ins n k m) ⟨some (.rd ins), v, stk [] l o n k m 0⟩
      ⟨none, none, stk [] [] (conv l ins n k m o) 0 0 0 0⟩
  | false :: false :: r, ins, n, k, m, o, v, hn => by
      have s1 : Run 2 ⟨some (.rd ins), v, stk [] (false :: false :: r) o n k m 0⟩
          ⟨some (if ins then .eN else .eK), some false,
            stk [] r (if ins then false :: o else o) n k m 0⟩ := by
        refine Run.head (d := ⟨some (.rd2 ins false), some false, stk [] (false :: r) o n k m 0⟩)
          (by simp [TM2.step, prog, TM2.stepAux]) (Run.single ?_)
        cases ins <;> simp [prog, TM2.stepAux]
      have ih := main_run r true 0 0 (m + 1) (if ins then endClause n o else o) none (by simp)
      cases ins with
      | false =>
          obtain rfl := hn rfl
          have r2 := eK_run [] r o 0 m 0 k (some false)
          simp only [convT, conv, Bool.false_eq_true, ite_false] at ih ⊢
          exact ((s1.trans r2).trans ih).of_eq (by omega)
      | true =>
          have r2 := eN_run [] r k m 0 n (false :: o) (some false)
          have r3 := eK_run [] r (List.replicate n true ++ false :: o) 0 m 0 k none
          simp only [convT, conv, ite_true] at ih ⊢
          simp only [endClause] at ih
          exact (((s1.trans r2).trans r3).trans ih).of_eq (by omega)
  | true :: false :: r, ins, n, k, m, o, v, hn => by
      have s1 : Run 2 ⟨some (.rd ins), v, stk [] (true :: false :: r) o n k m 0⟩
          ⟨some (.rd ins), some false, stk [] r o n (k + 1) m 0⟩ := by
        refine Run.head (d := ⟨some (.rd2 ins true), some true, stk [] (false :: r) o n k m 0⟩)
          (by simp [TM2.step, prog, TM2.stepAux]) (Run.single ?_)
        simp [prog, TM2.stepAux]
      have ih := main_run r ins n (k + 1) m o (some false) hn
      simp only [convT, conv]
      exact (s1.trans ih).of_eq (by omega)
  | s :: true :: r, ins, n, k, m, o, v, hn => by
      cases ins with
      | false =>
          have s1 : Run 2 ⟨some (.rd false), v, stk [] (s :: true :: r) o n k m 0⟩
              ⟨some (.rd false), some true, stk [] r o n k m 0⟩ := by
            refine Run.head (d := ⟨some (.rd2 false s), some s, stk [] (true :: r) o n k m 0⟩)
              (by simp [TM2.step, prog, TM2.stepAux]) (Run.single ?_)
            simp [prog, TM2.stepAux]
          have ih := main_run r false n k m o (some true) hn
          simp only [convT, conv, Bool.false_eq_true, ite_false]
          exact (s1.trans ih).of_eq (by omega)
      | true =>
          have s1 : Run 2 ⟨some (.rd true), v, stk [] (s :: true :: r) o n k m 0⟩
              ⟨some .litA, some true, stk [] r (false :: (!s) :: o) n k m 0⟩ := by
            refine Run.head (d := ⟨some (.rd2 true s), some s, stk [] (true :: r) o n k m 0⟩)
              (by simp [TM2.step, prog, TM2.stepAux]) (Run.single ?_)
            simp [prog, TM2.stepAux]
          have r2 := litA_run [] r (false :: (!s) :: o) n m k 0 (some true)
          have r3 := litB_run [] r (rep [true, true] k ++ false :: (!s) :: o) n m k 0 none
          have ih := main_run r true (n + 1) (k + 1) m (rep [true, true] k ++ false :: (!s) :: o)
            none (by simp)
          simp only [convT, conv, ite_true, Nat.zero_add] at ih r2 r3 ⊢
          exact (((s1.trans r2).trans r3).trans ih).of_eq (by omega)
  | [x], ins, n, k, m, o, v, hn => by
      have s1 : Run 2 ⟨some (.rd ins), v, stk [] [x] o n k m 0⟩
          ⟨some (.fK ins), none, stk [] [] o n k m 0⟩ := by
        refine Run.head (d := ⟨some (.rd2 ins x), some x, stk [] [] o n k m 0⟩)
          (by simp [TM2.step, prog, TM2.stepAux]) (Run.single ?_)
        simp [prog, TM2.stepAux]
      have r2 := fin_run o ins n k m hn
      simp only [convT, conv]
      exact s1.trans r2
  | [], ins, n, k, m, o, v, hn => by
      have s1 : Run 1 ⟨some (.rd ins), v, stk [] [] o n k m 0⟩
          ⟨some (.fK ins), none, stk [] [] o n k m 0⟩ :=
        Run.single (by simp [prog, TM2.stepAux])
      have r2 := fin_run o ins n k m hn
      simp only [convT, conv]
      exact s1.trans r2

/-! ### Time bound and the packaged machine -/

/-- **Step bound for the main loop.** For every bit string $l$, whether or not a clause is open, and
all natural numbers $n, k, m, Q$ with $|l| + n + k + m \le Q$, the exact step count of the main loop
on stash $l$ with literal, slot and clause counters $n, k, m$ is at most
$(|l| + 1)(2Q + 6) + Q + 4$. -/
theorem convT_le : ∀ (l : List Bool) (ins : Bool) (n k m Q : ℕ),
    l.length + n + k + m ≤ Q → convT l ins n k m ≤ (l.length + 1) * (2 * Q + 6) + Q + 4
  | false :: false :: r, ins, n, k, m, Q, hQ => by
      have h := convT_le r true 0 0 (m + 1) Q (by simp at hQ; omega)
      have e : (r.length + 2 + 1) * (2 * Q + 6) =
          (r.length + 1) * (2 * Q + 6) + 2 * (2 * Q + 6) := by ring
      simp only [convT, List.length_cons] at hQ ⊢
      rw [show r.length + 1 + 1 + 1 = r.length + 2 + 1 by omega, e]
      generalize (r.length + 1) * (2 * Q + 6) = A at h ⊢
      split <;> omega
  | true :: false :: r, ins, n, k, m, Q, hQ => by
      have h := convT_le r ins n (k + 1) m Q (by simp at hQ; omega)
      have e : (r.length + 2 + 1) * (2 * Q + 6) =
          (r.length + 1) * (2 * Q + 6) + 2 * (2 * Q + 6) := by ring
      simp only [convT, List.length_cons] at hQ ⊢
      rw [show r.length + 1 + 1 + 1 = r.length + 2 + 1 by omega, e]
      generalize (r.length + 1) * (2 * Q + 6) = A at h ⊢
      omega
  | s :: true :: r, ins, n, k, m, Q, hQ => by
      have e : (r.length + 2 + 1) * (2 * Q + 6) =
          (r.length + 1) * (2 * Q + 6) + 2 * (2 * Q + 6) := by ring
      simp only [List.length_cons] at hQ
      cases ins with
      | false =>
          have h := convT_le r false n k m Q (by omega)
          simp only [convT, Bool.false_eq_true, ite_false, List.length_cons]
          rw [show r.length + 1 + 1 + 1 = r.length + 2 + 1 by omega, e]
          generalize (r.length + 1) * (2 * Q + 6) = A at h ⊢
          omega
      | true =>
          have h := convT_le r true (n + 1) (k + 1) m Q (by omega)
          simp only [convT, ite_true, List.length_cons]
          rw [show r.length + 1 + 1 + 1 = r.length + 2 + 1 by omega, e]
          generalize (r.length + 1) * (2 * Q + 6) = A at h ⊢
          omega
  | [x], ins, n, k, m, Q, hQ => by
      simp only [convT, List.length_cons, List.length_nil] at hQ ⊢
      have : 2 * Q + 6 ≤ (0 + 1 + 1) * (2 * Q + 6) := by omega
      split <;> omega
  | [], ins, n, k, m, Q, hQ => by
      simp only [convT, List.length_nil] at hQ ⊢
      split <;> omega

/-- **The dense-to-binary machine.** The multi-stack Turing machine whose stacks are indexed by
the stack names (input, stash, output, the counters $n$, $k$, $m$ and the scratch $t$), each
with the Booleans as alphabet. It reads its input from the input stack and leaves its output on
the output stack; its labels are the program labels, starting at the label that moves the input
onto the stash; its internal state is an optional Boolean, initially empty; and each label runs
the corresponding statement of the program. -/
def tm : FinTM2 where
  K := Stk
  k₀ := .inp
  k₁ := .out
  Γ := fun _ => Bool
  Λ := Lab
  main := .mv
  σ := Option Bool
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

theorem initList_tm (w : List Bool) : initList tm w = ⟨some .mv, none, stk w [] [] 0 0 0 0⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (w : List Bool) : haltList tm w = ⟨none, none, stk [] [] w 0 0 0 0⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

/-- **The dense-to-binary translation on raw bits is polynomial-time.** There is a finite
multi-stack Turing machine whose input and output alphabets are the bits such that, for every bit
string $w$ of length $L$, the machine started on input $w$ halts within $2L^2 + 10L + 11$ steps with
the dense-to-binary translation of $w$ on its output stack and all other stacks empty. -/
noncomputable def computable :
    TM2ComputableInPolyTime (fun l : List Bool => l) (fun l : List Bool => l) binConv where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 10 * Polynomial.X + Polynomial.C 11
  outputsFun := fun w => by
    unfold TM2OutputsInTime
    refine ⟨⟨w.length + 1 + convT w.reverse false 0 0 0, ?_⟩, ?_⟩
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [List.map_id, List.map_id, initList_tm, Option.map_some, haltList_tm]
      have h1 := mv_run w [] [] none
      rw [List.append_nil] at h1
      exact h1.trans (main_run w.reverse false 0 0 0 [] none (fun _ => rfl))
    · have h := convT_le w.reverse false 0 0 0 w.length (by simp)
      have e : (w.length + 1) * (2 * w.length + 6) = 2 * w.length ^ 2 + 8 * w.length + 6 := by
        ring
      simp only [List.length_reverse, e] at h
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
      generalize w.length ^ 2 = S at h ⊢
      omega

end Cslib.Complexity.DenseSAT.ToBinary
