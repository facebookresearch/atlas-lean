/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `D3OneHot.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/D3OneHot.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib); the generic counter view (`[LIB]`) moved to `CounterView`; module docstring
rewritten for this repository (the source's notes and status lines dropped), missing docstrings
added, long lines wrapped.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.CounterView
public import CSLibExt.Computability.Complexity.CookLevin.Family

/-!
# Cook-Levin: the cell one-hot family

Built on the shared counter view `CounterView`. For every `t ≤ T`, `k < KK`, `j < H`, with cell base `B = cIdx H t k j 0`: the
at-least-one clause `⋁_{x<g} C[B+x]`, then the at-most-one clauses `¬C[B+x] ∨ ¬C[B+y]` for
`x < y < g`, each dense over all `V = (T+1)·W` variables. The loops over `t`, `k` and `j` run at
run time (nested `forHead` loops on counters). The module also provides the dense-literal routine
and cell-layout lemmas (`base_le`, `kb_le`, ...) that `Shift` and `Accept` reuse. The final formula
does not use the one-hot family itself (the soundness argument does not need it).
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.OneHot

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc Inc.le encodeClause_denseClause gapEnc_shift inc_of_mono
  denseClause)
open Cslib.Complexity.CookLevin.CounterView

/-! ## [FAM] The family (pure specification) -/

section Spec

/-- **At-least-one literals of a cell.** For $g, B \in \mathbb{N}$, the list of the $g$ positive
literals on the variables $v_B, v_{B+1}, \dots, v_{B+g-1}$, in this order, each given as the pair
of its variable index and the sign true; these are the literals of the clause
$v_B \lor \dots \lor v_{B+g-1}$. -/
def aloLits (g B : ℕ) : List (ℕ × Bool) := (List.range g).map fun x => (B + x, true)

/-- **At-most-one literals for a pair.** For $B, x, y \in \mathbb{N}$, the two-element list of the
negative literals on the variables $v_{B+x}$ and $v_{B+y}$, in this order, each given as the pair of
its variable index and the sign false; these are the literals of the clause
$\neg v_{B+x} \lor \neg v_{B+y}$. It is used for pairs $x < y$. -/
def amoLits (B x y : ℕ) : List (ℕ × Bool) := [(B + x, false), (B + y, false)]

/-- **At-most-one clauses of the first rows of a cell.** For natural numbers $V$, $B$ and $y$,
write $p_i$ for the variable with index $i$. This is the CNF formula listing, for
$y' = 0, 1, \dots, y - 1$ in turn and within each for $x = 0, 1, \dots, y' - 1$ in turn, the
dense clause over $V$ variables built from the literals $\lnot p_{B + x}$ and $\lnot p_{B + y'}$:
its slot $i < V$ holds the literal on $p_i$ if there is one and is empty otherwise. -/
def rowsCNF (V B y : ℕ) : CNF :=
  (List.range y).flatMap fun y' => (List.range y').map fun x => denseClause V (amoLits B x y')

/-- **One-hot clauses of a cell.** For $g, V, B \in \mathbb{N}$, the CNF formula whose first clause
is the at-least-one clause $v_B \lor \dots \lor v_{B+g-1}$ and whose remaining clauses are the
at-most-one clauses $\neg v_{B+x} \lor \neg v_{B+y}$ for $x < y < g$, ordered by $y$ and then by
$x$. Each clause is written densely over the $V$ variables $v_0, \dots, v_{V-1}$; literals on
variables of index at least $V$ are dropped. -/
def cellCNF (g V B : ℕ) : CNF := denseClause V (aloLits g B) :: rowsCNF V B g

/-- **The one-hot cell family.** Fix a layout with label/state block size $A$, $K$ stacks and
$g$ symbol codes, and bounds $T$ and $H$. Let $W = A + KHg$ be the row width and $V = (T+1)W$
the number of variables $v_0, \dots, v_{V-1}$. For every time $t \le T$, stack $k < K$ and depth
$j < H$, the cell with base $B = tW + A + (kH + j)g$ contributes the at-least-one clause
$v_B \lor \dots \lor v_{B+g-1}$, followed by the at-most-one clauses
$\lnot v_{B+x} \lor \lnot v_{B+y}$ for $x < y < g$, ordered by $y$ and then by $x$. Every clause
is written densely, with one slot for each of the $V$ variables. The family is the CNF formula
listing these clauses, with the cells ordered by $t$, then $k$, then $j$. -/
def ohFamily (L : Layout) (T H : ℕ) : CNF :=
  (List.range (T + 1)).flatMap fun t => (List.range L.KK).flatMap fun k =>
    (List.range H).flatMap fun j => cellCNF L.g (L.numVars T H) (L.cIdx H t k j 0)

end Spec

/-! ## [FAM] The generator machine -/

/-- **Counters of the one-hot generator.** The finite type of the nineteen unit counters of the
one-hot clause generator: Tn, Ti, Kc, Kd, Hs, Hi, Gc, HG, Wc, Vc, TW, KB, CB, P, Q, tmp, md,
c1 and c2. -/
inductive CK
  | Tn | Ti | Kc | Kd | Hs | Hi | Gc | HG | Wc | Vc | TW | KB | CB | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Kc, CK.Kd, CK.Hs, CK.Hi, CK.Gc, CK.HG, CK.Wc, CK.Vc, CK.TW, CK.KB,
      CK.CB, CK.P, CK.Q, CK.tmp, CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Clause kinds of a one-hot cell.** For a natural number $g$, a clause kind of a cell with
$g$ symbol codes is either the at-least-one kind, or the at-most-one kind of a pair $(x, y)$ of
symbol codes $x, y < g$ (not necessarily ordered). -/
inductive CL (g : ℕ)
  | alo
  | amo (x y : Fin g)
  deriving DecidableEq, Fintype

namespace CL

variable {g : ℕ}

/-- **Number of literals of a one-hot clause kind.** The number of literals of the at-least-one
clause kind of a cell with $g$ symbol codes is $g$, and that of every at-most-one clause kind
$\mathrm{amo}(x, y)$ is $2$. -/
def nl : CL g → ℕ
  | alo => g
  | amo _ _ => 2

/-- **Offset of a literal in a one-hot clause.** The offset from the cell base of literal $l$ of a
clause kind is $l$ for the at-least-one clause, and for the at-most-one clause
$\mathrm{amo}(x, y)$ it is $x$ when $l = 0$ and $y$ otherwise. -/
def off : CL g → ℕ → ℕ
  | alo, l => l
  | amo x y, l => if l = 0 then x else y

/-- **Literal sign of a clause kind.** For a clause kind $c$ of a cell, $\mathrm{sg}(c)$ is the
sign shared by all literals of $c$: true (positive) for the at-least-one clause and false
(negative) for every at-most-one clause $\mathrm{amo}(x, y)$. -/
def sg : CL g → Bool
  | alo => true
  | amo _ _ => false

/-- **Well-formed clause kinds.** A clause kind of a cell is well formed when it is the
at-least-one clause, or an at-most-one clause $\mathrm{amo}(x, y)$ with $x < y$. -/
def WF : CL g → Prop
  | alo => True
  | amo x y => x.val < y.val

end CL

/-- **Stages of the one-hot precomputation.** The control labels of the generator's
precomputation, sixteen in all: one each for incrementing the time counter $T_n$, writing the
number $g$ of symbol codes on the counter $G_c$, writing the label/state block size $A$ on the
counter $W_c$ and writing the number $K$ of stacks on the counter $K_c$, and one for each of the
four stages of a multiplication routine in each of the three multiplications
$HG := HG + H_s G_c$, $W_c := W_c + K_c \cdot HG$ and $V_c := V_c + T_n W_c$, where $H_s$ is the
height counter and $HG$ and $V_c$ are further counters of the generator. -/
inductive PS
  | inc | eg | hg (s : MS) | ew | ek | w (s : MS) | v (s : MS)
  deriving DecidableEq, Fintype

/-- **Stages of the one-hot literal routine.** The stages of the routine of the one-hot generator
that emits one literal are: two copy stages, the offset stage, the decrement stage, the
comparison stage, for each ordering $o$ (less, equal, greater) two restore stages $r(o)$ and
$r_B(o)$, the gap stage, the failure stage, the slot stage and the drain stage. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- **Control labels of the one-hot generator.** For a natural number $g$, the labels are: a
precomputation label for each precomputation stage; for the time loop, a head, a rest label, a
multiplication label for each multiplication stage, and an end label; for the stack loop, a
head, a rest label, an emission label, two copy labels, a multiplication label for each
multiplication stage, and an end label; for the depth loop, a head, a rest label, two copy
labels, a multiplication label for each multiplication stage, and a drain label; for each
clause kind $c$ of a cell with $g$ symbol codes, a start label, two copy labels, a literal
label for each literal index $l < g$ and each literal stage, and a finishing label; and a
halting label.

The type is finite: each field ranges over a finite type (a stage, a clause kind of a cell with
$g$ symbol codes, or an index below $g$). -/
inductive GL (g : ℕ)
  | pre (s : PS)
  | tHead | tRest | tw (s : MS) | tEnd
  | kHead | kRest | kbE | kbC1 | kbC2 | kbM (s : MS) | kEnd
  | jHead | jRest | jbC1 | jbC2 | jbM (s : MS) | jd
  | e00 (c : CL g) | cv1 (c : CL g) | cv2 (c : CL g) | lit (c : CL g) (l : Fin g) (s : LS)
  | fin (c : CL g)
  | done
  deriving DecidableEq, Fintype

namespace GL

variable {g : ℕ}

/-- **Entry label of a one-hot literal routine.** For a clause kind $c$ of a cell with $g$ symbol
codes and a natural number $l$, the entry label of literal $l$ of $c$ is the first-stage label
of the routine emitting literal $l$ of $c$ if $l < g$, and the halting label otherwise.

The generator never uses it with $l \ge g$. -/
def litL (c : CL g) (l : ℕ) : GL g := if h : l < g then .lit c ⟨l, h⟩ .cp1 else .done

/-- **Label after a literal routine of the one-hot generator.** For a clause kind $c$ of a cell
with $g$ symbol codes and an index $l$, the label the generator moves to once literals
$l, l+1, \dots$ of $c$ have been emitted (literals are emitted from the last one down to the
first): if $l = 0$, the final stage of clause $c$, which emits the leading run of empty slots;
otherwise the routine for literal $l - 1$ of $c$, or the halting label when $l - 1 \ge g$. -/
def after (c : CL g) (l : ℕ) : GL g := if l = 0 then .fin c else litL c (l - 1)

/-- **Entry label of an at-most-one clause.** Fix a number $g$ of symbol codes. For natural
numbers $x$ and $y$ with $x < y < g$, the generator label at which the emission of the
at-most-one clause for the pair $(x, y)$ of the current cell begins; for any other pair it is the
halting label, a case the generator never uses. -/
def pr (x y : ℕ) : GL g :=
  if h : x < y ∧ y < g then .e00 (.amo ⟨x, by omega⟩ ⟨y, h.2⟩) else .done

/-- **Entry label for the first rows of a cell.** Let $g$ be the number of symbol codes of the
one-hot generator. For a natural number $y$, this is the label of the generator at which the
at-least-one clause starts when $y \le 1$; when $2 \le y \le g$, the label starting the
at-most-one clause for the pair $(y - 2, y - 1)$; and when $y \ge 2$ and $y > g$, the final
label $\mathrm{done}$.

From here, for $y \le g$, the generator emits the clauses of the rows below $y$, then the
at-least-one clause. -/
def yDone (y : ℕ) : GL g := if y ≤ 1 then .e00 .alo else pr (y - 2) (y - 1)

/-- **One-hot generator: the label after a clause.** Let $c$ be a clause kind of a cell with $g$
symbol codes: the at-least-one clause, or the at-most-one clause $\mathrm{amo}(x, y)$ for symbol
codes $x, y < g$. The label the generator goes to after clause $c$ is the end of the cell if $c$
is the at-least-one clause. If $c = \mathrm{amo}(x, y)$ with $x > 0$, it is the start of clause
$\mathrm{amo}(x - 1, y)$ when $x - 1 < y < g$, and the halting label otherwise. If
$c = \mathrm{amo}(0, y)$, it is the start of the at-least-one clause when $y \le 1$, and the start
of clause $\mathrm{amo}(y - 2, y - 1)$ when $y \ge 2$. -/
def nextC : CL g → GL g
  | .alo => .jd
  | .amo x y => if x.val = 0 then yDone y.val else pr (x.val - 1) y.val

theorem litL_of_lt {c : CL g} {l : ℕ} (h : l < g) : (litL c l : GL g) = .lit c ⟨l, h⟩ .cp1 :=
  dite_eq_left h

theorem pr_of_lt {x y : ℕ} (h1 : x < y) (h2 : y < g) :
    (pr x y : GL g) = .e00 (.amo ⟨x, by omega⟩ ⟨y, h2⟩) := dite_eq_left ⟨h1, h2⟩

end GL

section Machine

variable (L : Layout)

/-- **One-hot generator: the routine for one literal.** Let $L$ be a layout with $g$ symbol codes,
$c$ a clause kind of a cell of $L$ and $l < g$ a literal index, and write $\mathrm{off}_c(l)$ for
the offset of literal $l$ of $c$ from the cell base. The routine for literal $l$ of $c$ is the
following fragment of the one-hot generator for $L$, which acts on unit counters and a Boolean
output stack. It copies the cell base counter $\mathrm{CB}$ onto counter $Q$ (restoring
$\mathrm{CB}$ through the scratch counter $\mathrm{tmp}$) and pushes $\mathrm{off}_c(l)$ more
units onto $Q$, so that $Q = \mathrm{CB} + \mathrm{off}_c(l)$ when $Q$ and $\mathrm{tmp}$ start
empty. Then it repeats: pop one unit from counter $P$, halting if $P$ is empty; compare $P$ with
$Q$ by popping both in step onto the scratch counters $c_1$ and $c_2$, then move those units back;
if $P \ne Q$, prepend the gap block $01$ to the output and repeat. Once $P = Q$, it prepends the
two-bit slot encoding of the sign of $c$ ($10$ if positive, $11$ if negative) to the output,
empties $Q$, and goes to the routine for literal $l - 1$ of $c$, or to the end of clause $c$ when
$l = 0$. -/
def litP (c : CL L.g) (l : Fin L.g) : LS → TM2.Stmt (SΓ CK) (GL L.g) Bool
  | .cp1 => xfer (.c .CB) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c l .cp1) (.lit c l .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c .CB, ()⟩] (.lit c l .cp2) (.lit c l .eo)
  | .eo => emitR (.c .Q) (List.replicate (c.off l) ()) (.lit c l .dec)
  | .dec => decr (.c .P) (.lit c l .bad) (.lit c l .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c l .cmp)
      (.lit c l (.r .lt)) (.lit c l (.r .eq)) (.lit c l (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c l (.r o)) (.lit c l (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c l (.rB o))
      (if o = .eq then .lit c l .slot else .lit c l .emL)
  | .emL => emitR .out [false, true] (.lit c l .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some c.sg)) (.lit c l .dq)
  | .dq => xfer (.c .Q) [] (.lit c l .dq) (GL.after c l)

/-- **The one-hot generator.** For a layout with label/state block size $A$, $K$ stacks and $g$
symbol codes, the program of a counter machine with an output bit stack and the unary counters
of the generator. Started with $T$ on the time counter $T_n$, $H$ on the height counter $H_s$ and
every other counter empty, it first sets $T_n = T + 1$, $G_c = g$, $HG = Hg$,
$W_c = A + K \cdot Hg$, $K_c = K$ and $V_c = (T + 1)W_c$. It then loops over times $t \le T$,
stacks $k < K$ and depths $j < H$; for each cell it computes the cell's base and pushes onto the
output stack the encodings of the cell's dense at-least-one and at-most-one clauses. When the
loops finish it halts.

On halting, the output stack holds the encoding of the one-hot cell family in front of its
original contents. -/
def prog : GL L.g → TM2.Stmt (SΓ CK) (GL L.g) Bool
  | .pre .inc => incr (.c .Tn) () (.pre .eg)
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Kc) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Kc .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre (.v .head)) s
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) .tHead s
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw .kHead s
  | .kHead => forHead (.c .Kc) (.c .Kd) () .kbE .kRest
  | .kRest => xfer (.c .Kd) [⟨.c .Kc, ()⟩] .kRest .tEnd
  | .tEnd => xfer (.c .TW) [] .tEnd .tHead
  | .kbE => emitR (.c .KB) (List.replicate L.A ()) .kbC1
  | .kbC1 => xfer (.c .TW) [⟨.c .KB, ()⟩, ⟨.c .tmp, ()⟩] .kbC1 .kbC2
  | .kbC2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] .kbC2 (.kbM .head)
  | .kbM s => mulS .Kc .md .HG .KB .tmp .kbM .jHead s
  | .kEnd => xfer (.c .KB) [] .kEnd .kHead
  | .jHead => forHead (.c .Hs) (.c .Hi) () .jbC1 .jRest
  | .jRest => xfer (.c .Hi) [⟨.c .Hs, ()⟩] .jRest .kEnd
  | .jbC1 => xfer (.c .KB) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] .jbC1 .jbC2
  | .jbC2 => xfer (.c .tmp) [⟨.c .KB, ()⟩] .jbC2 (.jbM .head)
  | .jbM s => mulS .Hs .md .Gc .CB .tmp .jbM (GL.yDone L.g) s
  | .jd => xfer (.c .CB) [] .jd .jHead
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (GL.after c c.nl)
  | .lit c l s => litP L c l s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GL.nextC c)
  | .done => .halt

/-- **The one-hot generator as a finite multi-stack machine.** The one-hot generator for a layout,
bundled as a Mathlib multi-stack Turing machine with finitely many stacks, labels and internal
states: its stacks are the output bit stack and one unary counter for each counter of the
generator, its input stack is the time counter and its output stack is the output stack, it
starts at its first precomputation label with internal state false, and it runs the generator's
program.

This bundling only checks the finiteness conditions; the generator also reads the height bound
from the height counter, which a bundled machine with a single input stack does not record. -/
def ohTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := GL L.g
  main := .pre .inc
  σ := Bool
  initialState := false
  m := prog L

end Machine

/-! ## [FAM] Clause kinds: literal positions -/

section Lits

variable {g : ℕ}

/-- **Literals of a one-hot clause kind.** For a cell base $B$ and a clause kind $c$ of a cell
with $g$ symbol codes, the literals of $c$ form a list of pairs (variable, sign): for the
at-least-one kind, the pairs $(B + x, \mathrm{true})$ for $x = 0, \dots, g - 1$ in increasing
order; for the at-most-one kind of the pair $(x, y)$, the two pairs $(B + x, \mathrm{false})$
and $(B + y, \mathrm{false})$. -/
def clits (B : ℕ) (c : CL g) : List (ℕ × Bool) := (List.range c.nl).map fun l => (B + c.off l, c.sg)

theorem clits_alo (B : ℕ) : clits B (.alo : CL g) = aloLits g B := rfl

theorem clits_amo (B : ℕ) (x y : Fin g) : clits B (.amo x y) = amoLits B x y := by
  simp [clits, CL.nl, CL.off, CL.sg, amoLits, List.range_succ]

theorem nl_le {c : CL g} (hc : c.WF) : c.nl ≤ g := by
  cases c with
  | alo => exact le_rfl
  | amo x y => simp only [CL.nl]; have := y.2; simp only [CL.WF] at hc; omega

theorem off_mono {c : CL g} (hc : c.WF) {l : ℕ} (hl : l + 1 < c.nl) : c.off l < c.off (l + 1) := by
  cases c with
  | alo => simp [CL.off]
  | amo x y =>
      simp only [CL.nl] at hl
      obtain rfl : l = 0 := by omega
      simpa [CL.off, CL.WF] using hc

theorem off_lt {c : CL g} {l : ℕ} (hl : l < c.nl) : c.off l < g := by
  cases c with
  | alo => exact hl
  | amo x y => simp only [CL.off]; split_ifs; exact x.2; exact y.2

theorem clits_drop (B : ℕ) (c : CL g) (l : ℕ) :
    (clits B c).drop l = (List.range' l (c.nl - l)).map fun l => (B + c.off l, c.sg) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

/-- **Boundary before a literal of a cell clause.** For $V, B \in \mathbb{N}$, a clause kind $c$
and an index $l$, the number $B + o_l$ if $l$ is less than the number of literals of $c$, where
$o_l$ is the offset of literal $l$ of $c$ from the cell base, and $V$ otherwise. -/
def bnd (V B : ℕ) (c : CL g) (l : ℕ) : ℕ := if l < c.nl then B + c.off l else V

theorem inc_drop {V B : ℕ} {c : CL g} (hc : c.WF) (hBV : B + g ≤ V) (l : ℕ) (hl : l ≤ c.nl) :
    Inc (bnd V B c l) ((clits B c).drop l) V := by
  rw [clits_drop]
  refine inc_of_mono _ c.nl V (fun j hj => ?_) (fun j hj => ?_) (c.nl - l) l _ (by omega)
    (fun hn => ?_) (fun _ => ?_)
  · simpa using off_mono hc hj
  · have := off_lt (c := c) (l := j) (by omega); simp only; omega
  · simp only [bnd]; split_ifs with h
    · omega
    · exact le_rfl
  · simp only [bnd, ite_eq_left (show l < c.nl by omega)]; exact le_rfl

theorem bnd_le {V B : ℕ} {c : CL g} (hc : c.WF) (hBV : B + g ≤ V) {l : ℕ} (hl : l ≤ c.nl) :
    bnd V B c l ≤ V := (inc_drop hc hBV l hl).le

theorem bnd_lt {V B : ℕ} {c : CL g} (hc : c.WF) (hBV : B + g ≤ V) {l : ℕ} (hl : l < c.nl) :
    B + c.off l < bnd V B c (l + 1) := by
  unfold bnd
  split_ifs with h
  · exact Nat.add_lt_add_left (off_mono hc h) B
  · have := off_lt hl; omega

end Lits

/-! ## [FAM] Correctness: one literal, one clause -/

section Clause

variable {L : Layout}

/-- **Empty scratch counters of the one-hot generator.** For an assignment $F$ of a natural number
to each counter of the one-hot generator, $\mathrm{Rest}(F)$ holds when the five scratch counters
$Q$, $\mathit{tmp}$, $\mathit{md}$, $c_1$ and $c_2$ all have value $0$ under $F$.

These are the counters that are empty whenever a clause starts. -/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem Rest.upd {F : CK → ℕ} (h : Rest F) {x : CK} (hQ : x ≠ .Q) (ht : x ≠ .tmp) (hm : x ≠ .md)
    (h1 : x ≠ .c1) (h2 : x ≠ .c2) (n : ℕ) : Rest (update F x n) :=
  ⟨by rw [update_of_ne hQ.symm, h.Q], by rw [update_of_ne ht.symm, h.tmp],
    by rw [update_of_ne hm.symm, h.md], by rw [update_of_ne h1.symm, h.c1],
    by rw [update_of_ne h2.symm, h.c2]⟩

/-- **Run of one literal routine (one-hot generator).** Let $L$ be a layout with $g$ symbol
codes, let $c$ be a clause kind of a cell with $g$ symbol codes, let $l < g$ be a literal index
with offset $\mathrm{off}_c(l)$, and let $F$ be counter values of the one-hot generator whose
scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$. Let
$q, \gamma \in \mathbb{N}$ with $q = F(\mathrm{CB}) + \mathrm{off}_c(l)$ and
$F(P) = q + \gamma + 1$. Then for every output $o$ and flag $v$, the one-hot generator for $L$
runs in at most $\gamma(3q + 6) + 2F(\mathrm{CB}) + 4q + 9$ steps from the first stage of the
routine for literal $l$ of $c$, with flag $v$, counters $F$ and output $o$, to the label after
literal $l$ of $c$ (the routine for literal $l - 1$, or the final stage of $c$ if $l = 0$), with
flag false, counters $F$ except $P = q$, and output $s \cdot (01)^{\gamma} \cdot o$, where $s$ is
the two-bit slot code of the sign of $c$ ($10$ if positive, $11$ if negative). -/
theorem lit_run (c : CL L.g) (l : Fin L.g) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F .CB + c.off l) (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L) (gap * (3 * q + 6) + 2 * F .CB + 4 * q + 9)
      ⟨some (.lit c l .cp1), v, st F o⟩
      ⟨some (GL.after c l), false,
        st (update F .P q) (encodeSlot (some c.sg) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  refine Bud.start ?_
  refine (copyS (M := prog L) (l₁ := .lit c l .cp1) (l₂ := .lit c l .cp2) (next := .lit c l .eo)
    rfl rfl (by decide) (by decide) (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L) (self := .lit c l .eo) (next := .lit c l .dec) rfl _ _ _).bud ?_
  refine (gapS (M := prog L) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2) (ys := [false, true])
    (dec := .lit c l .dec) (cmpL := .lit c l .cmp) (emitL := .lit c l .emL)
    (ifZero := .lit c l .bad) (next := .lit c l .slot) (r := fun o => .lit c l (.r o))
    (rB := fun o => .lit c l (.rB o))
    (out := fun o => if o = .eq then .lit c l .slot else .lit c l .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L) (self := .lit c l .slot) (next := .lit c l .dq) rfl _ _ _).bud ?_
  refine (drainS (M := prog L) (self := .lit c l .dq) (next := GL.after c l) (x := .Q) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- **Per-literal step cost of the one-hot generator.** For a natural number $V$, the cost of
emitting one literal, apart from the gap loop, is $6V + 9$. -/
def litE (V : ℕ) : ℕ := 6 * V + 9

/-- **Step budget for one one-hot clause.** For natural numbers $g$ and $V$, the step budget for
one clause is $V(3V + 6) + g(6V + 9) + 3V + 4$, where $6V + 9$ is the per-literal cost apart
from the gap loop. -/
def clauseB (g V : ℕ) : ℕ := V * (3 * V + 6) + g * litE V + 3 * V + 4

/-- **Run of the literal routines of a clause (one-hot generator).** Let $L$ be a layout with $g$
symbol codes, let $c$ be a well-formed clause kind of a cell with $g$ symbol codes (the
at-least-one clause, or the at-most-one clause $\mathrm{amo}(x, y)$ with $x < y$) with $n$
literals, write $\mathrm{off}_c(l)$ for the offset of literal $l$ of $c$ from the cell base, and
let $B, V \in \mathbb{N}$ with $B + g \le V$. For $l \le n$ let $b_l$ be
$B + \mathrm{off}_c(l)$ if $l < n$ and $V$ otherwise, let $\lambda_l$ be the list of literals of
$c$ at base $B$ (position and sign) from index $l$ on, and let the label after literal $l$ be the
routine for literal $l - 1$ of $c$, or the final stage of $c$ if $l = 0$. Write $E(a, \lambda)$
for the gap encoding of $\lambda$ from slot $a$ to $V$. Let $F$ be counter values of the one-hot
generator whose scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$ and
with $F(\mathrm{CB}) = B$, and let $o$ be an output. Then for every $l \le n$ and flag $v$ there
is a flag $v'$ such that the one-hot generator for $L$ runs in at most $b_l(3V + 6) + l(6V + 9)$
steps from the label after literal $l$ of $c$, with flag $v$, counters $F$ except $P = b_l$ and
output $E(b_l, \lambda_l) \cdot 00 \cdot o$, to the final stage of $c$, with flag $v'$, counters
$F$ except $P = b_0$ and output $E(b_0, \lambda_0) \cdot 00 \cdot o$. -/
theorem lits_run {V B : ℕ} {c : CL L.g} (hc : c.WF) (hBV : B + L.g ≤ V) (F : CK → ℕ)
    (hF : Rest F) (hCB : F .CB = B) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L) (bnd V B c l * (3 * V + 6) + l * litE V)
        ⟨some (GL.after c l), v,
          st (update F .P (bnd V B c l)) (gapEnc (bnd V B c l) ((clits B c).drop l) V ++
            [false, false] ++ o)⟩
        ⟨some (.fin c), v',
          st (update F .P (bnd V B c 0)) (gapEnc (bnd V B c 0) (clits B c) V ++
            [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GL.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hlg : l < L.g := lt_of_lt_of_le hlm (nl_le hc)
      set p := B + c.off l with hp
      set b := bnd V B c (l + 1) with hb
      have hpb : p < b := bnd_lt hc hBV hlm
      have r := lit_run c ⟨l, hlg⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by simp [hp, hCB]) (by simp; omega)
        (gapEnc b ((clits B c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GL.after, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel, GL.litL_of_lt hlg]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd V B c l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits B c).drop l = (p, c.sg) :: (clits B c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hc hBV (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hc hBV hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hCB]
      rw [Nat.add_one_mul l]
      unfold litE
      omega

/-- **One clause of the one-hot generator.** Let $L$ be a layout with $g$ symbol codes, let $c$
be a well-formed clause kind of a cell (the pair of an at-most-one kind is increasing), and let
$B$ and $V$ be natural numbers with $B + g \le V$. Let $F$ be counter values whose scratch
counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are zero, whose cell-base counter
$\mathrm{CB}$ holds $B$, whose variable counter $\mathrm{Vc}$ holds $V$, and whose position
counter $P$ is zero. Then for every output word $o$ and every machine state $v$, the generator
of $L$ runs in at most $V(3V + 6) + g(6V + 9) + 3V + 4$ steps from the label that starts
clause $c$, with state $v$, counters $F$ and output $o$, to the label that follows clause $c$,
with state false, the same counters $F$, and output the encoding of the dense clause over $V$
variables whose literals are those of $c$ in the cell with base $B$, followed by $o$. -/
theorem clause_run {V B : ℕ} {c : CL L.g} (hc : c.WF) (hBV : B + L.g ≤ V) (F : CK → ℕ)
    (hF : Rest F) (hCB : F .CB = B) (hV : F .Vc = V) (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L) (clauseB L.g V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GL.nextC c), false, st F (encodeClause (denseClause V (clits B c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := GL.after c c.nl) rfl rfl
    (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run hc hBV F hF hCB o c.nl le_rfl false
  have hbm : bnd V B c c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L) (self := .fin c) (next := GL.nextC c) (x := .P) rfl _ _ _).bud ?_
  have e1 : update (update F .P (bnd V B c 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hc hBV 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits B c)) =
      rep [false, true] (bnd V B c 0) ++ gapEnc (bnd V B c 0) (clits B c) V ++ [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hc hBV (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) (nl_le hc)
  unfold clauseB
  omega

end Clause

/-! ## [FAM] Correctness: the clauses of one cell (a 2-D label chain) -/

section Cell

variable {L : Layout}

theorem alo_run {V B : ℕ} (hBV : B + L.g ≤ V) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = B)
    (hV : F .Vc = V) (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L) (clauseB L.g V) ⟨some (.e00 .alo), v, st F o⟩
      ⟨some .jd, false, st F (encodeClause (denseClause V (aloLits L.g B)) ++ o)⟩ :=
  clause_run (c := .alo) True.intro hBV F hF hCB hV hP o v

/-- **Generator run over one row of at-most-one clauses.** Let $L$ be a layout with $g$ symbol
codes, let $V$ and $B$ be natural numbers with $B + g \le V$, write $p_i$ for the variable with
index $i$, and let $F$ assign a value to each counter of the one-hot generator such that the
scratch counters are empty ($\mathrm{Rest}(F)$), $F(CB) = B$, $F(Vc) = V$ and $F(P) = 0$. Let
$y < g$, let $\beta = V(3V + 6) + g(6V + 9) + 3V + 4$ be the step budget of one clause, and for
$x' < y$ let $e_{x'}$ be the encoding of the dense clause over $V$ variables whose only literals
are $\lnot p_{B + x'}$ and $\lnot p_{B + y}$. Then for every $x < y$, every output list $o$ and
every flag $v$, the one-hot generator of $L$, started at the label of the at-most-one clause for
the pair $(x, y)$ with flag $v$, output stack $o$ and each counter $c$ holding $F(c)$, reaches
within $(x + 1) \beta$ steps the label $\mathrm{yDone}(y)$ (Y Done) with flag false, the same
counters, and output stack $e_0 e_1 \cdots e_x \, o$ (concatenation). -/
theorem row_run {V B : ℕ} (hBV : B + L.g ≤ V) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = B)
    (hV : F .Vc = V) (hP : F .P = 0) {y : ℕ} (hy : y < L.g) :
    ∀ x, x < y → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L) ((x + 1) * clauseB L.g V) ⟨some (GL.pr x y), v, st F o⟩
        ⟨some (GL.yDone y), false, st F ((List.range (x + 1)).flatMap
          (fun x' => encodeClause (denseClause V (amoLits B x' y))) ++ o)⟩ := by
  intro x
  induction x with
  | zero =>
      intro hx o v
      have r := clause_run (c := .amo ⟨0, by omega⟩ ⟨y, hy⟩) hx hBV F hF hCB hV hP o v
      rw [GL.pr_of_lt hx hy]
      simpa [GL.nextC, clits_amo] using r
  | succ x ih =>
      intro hx o v
      have r := clause_run (c := .amo ⟨x + 1, by omega⟩ ⟨y, hy⟩) hx hBV F hF hCB hV hP o v
      simp only [GL.nextC, clits_amo, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at r
      rw [GL.pr_of_lt hx hy]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V (amoLits B (x + 1) y)) ++ o) false
      rw [List.range_succ (n := x + 1), List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (x + 1)]; omega

theorem encodeCNF_rows_succ (g V B y : ℕ) :
    encodeCNF (denseClause V (aloLits g B) :: rowsCNF V B (y + 1)) =
      encodeCNF (denseClause V (aloLits g B) :: rowsCNF V B y) ++
        (List.range y).flatMap (fun x => encodeClause (denseClause V (amoLits B x y))) := by
  simp [encodeCNF, rowsCNF, List.range_succ, List.flatMap_append, List.append_assoc,
    List.flatMap_map]

/-- **Generator run over the first rows and the at-least-one clause.** Let $L$ be a layout with
$g$ symbol codes, let $V$ and $B$ be natural numbers with $B + g \le V$, write $p_i$ for the
variable with index $i$, and let $F$ assign a value to each counter of the one-hot generator such
that the scratch counters are empty ($\mathrm{Rest}(F)$), $F(CB) = B$, $F(Vc) = V$ and
$F(P) = 0$. Let $\beta = V(3V + 6) + g(6V + 9) + 3V + 4$ be the step budget of one clause, and
for $y \le g$ let $e_y$ be the encoding of the CNF formula whose first clause is the dense clause
over $V$ variables with the positive literals $p_B, \dots, p_{B + g - 1}$, followed by the
at-most-one clauses of the rows $y' < y$ with base $B$ over $V$ variables (Rows CNF). Then for
every $y \le g$, every output list $o$ and every flag $v$, the one-hot generator of $L$, started
at the label $\mathrm{yDone}(y)$ (Y Done) with flag $v$, output stack $o$ and each counter $c$
holding $F(c)$, reaches within $(1 + y^2) \beta$ steps the label $\mathrm{jd}$ (which drains
$CB$) with flag false, the same counters, and output stack $e_y \, o$ (concatenation). -/
theorem rows_run {V B : ℕ} (hBV : B + L.g ≤ V) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = B)
    (hV : F .Vc = V) (hP : F .P = 0) :
    ∀ y, y ≤ L.g → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L) ((1 + y * y) * clauseB L.g V) ⟨some (GL.yDone y), v, st F o⟩
        ⟨some .jd, false,
          st F (encodeCNF (denseClause V (aloLits L.g B) :: rowsCNF V B y) ++ o)⟩ := by
  intro y
  induction y with
  | zero =>
      intro _ o v
      have r := alo_run hBV F hF hCB hV hP o v
      simp only [GL.yDone, zero_le, ite_true]
      have e : encodeCNF (denseClause V (aloLits L.g B) :: rowsCNF V B 0) ++ o =
          encodeClause (denseClause V (aloLits L.g B)) ++ o := by simp [encodeCNF, rowsCNF]
      rw [e]; exact r.mono (by simp)
  | succ y ih =>
      intro hy o v
      by_cases hy0 : y = 0
      · subst hy0
        have r := alo_run hBV F hF hCB hV hP o v
        simp only [GL.yDone, le_refl, ite_true]
        have e : encodeCNF (denseClause V (aloLits L.g B) :: rowsCNF V B (0 + 1)) ++ o =
            encodeClause (denseClause V (aloLits L.g B)) ++ o := by simp [encodeCNF, rowsCNF]
        rw [e]; exact r.mono (by simp; omega)
      · rw [GL.yDone, ite_eq_right (by omega), show y + 1 - 2 = y - 1 by omega, Nat.add_sub_cancel]
        have r := row_run hBV F hF hCB hV hP (y := y) (by omega) (y - 1) (by omega) o v
        rw [show y - 1 + 1 = y by omega] at r
        refine Bud.start (r.bud ?_)
        have := ih (by omega) ((List.range y).flatMap
          (fun x => encodeClause (denseClause V (amoLits B x y))) ++ o) false
        rw [encodeCNF_rows_succ, List.append_assoc]
        refine this.bud (Bud.fin ?_ rfl)
        nlinarith [Nat.zero_le (clauseB L.g V), Nat.zero_le (y * clauseB L.g V)]

/-- **Step bound for one cell.** For $g, H, V \in \mathbb{N}$, the number
$2V + 2 + (H(2g + 3) + H + 2) + (1 + g^2)\, b + V + 1$, where $b$ is the step bound for one
clause for $g$ and $V$. It bounds the steps of one iteration of the one-hot generator's loop over
cell depths. -/
def cellB (g H V : ℕ) : ℕ :=
  2 * V + 2 + (H * (2 * g + 3) + H + 2) + (1 + g * g) * clauseB g V + V + 1

/-- **Generator run for one cell.** Let $L$ be a layout with $g$ symbol codes and let $j < H$, $V$
and $B$ be natural numbers. Let $F$ be counter values of the one-hot generator with the scratch
counters $Q$, tmp, md, $c_1$, $c_2$ empty, the counters $CB$ and $P$ zero, $Vc = V$, $Gc = g$,
$Hs = j$, $j g + KB = B$, and suppose $B + g \le V$. Then for every output $o$ and flag $v$, the
generator goes, in at most the one-cell step bound for $g$, $H$, $V$ steps, from the start of the
body of the depth loop with flag $v$, counters $F$ and output $o$ to the head of the depth loop
with flag false, counters $F$ and output the encoding of the one-hot clauses of the cell with
base $B$ over $V$ variables followed by $o$. -/
theorem cell_run {V H j B : ℕ} (hj : j < H) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hHs : F .Hs = j)
    (hB : j * L.g + F .KB = B) (hBV : B + L.g ≤ V) (o : List Bool) (v : Bool) :
    RunLe (prog L) (cellB L.g H V) ⟨some .jbC1, v, st F o⟩
      ⟨some .jHead, false, st F (encodeCNF (cellCNF L.g V B) ++ o)⟩ := by
  refine Bud.start ?_
  refine (copyS (M := prog L) (l₁ := .jbC1) (l₂ := .jbC2) (next := .jbM .head) rfl rfl
    (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L) (mk := .jbM) (next := GL.yDone L.g) (a := .Hs) (ad := .md)
    (b := .Gc) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := update F .CB B) (by funext x; cases x <;> simp [hHs, hG, hCB, ← hB]) ?_
  have hF' : Rest (update F .CB B) :=
    hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) B
  refine (rows_run hBV _ hF' (by simp) (by simp [hV]) (by simp [hP]) L.g le_rfl o _).bud ?_
  refine (drainS (M := prog L) (self := .jd) (next := .jHead) (x := .CB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) hj.le
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hHs, hG, hCB]
    unfold cellB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB]

end Cell

/-! ## [FAM] Correctness: the three nested runtime loops and the whole generator -/

section Top

variable {L : Layout}

theorem kb_le {T H t k : ℕ} (ht : t ≤ T) (hk : k < L.KK) :
    k * (H * L.g) + (t * L.rowW H + L.A) ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h2 : k * (H * L.g) + H * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have h3 : (t + 1) * (L.A + L.KK * (H * L.g)) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h3
  omega

theorem base_le {T H t k j : ℕ} (ht : t ≤ T) (hk : k < L.KK) (hj : j < H) :
    j * L.g + (k * (H * L.g) + (t * L.rowW H + L.A)) + L.g ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h1 : j * L.g + L.g ≤ H * L.g := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have h2 : k * (H * L.g) + H * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have h3 : (t + 1) * (L.A + L.KK * (H * L.g)) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h3
  omega

theorem base_eq (H t k j : ℕ) :
    j * L.g + (k * (H * L.g) + (t * L.rowW H + L.A)) = L.cIdx H t k j 0 := by
  unfold Layout.cIdx; ring

/-- **Encoded one-hot clauses of one stack at one time step.** For a layout $L$ with $g$ symbol
codes, natural numbers $T, H$, a time step $t$ and a stack $k$, the concatenation over
$j = 0, \dots, H - 1$ of the bit encodings of the one-hot clauses of the cell whose base is the
cell variable of $L$ for stack $k$, depth $j$, symbol code $0$ at time $t$, written densely over
the $V$ variables of $L$ for $T$ and $H$. -/
def blkK (L : Layout) (T H t k : ℕ) : List Bool :=
  (List.range H).flatMap fun j => encodeCNF (cellCNF L.g (L.numVars T H) (L.cIdx H t k j 0))

/-- **Encoded one-hot clauses of one time step.** For a layout $L$ with $K$ stacks, natural
numbers $T, H$ and a time step $t$, the concatenation over the stacks $k = 0, \dots, K - 1$ of the
encoded one-hot clauses of stack $k$ at time step $t$ (for $T$ and $H$). -/
def blkT (L : Layout) (T H t : ℕ) : List Bool := (List.range L.KK).flatMap (blkK L T H t)

/-- **Step budget for one stack iteration of the one-hot generator.** For natural numbers $g$,
$K$, $H$ and $V$, let $c = V(3V + 6) + g(6V + 9) + 3V + 4$ be the step budget for one clause
and $C = 2V + 2 + (H(2g + 3) + H + 2) + (1 + g^2)c + V + 1$ the step budget for one cell. The
budget is $1 + (2V + 2) + (K(2Hg + 3) + K + 2) + (H(C + 1) + H + 2) + V + 1$. -/
def kBodyB (g KK H V : ℕ) : ℕ :=
  1 + (2 * V + 2) + (KK * (2 * (H * g) + 3) + KK + 2) + (H * (cellB g H V + 1) + H + 2) + V + 1

/-- **One stack iteration of the one-hot generator.** Let $L$ be a layout with $g$ symbol codes,
$K$ stacks and a label/state block of size $A$, let $T$, $H$, $t$, $k$ be natural numbers with
$t \le T$ and $k < K$, let $W = A + KHg$ be the row width of $L$ at height $H$, and let
$V = (T + 1)W$ be the number of variables. For $j < H$ let $B_j = tW + A + (kH + j)g$ be the
base of the cell at time $t$, stack $k$ and depth $j$, and let $w_j$ be the encoding of the
dense clause over $V$ variables with literals $(B_j + x, \mathrm{true})$ for
$x = 0, \dots, g - 1$ in increasing order, followed by the encodings of the dense clauses over
$V$ variables with literals $(B_j + x, \mathrm{false})$ and $(B_j + y, \mathrm{false})$ for all
pairs $x < y < g$, ordered by $y$ and then by $x$. Let $F$ be counter values whose scratch
counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are zero, with
$\mathrm{CB} = P = \mathrm{KB} = \mathrm{Hi} = 0$, $\mathrm{Vc} = V$, $\mathrm{Gc} = g$,
$\mathrm{HG} = Hg$, $\mathrm{Hs} = H$, $\mathrm{TW} = tW$ and $\mathrm{Kc} = k$. Then for every
output word $o$ and every machine state $v$, the generator of $L$ runs within the
one-stack-iteration step budget at $(g, K, H, V)$ from the label that starts the body of the
stack loop, with state $v$, counters $F$ and output $o$, to the head of the stack loop, with
state false, the same counters $F$, and output $w_0 w_1 \cdots w_{H-1}$ followed by $o$. -/
theorem kbody_run {T H t k : ℕ} (ht : t ≤ T) (hk : k < L.KK) (F : CK → ℕ) (hF : Rest F)
    (hCB : F .CB = 0) (hP : F .P = 0) (hKB : F .KB = 0) (hV : F .Vc = L.numVars T H)
    (hG : F .Gc = L.g) (hHG : F .HG = H * L.g) (hHs : F .Hs = H) (hHi : F .Hi = 0)
    (hTW : F .TW = t * L.rowW H) (hKc : F .Kc = k) (o : List Bool) (v : Bool) :
    RunLe (prog L) (kBodyB L.g L.KK H (L.numVars T H)) ⟨some .kbE, v, st F o⟩
      ⟨some .kHead, false, st F (blkK L T H t k ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L) (self := .kbE) (next := .kbC1) (x := .KB) rfl _ _ _).bud ?_
  refine (copyS (M := prog L) (l₁ := .kbC1) (l₂ := .kbC2) (next := .kbM .head) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) v o).bud ?_
  refine (mulS_run (M := prog L) (mk := .kbM) (next := .jHead) (a := .Kc) (ad := .md)
    (b := .HG) (c := .KB) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  set KBv := k * (H * L.g) + (t * L.rowW H + L.A) with hKBv
  refine bud_st (F' := update F .KB KBv) (by
    funext x; cases x <;> simp [hKc, hHG, hTW, hKB, hKBv]) ?_
  have hloop := stLoop (M := prog L) (c := .Hs) (cd := .Hi) (head := .jHead) (body := .jbC1)
    (rest := .jRest) (next := .kEnd) rfl rfl (by decide) H (cellB L.g H (L.numVars T H))
    (fun j => encodeCNF (cellCNF L.g (L.numVars T H) (L.cIdx H t k j 0)))
    (update F .KB KBv) (by simp [hHs]) (by simp [hHi])
    (fun j hj o' => ⟨false, cell_run hj _
      ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
      (by simp [hCB]) (by simp [hP]) (by simp [hV]) (by simp [hG]) (by simp)
      (by simp [hKBv, base_eq]) (by rw [← base_eq]; exact base_le ht hk hj) o' true⟩)
    false o
  refine hloop.bud ?_
  refine (drainS (M := prog L) (self := .kEnd) (next := .kHead) (x := .KB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := kb_le (H := H) ht hk
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.mul_le_mul_right (2 * (H * L.g) + 3) hk.le
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKc, hHG, hTW,
      hKB]
    unfold kBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hKB]

/-- **Step budget for one time step of the one-hot generator.** Let $L$ be a layout with $A$
label/state variables per row, $K$ stacks and $g$ symbol codes, let $T$ and $H$ be natural
numbers, $W = A + K H g$ the row width and $V = (T + 1) W$ the number of variables, and let
$\kappa$ be the step budget of one iteration of the $k$ loop for $g$, $K$, $H$ and $V$. The
budget is $T(2W + 3) + T + 2 + \bigl(K(\kappa + 1) + K + 2\bigr) + V + 1$. -/
def tBodyB (L : Layout) (T H : ℕ) : ℕ :=
  T * (2 * L.rowW H + 3) + T + 2 + (L.KK * (kBodyB L.g L.KK H (L.numVars T H) + 1) + L.KK + 2) +
    L.numVars T H + 1

/-- **Generator run over one time step.** Let $L$ be a layout with $A$ label/state variables per
row, $K$ stacks and $g$ symbol codes, let $t \le T$ and $H$ be natural numbers, and write
$W = A + K H g$ for the row width, $V = (T + 1) W$ for the number of variables and $p_i$ for the
variable with index $i$. Let $F$ assign a value to each counter of the one-hot generator such
that the scratch counters are empty ($\mathrm{Rest}(F)$),
$F(CB) = F(P) = F(KB) = F(TW) = F(Hi) = F(Kd) = 0$, $F(Vc) = V$, $F(Gc) = g$, $F(HG) = H g$,
$F(Hs) = H$, $F(Wc) = W$, $F(Kc) = K$ and $F(Tn) = t$. For $k < K$ and $j < H$ let
$b_{k,j} = t W + A + (k H + j) g$ be the base of cell $(k, j)$, and let $E_{k,j}$ be the encoding
of the CNF formula consisting of the dense clause over $V$ variables with the positive literals
$p_{b_{k,j}}, \dots, p_{b_{k,j} + g - 1}$, followed, for $y = 0, \dots, g - 1$ in turn and within
each for $x = 0, \dots, y - 1$ in turn, by the dense clause over $V$ variables whose only literals
are $\lnot p_{b_{k,j} + x}$ and $\lnot p_{b_{k,j} + y}$. Let $E$ be the concatenation of the
$E_{k,j}$ for $k = 0, \dots, K - 1$ and within each for $j = 0, \dots, H - 1$. Then for every
output list $o$ and every flag $v$, the one-hot generator of $L$, started at the first label of
the stage computing $TW := t W$ with flag $v$, output stack $o$ and each counter $c$ holding
$F(c)$, reaches within the time-step budget of $L$, $T$ and $H$ (T Body B) steps the head of the
time loop with flag false, the same counters, and output stack $E \, o$ (concatenation). -/
theorem tbody_run {T H t : ℕ} (ht : t ≤ T) (F : CK → ℕ) (hF : Rest F)
    (hCB : F .CB = 0) (hP : F .P = 0) (hKB : F .KB = 0) (hTW : F .TW = 0)
    (hV : F .Vc = L.numVars T H) (hG : F .Gc = L.g) (hHG : F .HG = H * L.g) (hHs : F .Hs = H)
    (hHi : F .Hi = 0) (hWc : F .Wc = L.rowW H) (hKc : F .Kc = L.KK) (hKd : F .Kd = 0)
    (hTn : F .Tn = t) (o : List Bool) (v : Bool) :
    RunLe (prog L) (tBodyB L T H) ⟨some (.tw .head), v, st F o⟩
      ⟨some .tHead, false, st F (blkT L T H t ++ o)⟩ := by
  refine Bud.start ?_
  refine (mulS_run (M := prog L) (mk := .tw) (next := .kHead) (a := .Tn) (ad := .md)
    (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := update F .TW (t * L.rowW H)) (by
    funext x; cases x <;> simp [hTn, hWc, hTW]) ?_
  have hloop := stLoop (M := prog L) (c := .Kc) (cd := .Kd) (head := .kHead) (body := .kbE)
    (rest := .kRest) (next := .tEnd) rfl rfl (by decide) L.KK (kBodyB L.g L.KK H (L.numVars T H))
    (blkK L T H t) (update F .TW (t * L.rowW H)) (by simp [hKc]) (by simp [hKd])
    (fun k hk o' => ⟨false, kbody_run ht hk _
      ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
      (by simp [hCB]) (by simp [hP]) (by simp [hKB]) (by simp [hV]) (by simp [hG])
      (by simp [hHG]) (by simp [hHs]) (by simp [hHi]) (by simp) (by simp) o' true⟩)
    false o
  refine hloop.bud ?_
  refine (drainS (M := prog L) (self := .tEnd) (next := .tHead) (x := .TW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    simp only [update_self, hTn, hWc]
    unfold tBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hTW]

/-- **Initial counters of the one-hot generator.** For natural numbers $T$ and $H$, the initial
counter values are $T$ on the counter $\mathrm{Tn}$, $H$ on the counter $\mathrm{Hs}$, and $0$
on every other counter. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

/-- **Counter values after the one-hot precomputation.** For a layout with label/state block size
$A$, $K$ stacks and $g$ symbol codes, and bounds $T$ and $H$, let $W = A + KHg$. After the
precomputation the generator's counters hold $T_n = T + 1$, $H_s = H$, $G_c = g$, $HG = Hg$,
$W_c = W$, $K_c = K$ and $V_c = (T + 1)W$, and every other counter holds $0$. -/
def preF (L : Layout) (T H : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Kc => L.KK
  | .Vc => L.numVars T H
  | _ => 0

/-- **Step budget of the one-hot precomputation.** For a layout with label/state block size $A$,
$K$ stacks and $g$ symbol codes, bounds $T$ and $H$, and row width $W = A + KHg$, the number of
steps allotted to the generator's precomputation is
$4 + (H(2g + 3) + H + 2) + (K(2Hg + 3) + K + 2) + ((T + 1)(2W + 3) + (T + 1) + 2)$. -/
def preB (L : Layout) (T H : ℕ) : ℕ :=
  4 + (H * (2 * L.g + 3) + H + 2) + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) +
    ((T + 1) * (2 * L.rowW H + 3) + (T + 1) + 2)

/-- **Explicit time bound of the one-hot generator.** For a layout $L$ and natural numbers $T$ and
$H$, the explicit time bound of the one-hot generator is $p + (T + 1)(b + 1) + (T + 1) + 2$,
where $p$ is the cost of its precomputation and $b$ the cost of one iteration of its time loop,
both for $L$, $T$ and $H$.

This bound is at most $668\,(A + K + g + 1)^7 (T + H + 1)^6$, where $A$ is the label block size,
$K$ the number of stacks and $g$ the number of symbol codes of $L$. -/
def ohBound (L : Layout) (T H : ℕ) : ℕ := preB L T H + ((T + 1) * (tBodyB L T H + 1) + (T + 1) + 2)

theorem encodeCNF_ohFamily (T H : ℕ) :
    encodeCNF (ohFamily L T H) = (List.range (T + 1)).flatMap (blkT L T H) := by
  simp [encodeCNF, ohFamily, List.flatMap_assoc]; rfl

/-- **Correctness of the one-hot generator, with its explicit time bound.** Fix a layout, natural
numbers $T$ and $H$, and a bit string $o$. Start the one-hot generator at its first
precomputation label, with internal state false, the output stack holding $o$, the time counter
holding $T$ and the height counter holding $H$ in unary, and every other counter empty. Then
within $\beta(T, H)$ steps, where $\beta$ is the generator's explicit step bound, it reaches its
halting label, in some internal state, with the output stack holding the encoding of the one-hot
cell family for $T$ and $H$ followed by $o$. -/
theorem oh_run (T H : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L) (ohBound L T H)
        ⟨some (.pre .inc), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (ohFamily L T H) ++ o := by
  refine ⟨false, st (preF L T H) (encodeCNF (ohFamily L T H) ++ o), ?_, rfl⟩
  refine Bud.start ?_
  refine (incS (M := prog L) (self := .pre .inc) (next := .pre .eg) (x := .Tn) rfl _ _ _).bud ?_
  refine (emitS (M := prog L) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc) rfl _ _
    _).bud ?_
  refine (mulS_run (M := prog L) (mk := fun s => .pre (.hg s)) (next := .pre .ew) (a := .Hs)
    (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [initF])
    (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _ _).bud ?_
  refine (emitS (M := prog L) (self := .pre .ek) (next := .pre (.w .head)) (x := .Kc) rfl _ _
    _).bud ?_
  refine (mulS_run (M := prog L) (mk := fun s => .pre (.w s)) (next := .pre (.v .head))
    (a := .Kc) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (mulS_run (M := prog L) (mk := fun s => .pre (.v s)) (next := .tHead)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars] <;> ring) ?_
  have hloop := stLoop (M := prog L) (c := .Tn) (cd := .Ti) (head := .tHead) (body := .tw .head)
    (rest := .tRest) (next := .done) rfl rfl (by decide) (T + 1) (tBodyB L T H)
    (blkT L T H) (preF L T H) rfl rfl
    (fun t ht o' => ⟨false, tbody_run (by omega) _
      ⟨by simp [preF], by simp [preF], by simp [preF], by simp [preF], by simp [preF]⟩
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp) o' true⟩)
    false o
  rw [← encodeCNF_ohFamily] at hloop
  refine hloop.bud (Bud.fin ?_ rfl)
  simp [initF, preB, ohBound, Layout.rowW]
  ring_nf
  omega

end Top

/-! ## [BOUND] The time bound is polynomial: `ohBound ≤ ohC · (T + H + 1)^6` -/

section Poly

theorem ohBound_mono {L L' : Layout} {T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hT : T ≤ T') (hH : H ≤ H') : ohBound L T H ≤ ohBound L' T' H' := by
  unfold ohBound preB tBodyB kBodyB cellB clauseB litE Layout.numVars Layout.rowW
  gcongr

/-- **Time bound of the one-hot generator on a uniform layout.** For all natural numbers $k \ge 1$
and $y \ge 1$, the explicit time bound of the one-hot generator for the layout whose label block
size, number of stacks, number of symbol codes and window depth all equal $k$, with $T = H = y$,
is at most $668\, k^7 y^6$.

Every monomial of the bound is at most $k^7 y^6$, and the coefficients sum to $668$, the value
of the bound at $k = y = 1$. -/
theorem ohBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    ohBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) y y ≤ 668 * k ^ 7 * y ^ 6 := by
  have m : ∀ a b, a ≤ 7 → b ≤ 6 → k ^ a * y ^ b ≤ k ^ 7 * y ^ 6 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold ohBound preB tBodyB kBodyB cellB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 4 5 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num),
    m 5 5 (by norm_num) (by norm_num),
    m 5 6 (by norm_num) (by norm_num),
    m 6 2 (by norm_num) (by norm_num),
    m 6 3 (by norm_num) (by norm_num),
    m 6 4 (by norm_num) (by norm_num),
    m 6 5 (by norm_num) (by norm_num),
    m 7 3 (by norm_num) (by norm_num),
    m 7 4 (by norm_num) (by norm_num),
    m 7 5 (by norm_num) (by norm_num),
    m 7 6 (by norm_num) (by norm_num)]

/-- **Constant of the one-hot time bound.** For a layout $L$ with label block size $A$, $K$ stacks
and $g$ symbol codes, the constant of the one-hot generator's time bound is
$668\,(A + K + g + 1)^7$; it does not depend on the window depth of $L$. -/
def ohC (L : Layout) : ℕ := 668 * (L.A + L.KK + L.g + 1) ^ 7

theorem ohBound_le (L : Layout) (T H : ℕ) : ohBound L T H ≤ ohC L * (T + H + 1) ^ 6 := by
  have := ohBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + 1))
    (T := T) (T' := T + H + 1) (H := H) (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega)
  have h2 := ohBound_uni (L.A + L.KK + L.g + 1) (T + H + 1) (by omega) (by omega)
  unfold ohC
  exact this.trans h2

open Polynomial in
/-- **The one-hot time bound as a polynomial.** For a layout with label/state block size $A$, $K$
stacks and $g$ symbol codes, let $c = 668\,(A + K + g + 1)^7$; this is the polynomial
$c\,(X + 1)^6$ with natural-number coefficients. For natural numbers $T$ and $H$, its value at
$X = T + H$ is $c\,(T + H + 1)^6$, the bound on the number of steps of the one-hot generator
started on $T$ and $H$. -/
noncomputable def ohPoly (L : Layout) : Polynomial ℕ := C (ohC L) * (X + 1) ^ 6

theorem ohPoly_eval (L : Layout) (T H : ℕ) : (ohPoly L).eval (T + H) = ohC L * (T + H + 1) ^ 6 := by
  simp [ohPoly]

/-- **Polynomial time bound for the one-hot generator.** Fix a layout with label/state block size
$A$, $K$ stacks and $g$ symbol codes, natural numbers $T$ and $H$, and a bit string $o$, and let
$c = 668\,(A + K + g + 1)^7$. Start the one-hot generator at its first precomputation label, with
internal state false, the output stack holding $o$, the time counter holding $T$ and the height
counter holding $H$ in unary, and every other counter empty. Then within $c\,(T + H + 1)^6$
steps it reaches its halting label, in some internal state, with the output stack holding the
encoding of the one-hot cell family for $T$ and $H$ followed by $o$. -/
theorem oh_time {L : Layout} (T H : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L) (ohC L * (T + H + 1) ^ 6)
        ⟨some (.pre .inc), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (ohFamily L T H) ++ o :=
  let ⟨v, S, h, h'⟩ := oh_run T H o; ⟨v, S, h.mono (ohBound_le L T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.OneHot
