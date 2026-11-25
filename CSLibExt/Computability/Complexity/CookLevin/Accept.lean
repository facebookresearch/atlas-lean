/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `D3Acc.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/D3Acc.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib); module docstring rewritten for this repository (the source's notes and status
lines dropped), missing docstrings added, long lines wrapped.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Situation

/-!
# Cook-Levin: generator machine for the accept family

For every label/state code `u < n1`, the dense unit clause `X[T, u]` with polarity `u = ac`, then
for every symbol code `x < g` the dense unit clause `C[T, k1, 0, x]` with polarity `x = ea`: at
time `T` the machine is halted and the output stack's top cell holds the accept symbol.
`Situation.Enc.accFamily` is the instance for a concrete encoding. Every clause is dense over
`V = (T+1)·W`.

The machine computes `H·g`, `W`, `T·W`, `V = (T+1)·W` and the cell base on runtime counters; the
`u` and `x` loops are label chains. `acc_gen_time` gives its run and step bound.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Accept

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc encodeClause_denseClause denseClause)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out emitS emitOut incS drainS
  xferES copyS mulS mulS_run gapS bud_st)

/-! ## [FAM] The family (pure specification) -/

section Spec

variable (L : Layout) (n1 ac k1 ea : ℕ)

/-- **Literals of an accept code clause.** For a layout $L$, a code $a_c$, a time $T$, a height $H$
and $u \in \mathbb{N}$, the literal list of code clause $u$ is the single literal whose variable
is the label/state variable $X[T, u]$ (entry $u$ of the label/state block at time $T$, for
height $H$) and which is positive exactly when $u = a_c$. -/
def codeLits (T H u : ℕ) : List (ℕ × Bool) := [(L.xIdx H T u, decide (u = ac))]

/-- **Literals of an accept cell clause.** For a layout $L$, a stack $k_1$, a symbol code $e_a$,
a time $T$, a height $H$ and $x \in \mathbb{N}$, the literal list of cell clause $x$ is the single
literal whose variable is the cell variable $C[T, k_1, 0, x]$ (time $T$, stack $k_1$, depth $0$
from the top, symbol code $x$, for height $H$) and which is positive exactly when $x = e_a$. -/
def cellLits (T H x : ℕ) : List (ℕ × Bool) := [(L.cIdx H T k1 0 x, decide (x = ea))]

/-- **The accept family of a layout.** Let $L$ be a layout with label block size $A$, $K$ stacks
and $g$ symbol codes, let $n_1, a, k_1, e, T, H$ be natural numbers, $W = A + K H g$ and
$V = (T + 1) W$. The accept family is the CNF formula over $V$ variables made of, first, for each
$u < n_1$ in increasing order, the clause whose only literal is the label variable $X[T, u]$
(variable $T W + u$), positive if $u = a$ and negative otherwise; then, for each $x < g$ in
increasing order, the clause whose only literal is the top-cell variable $C[T, k_1, 0, x]$ of
stack $k_1$ (variable $T W + A + k_1 H g + x$), positive if $x = e$ and negative otherwise. Each
clause is a dense row of $V$ slots: the slot of its variable holds the literal and every other
slot is empty (all slots are empty if the variable is at least $V$). -/
def accFam (T H : ℕ) : CNF :=
  (List.range n1).map (fun u => denseClause (L.numVars T H) (codeLits L ac T H u)) ++
    (List.range L.g).map (fun x => denseClause (L.numVars T H) (cellLits L k1 ea T H x))

end Spec

/-! ## [FAM] The generator machine -/

/-- **Counters of the accept generator.** The accept-family generator has sixteen distinct unit
counters, named $\mathsf{Tn}$, $\mathsf{Hs}$, $\mathsf{Gc}$, $\mathsf{HG}$, $\mathsf{Wc}$,
$\mathsf{Kc}$, $\mathsf{K1}$, $\mathsf{Vc}$, $\mathsf{TW}$, $\mathsf{CB}$, $\mathsf{P}$,
$\mathsf{Q}$, $\mathsf{tmp}$, $\mathsf{md}$, $\mathsf{c1}$ and $\mathsf{c2}$. -/
inductive CK
  | Tn | Hs | Gc | HG | Wc | Kc | K1 | Vc | TW | CB | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Hs, CK.Gc, CK.HG, CK.Wc, CK.Kc, CK.K1, CK.Vc, CK.TW, CK.CB, CK.P, CK.Q,
      CK.tmp, CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Clause kinds of the accept generator.** For natural numbers $n_1$ and $g$, a clause kind is
either a code clause $u$ for some $u < n_1$ or a cell clause $x$ for some $x < g$. -/
inductive AK (n1 g : ℕ)
  | code (u : Fin n1)
  | cell (x : Fin g)
  deriving DecidableEq, Fintype

namespace AK

variable {n1 g : ℕ}

/-- **Base counter of an accept clause.** For a clause kind $c$ of the accept generator, the
base counter of its single literal is the counter $\mathsf{TW}$ when $c$ is a code clause and
the counter $\mathsf{CB}$ when $c$ is a cell clause. -/
def bc : AK n1 g → CK
  | code _ => .TW
  | cell _ => .CB

/-- **Offset of a clause's literal.** For $n_1, g \in \mathbb{N}$, the offset of a clause kind of
the accept generator is its index: $u$ for the code clause $u < n_1$ and $x$ for the cell clause
$x < g$. It is the distance of the clause's single literal from its base counter. -/
def off : AK n1 g → ℕ
  | code u => u
  | cell x => x

/-- **Polarity of an accept clause's literal.** Fix naturals $n_1$ and $g$, and let $a$ and $e$
be naturals. The polarity of the code clause of $u < n_1$ is true exactly when $u = a$, and the
polarity of the cell clause of $x < g$ is true exactly when $x = e$. -/
def sg (ac ea : ℕ) : AK n1 g → Bool
  | code u => decide (u.val = ac)
  | cell x => decide (x.val = ea)

theorem bc_ne (c : AK n1 g) : c.bc ≠ .Q ∧ c.bc ≠ .tmp ∧ c.bc ≠ .P := by
  cases c <;> simp [bc]

end AK

/-- **Precomputation stages of the accept generator.** Write $A$, $K$ and $g$ for the
label/state block size, the number of stacks and the number of symbol codes of the generator's
layout, and $k_1$ for the index of the stack whose top cell it checks. A precomputation stage is
one of eight plain stages or one of five multiplication stages, each of which carries a stage $s$
of the multiplication routine. Named by the step the generator takes there, in the order it runs
them, they are: push $g$ units on $\mathsf{Gc}$; multiply into $\mathsf{HG}$ at $s$; push $A$
units on $\mathsf{Wc}$; push $K$ units on $\mathsf{Kc}$; multiply into $\mathsf{Wc}$ at $s$;
multiply into $\mathsf{TW}$ at $s$; increment $\mathsf{Tn}$; multiply into $\mathsf{Vc}$ at $s$;
drain $\mathsf{TW}$ onto both $\mathsf{CB}$ and $\mathsf{tmp}$; drain $\mathsf{tmp}$ back onto
$\mathsf{TW}$; push $A$ units on $\mathsf{CB}$; push $k_1$ units on $\mathsf{K1}$; multiply into
$\mathsf{CB}$ at $s$. -/
inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | tw (s : MS) | inc | v (s : MS)
  | cb1 | cb2 | cbA | k1 | cbM (s : MS)
  deriving DecidableEq, Fintype

/-- **Stages of the accept generator's literal routine.** The stages of the accept generator's
routine emitting a clause's literal are $\mathrm{cp1}$, $\mathrm{cp2}$, $\mathrm{eo}$,
$\mathrm{dec}$, $\mathrm{cmp}$, $r(o)$ and $r_B(o)$ for each ordering $o \in \{<, =, >\}$,
$\mathrm{emL}$, $\mathrm{bad}$, $\mathrm{slot}$ and $\mathrm{dq}$. They form a finite type with
decidable equality. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- **Labels of the accept generator.** For $n_1, g \in \mathbb{N}$, a label is one of: a
precomputation stage; $\mathrm{e00}(c)$, $\mathrm{cv1}(c)$, $\mathrm{cv2}(c)$ or
$\mathrm{fin}(c)$ for a clause kind $c$ (a code clause $u < n_1$ or a cell clause $x < g$);
$\mathrm{lit}(c, s)$ for a clause kind $c$ and a stage $s$ of the literal routine; or the halting
label $\mathrm{done}$. The labels form a finite type with decidable equality. -/
inductive GL (n1 g : ℕ)
  | pre (s : PS)
  | e00 (c : AK n1 g) | cv1 (c : AK n1 g) | cv2 (c : AK n1 g) | lit (c : AK n1 g) (s : LS)
  | fin (c : AK n1 g)
  | done
  deriving DecidableEq, Fintype

namespace GL

variable {n1 g : ℕ}

/-- **Entry label of an accept code clause.** For a generator with $n_1$ code clauses and $g$ cell
clauses and $u \in \mathbb{N}$, the code-chain label at $u$ is the entry label of code clause $u$
when $u < n_1$, and the halting label $\mathrm{done}$ when $u \ge n_1$. -/
def codeFrom (u : ℕ) : GL n1 g := if h : u < n1 then .e00 (.code ⟨u, h⟩) else .done

/-- **Start of the accept code chain.** For a generator with $n_1$ code clauses, the code chain
starts at the entry label of code clause $n_1 - 1$ (the last one, as clauses are emitted last
first), or at the halting label $\mathrm{done}$ when $n_1 = 0$. -/
def codeStart : GL n1 g := if n1 = 0 then .done else codeFrom (n1 - 1)

/-- **Entry label of an accept cell clause.** For a generator with $n_1$ code clauses and $g$ cell
clauses and $x \in \mathbb{N}$, the cell-chain label at $x$ is the entry label of cell clause $x$
when $x < g$, and the start of the code chain when $x \ge g$. -/
def cellFrom (x : ℕ) : GL n1 g := if h : x < g then .e00 (.cell ⟨x, h⟩) else codeStart

/-- **First clause label of the accept generator.** Fix naturals $n_1$ and $g$, the numbers
of code clauses and of cell clauses. Clauses are emitted last first, so the label at which clause
emission starts is the start label of the cell clause of $g - 1$ when $g > 0$. When $g = 0$ it is
the start label of the code clause of $n_1 - 1$ if $n_1 > 0$, and the final label if $n_1 = 0$. -/
def start : GL n1 g := if g = 0 then codeStart else cellFrom (g - 1)

/-- **Next label after a clause of the accept generator.** Let $n_1, g \in \mathbb{N}$; clauses are
emitted last first. After the code clause $u < n_1$ the generator goes to the halting label
$\mathrm{done}$ if $u = 0$, and otherwise to the first label $\mathrm{e00}$ of code clause
$u - 1$. After the cell clause $x < g$ it goes, if $x = 0$, to the start of the code chain (the
first label of code clause $n_1 - 1$, or $\mathrm{done}$ if $n_1 = 0$), and otherwise to the
first label of cell clause $x - 1$. -/
def nextC : AK n1 g → GL n1 g
  | .code u => if u.val = 0 then .done else codeFrom (u.val - 1)
  | .cell x => if x.val = 0 then codeStart else cellFrom (x.val - 1)

theorem codeFrom_of_lt {u : ℕ} (h : u < n1) : (codeFrom u : GL n1 g) = .e00 (.code ⟨u, h⟩) :=
  dite_eq_left h

theorem cellFrom_of_lt {x : ℕ} (h : x < g) : (cellFrom x : GL n1 g) = .e00 (.cell ⟨x, h⟩) :=
  dite_eq_left h

end GL

section Machine

variable (L : Layout) (n1 ac k1 ea : ℕ)

/-- **Literal routine of the accept generator.** Fix a layout $L$ with $g$ symbol codes and
parameters $n_1$, $\mathrm{ac}$, $\mathrm{ea}$, and a clause kind $c$ with base counter $b(c)$,
offset $\mathrm{off}(c)$ and polarity $\sigma(c)$. The literal routine of $c$ gives the
generator's statement at each label $\mathrm{lit}(c, s)$; below, a stage $s$ stands for the label
$\mathrm{lit}(c, s)$, and moving a counter onto targets means popping it until it is empty and
pushing one unit onto every target for each unit popped. At $\mathrm{cp1}$ it moves $b(c)$ onto
$Q$ and $\mathrm{tmp}$, then goes to $\mathrm{cp2}$. At $\mathrm{cp2}$ it moves $\mathrm{tmp}$
onto $b(c)$, then goes to $\mathrm{eo}$. At $\mathrm{eo}$ it pushes $\mathrm{off}(c)$ units onto
$Q$ and goes to $\mathrm{dec}$. At $\mathrm{dec}$ it pops $P$ and goes to $\mathrm{bad}$ if $P$
was empty, else to $\mathrm{cmp}$. At $\mathrm{cmp}$ it pops one unit from each nonempty one of
$P$ and $Q$, pushing a unit onto $c_1$ for $P$ and onto $c_2$ for $Q$; it repeats
$\mathrm{cmp}$ if both were nonempty, and otherwise goes to $r(o)$, where the ordering $o$ is
$<$ if only $Q$ was nonempty, $=$ if both were empty, and $>$ if only $P$ was nonempty. At
$r(o)$ it moves $c_1$ onto $P$, then goes to $r_B(o)$. At $r_B(o)$ it moves $c_2$ onto $Q$,
then goes to $\mathrm{slot}$ if $o$ is $=$ and to $\mathrm{emL}$ otherwise. At $\mathrm{emL}$ it
prepends the bits false, true to the output and goes to $\mathrm{dec}$. At $\mathrm{bad}$ it
halts. At $\mathrm{slot}$ it prepends the bits true, $\lnot\sigma(c)$ to the output and goes to
$\mathrm{dq}$. At $\mathrm{dq}$ it empties $Q$, then goes to $\mathrm{fin}(c)$. -/
def litP (c : AK n1 L.g) : LS → TM2.Stmt (SΓ CK) (GL n1 L.g) Bool
  | .cp1 => xfer (.c c.bc) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c .cp1) (.lit c .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c c.bc, ()⟩] (.lit c .cp2) (.lit c .eo)
  | .eo => emitR (.c .Q) (List.replicate c.off ()) (.lit c .dec)
  | .dec => decr (.c .P) (.lit c .bad) (.lit c .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c .cmp)
      (.lit c (.r .lt)) (.lit c (.r .eq)) (.lit c (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c (.r o)) (.lit c (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c (.rB o))
      (if o = .eq then .lit c .slot else .lit c .emL)
  | .emL => emitR .out [false, true] (.lit c .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg ac ea))) (.lit c .dq)
  | .dq => xfer (.c .Q) [] (.lit c .dq) (.fin c)

/-- **Generator machine for the accept family.** Fix a layout $L$ with label/state block size
$A$, $K$ stacks and $g$ symbol codes, and naturals $n_1$, $a$, $k_1$, $e$. The generator is a
multi-stack machine with a Boolean output stack, the unit counters of the generator, and a
Boolean internal state. Its precomputation pushes $g$ units on $\mathsf{Gc}$, adds
$\mathsf{Hs} \cdot \mathsf{Gc}$ to $\mathsf{HG}$, pushes $A$ units on $\mathsf{Wc}$, pushes $K$
units on $\mathsf{Kc}$, adds $\mathsf{Kc} \cdot \mathsf{HG}$ to $\mathsf{Wc}$, adds
$\mathsf{Tn} \cdot \mathsf{Wc}$ to $\mathsf{TW}$, pushes one unit on $\mathsf{Tn}$, adds
$\mathsf{Tn} \cdot \mathsf{Wc}$ to $\mathsf{Vc}$, drains $\mathsf{TW}$ onto both $\mathsf{CB}$
and $\mathsf{tmp}$ and then $\mathsf{tmp}$ back onto $\mathsf{TW}$, pushes $A$ units on
$\mathsf{CB}$, pushes $k_1$ units on $\mathsf{K1}$, adds $\mathsf{K1} \cdot \mathsf{HG}$ to
$\mathsf{CB}$, and goes to the first clause label; each multiplication uses $\mathsf{md}$ as
its index counter and $\mathsf{tmp}$ as scratch. For each clause $c$ (a code clause of $u < n_1$
or a cell clause of $x < g$) it prepends $[\mathrm{false}, \mathrm{false}]$ to the output,
drains $\mathsf{Vc}$ onto both $\mathsf{P}$ and $\mathsf{tmp}$ and then $\mathsf{tmp}$ back onto
$\mathsf{Vc}$, runs the literal routine of $c$ with polarity parameters $a$ and $e$, drains
$\mathsf{P}$ while prepending $[\mathrm{false}, \mathrm{true}]$ to the output once per unit, and
goes to the label after $c$. At its final label it halts.

It is meant to be started with $T$ on $\mathsf{Tn}$, $H$ on $\mathsf{Hs}$ and every other
counter empty. -/
def prog : GL n1 L.g → TM2.Stmt (SΓ CK) (GL n1 L.g) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Kc) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Kc .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre (.tw .head)) s
  | .pre (.tw s) => mulS .Tn .md .Wc .TW .tmp (fun s => .pre (.tw s)) (.pre .inc) s
  | .pre .inc => incr (.c .Tn) () (.pre (.v .head))
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .cb1) s
  | .pre .cb1 => xfer (.c .TW) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.pre .cb1) (.pre .cb2)
  | .pre .cb2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.pre .cb2) (.pre .cbA)
  | .pre .cbA => emitR (.c .CB) (List.replicate L.A ()) (.pre .k1)
  | .pre .k1 => emitR (.c .K1) (List.replicate k1 ()) (.pre (.cbM .head))
  | .pre (.cbM s) => mulS .K1 .md .HG .CB .tmp (fun s => .pre (.cbM s)) GL.start s
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (.lit c .cp1)
  | .lit c s => litP L n1 ac ea c s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GL.nextC c)
  | .done => .halt

/-- **The accept generator as a finite multi-stack machine.** For a layout $L$ with $g$ symbol
codes and natural numbers $n_1, a, k_1, e$, this is the finite multi-stack Turing machine whose
stacks are an output stack of bits and one unary counter for each of the generator's sixteen
counter names, whose input stack is the counter $T_n$ and output stack the bit stack, whose labels
are the generator's labels for $n_1$ code clauses and $g$ cell clauses with start label the first
precomputation stage, whose internal states are booleans with initial state false, and whose
transition function is the accept generator for $L$, $n_1$, $a$, $k_1$, $e$.

It serves only to check that the generator meets the finiteness conditions of a finite machine. -/
def accTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := GL n1 L.g
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L n1 ac k1 ea

end Machine

/-! ## [FAM] Correctness: one clause -/

section Clause

variable {L : Layout} {n1 ac k1 ea : ℕ}

/-- **Empty scratch counters of the accept generator.** An assignment $F$ of a natural number to
each counter of the generator satisfies this predicate when $F$ is zero on the scratch counters
$\mathsf{Q}$, $\mathsf{tmp}$, $\mathsf{md}$, $\mathsf{c1}$ and $\mathsf{c2}$.

The generator keeps these counters empty whenever a clause starts. -/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

/-- **Run of the literal routine of the accept generator.** Let $c$ be a clause kind with base
counter $b(c)$, offset $\mathrm{off}(c)$ and polarity $\sigma(c)$, and let $F$ assign values to
the counters of the accept generator (for layout $L$ and parameters $n_1$, $\mathrm{ac}$, $k_1$,
$\mathrm{ea}$) such that the scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$
are $0$. Let $q, m \in \mathbb{N}$ with $q = F(b(c)) + \mathrm{off}(c)$ and
$F(P) = q + m + 1$. Then for every output word $o$ and every Boolean state $v$, the generator
runs in at most $m(3q + 6) + 2F(b(c)) + 4q + 9$ steps from the label
$\mathrm{lit}(c, \mathrm{cp1})$, with state $v$, counters $F$ and output $o$, to the label
$\mathrm{fin}(c)$, with state false, the counters $F$ except that $P$ holds $q$, and output
$s\,z\,o$. Here $s$ is the two bits true, $\lnot\sigma(c)$ (the encoding of a slot holding a
literal of polarity $\sigma(c)$), and $z$ is $m$ copies of the two bits false, true (the
encoding of $m$ empty slots). -/
theorem lit_run (c : AK n1 L.g) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F c.bc + c.off) (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L n1 ac k1 ea) (gap * (3 * q + 6) + 2 * F c.bc + 4 * q + 9)
      ⟨some (.lit c .cp1), v, st F o⟩
      ⟨some (.fin c), false,
        st (update F .P q) (encodeSlot (some (c.sg ac ea)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  refine Bud.start ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .lit c .cp1) (l₂ := .lit c .cp2)
    (next := .lit c .eo) rfl rfl b1 b2 (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .lit c .eo) (next := .lit c .dec) rfl _ _
    _).bud ?_
  refine (gapS (M := prog L n1 ac k1 ea) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true])
    (dec := .lit c .dec) (cmpL := .lit c .cmp) (emitL := .lit c .emL)
    (ifZero := .lit c .bad) (next := .lit c .slot) (r := fun o => .lit c (.r o))
    (rB := fun o => .lit c (.rB o))
    (out := fun o => if o = .eq then .lit c .slot else .lit c .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L n1 ac k1 ea) (self := .lit c .slot) (next := .lit c .dq) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L n1 ac k1 ea) (self := .lit c .dq) (next := .fin c) (x := .Q) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- **Step bound for one accept clause.** For $V \in \mathbb{N}$, the step budget for one clause of
the accept generator is $B(V) = V(3V + 6) + 10V + 13$. -/
def clauseB (V : ℕ) : ℕ := V * (3 * V + 6) + 10 * V + 13

theorem encodeClause_unit {V p : ℕ} {b : Bool} (h : p < V) :
    encodeClause (denseClause V [(p, b)]) =
      rep [false, true] p ++ encodeSlot (some b) ++ rep [false, true] (V - p - 1) ++
        [false, false] := by
  rw [encodeClause_denseClause (show Inc 0 [(p, b)] V from ⟨Nat.zero_le _, h⟩)]
  simp only [gapEnc, Nat.sub_zero, List.append_assoc]
  rw [show V - (p + 1) = V - p - 1 by omega]

/-- **One clause of the accept generator.** Let $L$ be a layout with $g$ symbol codes, let
$n_1, a, k_1, e, V \in \mathbb{N}$, and let $c$ be a clause kind of the accept generator (a code
clause $u < n_1$ or a cell clause $x < g$) with base counter $b(c)$, offset $\mathrm{off}(c)$ and
polarity $\sigma(c)$ for $a$ and $e$. Let $F$ be counter values of the generator whose scratch
counters $\mathsf{Q}$, $\mathsf{tmp}$, $\mathsf{md}$, $\mathsf{c1}$, $\mathsf{c2}$ are $0$, with
$F(\mathsf{Vc}) = V$, $F(\mathsf{P}) = 0$ and $p = F(b(c)) + \mathrm{off}(c) < V$. Then for every
output word $o$ and every Boolean state $v$, the accept generator for $L$, $n_1$, $a$, $k_1$, $e$
runs in at most $V(3V + 6) + 10V + 13$ steps from the label $\mathrm{e00}(c)$, with state $v$,
counters $F$ and output $o$, to the label after clause $c$, with state false, the same counters
$F$, and output the encoding of the dense clause over $V$ variables whose only literal is the
variable $p$ with polarity $\sigma(c)$, followed by $o$. -/
theorem clause_run {V : ℕ} (c : AK n1 L.g) (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V)
    (hP : F .P = 0) (hlt : F c.bc + c.off < V) (o : List Bool) (v : Bool) :
    RunLe (prog L n1 ac k1 ea) (clauseB V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GL.nextC c), false,
        st F (encodeClause (denseClause V [(F c.bc + c.off, c.sg ac ea)]) ++ o)⟩ := by
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  set p := F c.bc + c.off with hpdef
  refine Bud.start ?_
  refine (emitOut (M := prog L n1 ac k1 ea) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := .lit c .cp1)
    rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  have r := lit_run (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) c (update F .P (F .Vc + F .P))
    ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
    p (V - p - 1) (by simp [hpdef, b3]) (by simp [hV, hP]; omega) ([false, false] ++ o) false
  refine r.bud ?_
  refine (xferES (M := prog L n1 ac k1 ea) (self := .fin c) (next := GL.nextC c) (x := .P) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp only [update_self, ne_eq, b3, not_false_eq_true, update_of_ne, hV, hP]
    have h1 : (V - p - 1) * (3 * p + 6) ≤ V * (3 * V + 6) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold clauseB
    omega
  · rw [encodeClause_unit hlt]
    simp only [update_self, update_idem, List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hP]

end Clause

/-! ## [FAM] Correctness: the two label chains and the whole generator -/

section Top

variable {L : Layout} {n1 ac k1 ea : ℕ}

/-- **Run of the code-clause chain of the accept generator.** Let $F$ assign values to the
counters of the accept generator (for layout $L$ and parameters $n_1$, $\mathrm{ac}$, $k_1$,
$\mathrm{ea}$) such that the scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$
are $0$, $F(\mathrm{Vc}) = V$, $F(P) = 0$ and $F(\mathrm{TW}) + n_1 \le V$. Then for every
$u < n_1$, every output word $o$ and every Boolean state $v$, the generator runs in at most
$(u + 1)(V(3V + 6) + 10V + 13)$ steps from the first label of code clause $u$, with state $v$,
counters $F$ and output $o$, to the halting label $\mathrm{done}$, with state false, counters $F$
and output $w_0 w_1 \cdots w_u\, o$. Here $w_i$ is the encoding of the dense clause over $V$
variables whose only literal is variable $F(\mathrm{TW}) + i$, positive if and only if
$i = \mathrm{ac}$. -/
theorem codes_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) :
    ∀ u, u < n1 → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L n1 ac k1 ea) ((u + 1) * clauseB V) ⟨some (GL.codeFrom u), v, st F o⟩
        ⟨some .done, false, st F ((List.range (u + 1)).flatMap
          (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++ o)⟩ := by
  intro u
  induction u with
  | zero =>
      intro hu o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.code ⟨0,
          hu⟩) F hF hV hP
        (by simp only [AK.bc, AK.off]; omega) o v
      rw [GL.codeFrom_of_lt hu]
      simpa [GL.nextC, AK.bc, AK.off, AK.sg] using r
  | succ u ih =>
      intro hu o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.code ⟨u + 1,
          hu⟩) F hF
        hV hP (by simp only [AK.bc, AK.off]; omega) o v
      simp only [GL.nextC, AK.bc, AK.off, AK.sg, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel] at r
      rw [GL.codeFrom_of_lt hu]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V [(F .TW + (u + 1),
          decide (u + 1 = ac))]) ++ o)
        false
      rw [List.range_succ (n := u + 1), List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (u + 1)]; omega

theorem codeStart_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) (o : List Bool) :
    RunLe (prog L n1 ac k1 ea) (n1 * clauseB V) ⟨some GL.codeStart, false, st F o⟩
      ⟨some .done, false, st F ((List.range n1).flatMap
        (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++ o)⟩ := by
  by_cases h : n1 = 0
  · subst h
    simp only [GL.codeStart, ite_true, List.range_zero, List.flatMap_nil, List.nil_append]
    exact ⟨0, Nat.zero_le _, Run.zero _⟩
  · rw [GL.codeStart, ite_eq_right h]
    have := codes_run (L := L) (ac := ac) (k1 := k1) (ea := ea) F hF hV hP hlt (n1 - 1) (by omega)
      o false
    rwa [Nat.sub_add_cancel (by omega)] at this

/-- **Run of the accept cell chain.** Let $L$ be a layout with $g$ symbol codes, let
$n_1, a_c, k_1, e_a \in \mathbb{N}$ be the parameters of the generator, and let $F$ give a value
to every counter of the generator such that the scratch counters $\mathsf{Q}$, $\mathsf{tmp}$,
$\mathsf{md}$, $\mathsf{c1}$, $\mathsf{c2}$ are $0$, $F(\mathsf{Vc}) = V$, $F(\mathsf{P}) = 0$,
$F(\mathsf{TW}) + n_1 \le V$ and $F(\mathsf{CB}) + g \le V$. Write
$B(V) = V(3V + 6) + 10V + 13$ for the one-clause step bound. Then for every $x < g$, every
output stack $o$ and every state bit $v$, the generator started at the entry label of cell
clause $x$ with state $v$, counters $F$ and output $o$ reaches the halting label $\mathrm{done}$
within $(x + 1)B(V) + n_1 B(V)$ steps, with state false, counters $F$, and output consisting of
the encodings of the dense clauses over $V$ variables whose single literal is at
$F(\mathsf{TW}) + u$, positive exactly when $u = a_c$, for $u = 0, \dots, n_1 - 1$, then of
those whose single literal is at $F(\mathsf{CB}) + y$, positive exactly when $y = e_a$, for
$y = 0, \dots, x$, then $o$. -/
theorem cells_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) (hlc : F .CB + L.g ≤ V) :
    ∀ x, x < L.g → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L n1 ac k1 ea) ((x + 1) * clauseB V + n1 * clauseB V)
        ⟨some (GL.cellFrom x), v, st F o⟩
        ⟨some .done, false, st F ((List.range n1).flatMap
          (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++
          (List.range (x + 1)).flatMap
          (fun x => encodeClause (denseClause V [(F .CB + x, decide (x = ea))])) ++ o)⟩ := by
  intro x
  induction x with
  | zero =>
      intro hx o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.cell ⟨0,
          hx⟩) F hF hV hP
        (by simp only [AK.bc, AK.off]; omega) o v
      rw [GL.cellFrom_of_lt hx]
      simp only [GL.nextC, AK.bc, AK.off, AK.sg, ite_true] at r
      refine Bud.start (r.bud ?_)
      have := codeStart_run (L := L) (ac := ac) (k1 := k1) (ea := ea) F hF hV hP hlt
        (encodeClause (denseClause V [(F .CB + 0, decide (0 = ea))]) ++ o)
      simp only [zero_add, List.range_one, List.flatMap_singleton, List.append_assoc] at this ⊢
      refine this.bud (Bud.fin ?_ rfl)
      omega
  | succ x ih =>
      intro hx o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.cell ⟨x + 1,
          hx⟩) F hF
        hV hP (by simp only [AK.bc, AK.off]; omega) o v
      simp only [GL.nextC, AK.bc, AK.off, AK.sg, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel] at r
      rw [GL.cellFrom_of_lt hx]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V [(F .CB + (x + 1),
          decide (x + 1 = ea))]) ++ o)
        false
      rw [List.range_succ (n := x + 1), List.flatMap_append, List.flatMap_singleton]
      simp only [List.append_assoc] at this ⊢
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (x + 1)]; omega

/-- **Initial counters of the accept generator.** For $T, H \in \mathbb{N}$, the initial counter
values are $T$ on the counter $\mathrm{Tn}$, $H$ on the counter $\mathrm{Hs}$, and $0$ on every
other counter. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

/-- **Counters after the precomputation of the accept generator.** For a layout $L$ with $A$
label/state variables per row, $K$ stacks and $g$ symbol codes, and for $k_1, T, H \in \mathbb{N}$,
let $W = A + KHg$ be the row width. The counter values after the precomputation are $T + 1$ on
$\mathrm{Tn}$, $H$ on $\mathrm{Hs}$, $g$ on $\mathrm{Gc}$, $Hg$ on $\mathrm{HG}$, $W$ on
$\mathrm{Wc}$, $K$ on $\mathrm{Kc}$, $k_1$ on $\mathrm{K1}$, $(T + 1)W$ on $\mathrm{Vc}$, $TW$ on
$\mathrm{TW}$, $TW + A + k_1Hg$ on $\mathrm{CB}$ (the index of the cell variable of stack $k_1$,
depth $0$ and symbol code $0$ at time $T$), and $0$ on every other counter. -/
def preF (L : Layout) (k1 T H : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Kc => L.KK
  | .K1 => k1
  | .Vc => L.numVars T H
  | .TW => T * L.rowW H
  | .CB => L.cIdx H T k1 0 0
  | _ => 0

/-- **Cost of the precomputation of the accept generator.** For a layout $L$ with $A$
label/state variables per row, $K$ stacks and $g$ symbol codes, and for $k_1, T, H \in \mathbb{N}$,
let $W = A + KHg$ be the row width. The step budget of the precomputation is
$3 + (H(2g + 3) + H + 2) + (K(2Hg + 3) + K + 2) + (T(2W + 3) + T + 2) + 1 +
((T + 1)(2W + 3) + (T + 1) + 2) + (2TW + 2) + 2 + (k_1(2Hg + 3) + k_1 + 2)$. -/
def preB (L : Layout) (k1 T H : ℕ) : ℕ :=
  3 + (H * (2 * L.g + 3) + H + 2) + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) +
    (T * (2 * L.rowW H + 3) + T + 2) + 1 + ((T + 1) * (2 * L.rowW H + 3) + (T + 1) + 2) +
    (2 * (T * L.rowW H) + 2) + 2 + (k1 * (2 * (H * L.g) + 3) + k1 + 2)

/-- **Explicit time bound of the accept generator.** For a layout $L$ with label block size $A$,
$K$ stacks and $g$ symbol codes, and natural numbers $n_1$, $k_1$, $T$, $H$, let
$W = A + K H g$ and $V = (T + 1) W$ (the number of variables). The bound is $P + (g + n_1)\,C$,
where $C = V(3V + 6) + 10V + 13$ is the cost of one clause and the precomputation cost is
$P = 3 + (H(2g + 3) + H + 2) + (K(2Hg + 3) + K + 2) + (T(2W + 3) + T + 2) + 1 +
((T + 1)(2W + 3) + (T + 1) + 2) + (2TW + 2) + 2 + (k_1(2Hg + 3) + k_1 + 2)$.

It is at most $314\,(A + K + g + n_1 + k_1 + 1)^5\,(T + H + 1)^4$. -/
def accBound (L : Layout) (n1 k1 T H : ℕ) : ℕ :=
  preB L k1 T H + (L.g + n1) * clauseB (L.numVars T H)

theorem encodeCNF_accFam (T H : ℕ) :
    encodeCNF (accFam L n1 ac k1 ea T H) =
      (List.range n1).flatMap (fun u => encodeClause (denseClause (L.numVars T H)
        [(T * L.rowW H + u, decide (u = ac))])) ++
      (List.range L.g).flatMap (fun x => encodeClause (denseClause (L.numVars T H)
        [(L.cIdx H T k1 0 0 + x, decide (x = ea))])) := by
  simp only [encodeCNF, accFam, List.flatMap_append, List.flatMap_map, codeLits, cellLits]
  rfl

/-- **Run of the accept generator's precomputation.** Fix a layout $L$ with label/state block
size $A$, $K$ stacks and $g$ symbol codes, and naturals $n_1$, $a$, $k_1$, $e$. For all
$T, H \in \mathbb{N}$ and every list $o$ of Booleans, write $W = A + K H g$ for the row width.
The accept generator, started at its first precomputation label with internal state false,
output $o$, $T$ units on counter $\mathsf{Tn}$, $H$ units on $\mathsf{Hs}$ and every other
counter empty, reaches in at most $\mathrm{preB}(L, k_1, T, H)$ steps the first clause label
with internal state false, output still $o$, and counters $\mathsf{Tn} = T + 1$,
$\mathsf{Hs} = H$, $\mathsf{Gc} = g$, $\mathsf{HG} = H g$, $\mathsf{Wc} = W$, $\mathsf{Kc} = K$,
$\mathsf{K1} = k_1$, $\mathsf{Vc} = (T + 1) W$, $\mathsf{TW} = T W$,
$\mathsf{CB} = T W + A + k_1 H g$, and every other counter empty. -/
theorem pre_run (T H : ℕ) (o : List Bool) :
    RunLe (prog L n1 ac k1 ea) (preB L k1 T H)
      ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some GL.start, false, st (preF L k1 T H) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.hg s)) (next := .pre .ew)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .ek) (next := .pre (.w .head)) (x := .Kc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.w s)) (next := .pre (.tw .head))
    (a := .Kc) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.tw s)) (next := .pre .inc)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (incS (M := prog L n1 ac k1 ea) (self := .pre .inc) (next := .pre (.v .head)) (x := .Tn)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.v s)) (next := .pre .cb1)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .pre .cb1) (l₂ := .pre .cb2) (next := .pre .cbA)
    rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .cbA) (next := .pre .k1) (x := .CB) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .k1) (next := .pre (.cbM .head)) (x := .K1)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.cbM s)) (next := GL.start)
    (a := .K1) (ad := .md) (b := .HG) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L k1 T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars, Layout.cIdx] <;>
      first | ring1 | (left; ring1)) (Bud.fin ?_ rfl)
  simp [initF, preB, Layout.rowW]
  ring_nf
  omega

/-- **Correctness of the accept generator, with its explicit time bound.** Let $L$ be a layout
with label block size $A$ and $K$ stacks, and let $n_1, a, k_1, e, T, H$ be natural numbers with
$n_1 \le A$, $k_1 < K$ and $H > 0$. Start the accept generator for $L$, $n_1$, $a$, $k_1$, $e$ at
its start label, with internal state false, $T$ and $H$ in unary on its counters $T_n$ and $H_s$,
all other counters empty and an arbitrary bit list $o$ on its output stack. Within a number of
steps at most the explicit time bound for $L$, $n_1$, $k_1$, $T$, $H$, it reaches the label done,
with some internal state, and its output stack then holds the binary encoding of the accept family
of $L$ for $n_1$, $a$, $k_1$, $e$ at $T$, $H$ followed by $o$.

The hypotheses say that the code block fits in the label block, that $k_1$ is a stack, and that
there is a top cell. -/
theorem acc_run (hn1 : n1 ≤ L.A) (hk1 : k1 < L.KK) (T H : ℕ) (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L n1 ac k1 ea) (accBound L n1 k1 T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (accFam L n1 ac k1 ea T H) ++ o := by
  refine ⟨false, st (preF L k1 T H) ((List.range n1).flatMap (fun u => encodeClause
    (denseClause (L.numVars T H) [(T * L.rowW H + u, decide (u = ac))])) ++
      (List.range L.g).flatMap (fun x => encodeClause (denseClause (L.numVars T H)
        [(L.cIdx H T k1 0 0 + x, decide (x = ea))])) ++ o), ?_, by
    rw [encodeCNF_accFam]; rfl⟩
  refine Bud.start ((pre_run (ac := ac) (ea := ea) T H o).bud ?_)
  have hR : Rest (preF L k1 T H) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hW : L.A ≤ L.rowW H := Nat.le_add_right _ _
  have hlt : preF L k1 T H .TW + n1 ≤ L.numVars T H := by
    simp only [preF, Layout.numVars]; rw [Nat.succ_mul]; omega
  have hlc : preF L k1 T H .CB + L.g ≤ L.numVars T H := by
    have := Cslib.Complexity.CookLevin.OneHot.base_le (L := L) (T := T) (H := H) (t := T) (k := k1) (j := 0) le_rfl hk1 hH
    simp only [preF]
    rw [← Cslib.Complexity.CookLevin.OneHot.base_eq]; simpa using this
  by_cases hg : L.g = 0
  · have hst : (GL.start : GL n1 L.g) = GL.codeStart := by simp [GL.start, hg]
    rw [hst, show List.range L.g = [] by simp [hg], List.flatMap_nil, List.append_nil]
    refine (codeStart_run (L := L) (ac := ac) (k1 := k1) (ea := ea) _ hR rfl rfl hlt o).bud
      (Bud.fin ?_ rfl)
    unfold accBound; simp only [preF, hg, zero_add]; omega
  · have hst : (GL.start : GL n1 L.g) = GL.cellFrom (L.g - 1) := by simp [GL.start, hg]
    rw [hst]
    have r := cells_run (L := L) (ac := ac) (k1 := k1) (ea := ea) _ hR rfl rfl hlt hlc (L.g - 1)
      (by omega) o false
    rw [Nat.sub_add_cancel (by omega)] at r
    simp only [List.append_assoc] at r ⊢
    refine r.bud (Bud.fin ?_ rfl)
    unfold accBound; simp only [preF]; rw [Nat.add_mul]; omega

end Top

/-! ## [BOUND] The time bound is polynomial: `accBound ≤ accC · (T + H + 1)^4` -/

section Poly

theorem accBound_mono {L L' : Layout} {n1 n1' k1 k1' T T' H H' : ℕ} (hA : L.A ≤ L'.A)
    (hK : L.KK ≤ L'.KK) (hg : L.g ≤ L'.g) (hn : n1 ≤ n1') (hk : k1 ≤ k1') (hT : T ≤ T')
    (hH : H ≤ H') : accBound L n1 k1 T H ≤ accBound L' n1' k1' T' H' := by
  unfold accBound preB clauseB Layout.numVars Layout.rowW
  gcongr

/-- **The accept generator's time bound on the uniform layout.** For all natural numbers $k \ge 1$
and $y \ge 1$, the explicit time bound of the accept generator for the layout with all four
constants equal to $k$, with $n_1 = k_1 = k$ and $T = H = y$, is at most $314\,k^5 y^4$.

Every monomial of the bound is at most $k^5 y^4$, and the coefficients sum to $314$, the value of
the bound at $k = y = 1$. -/
theorem accBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    accBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k k y y ≤ 314 * k ^ 5 * y ^ 4 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 4 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 4 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold accBound preB clauseB Layout.numVars Layout.rowW Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 0 3 (by norm_num) (by norm_num),
    m 0 4 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 1 4 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num),
    m 3 0 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num),
    m 4 0 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 5 0 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num)]

/-- The constant 314 is exact: the sum of the coefficients. -/
example : accBound (Cslib.Complexity.CookLevin.Family.Layout.uni 1) 1 1 1 1 = 314 := rfl

/-- **Constant of the accept generator's time bound.** For a layout $L$ with label block size
$A$, $K$ stacks and $g$ symbol codes, and natural numbers $n_1$, $k_1$, the constant is
$314\,(A + K + g + n_1 + k_1 + 1)^5$. -/
def accC (L : Layout) (n1 k1 : ℕ) : ℕ := 314 * (L.A + L.KK + L.g + n1 + k1 + 1) ^ 5

theorem accBound_le (L : Layout) (n1 k1 T H : ℕ) :
    accBound L n1 k1 T H ≤ accC L n1 k1 * (T + H + 1) ^ 4 := by
  have := accBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + n1 + k1 + 1))
    (n1 := n1) (k1 := k1)
    (n1' := L.A + L.KK + L.g + n1 + k1 + 1) (k1' := L.A + L.KK + L.g + n1 + k1 + 1)
    (T := T) (T' := T + H + 1) (H := H) (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := accBound_uni (L.A + L.KK + L.g + n1 + k1 + 1) (T + H + 1) (by omega) (by omega)
  unfold accC
  exact this.trans h2

/-- **Polynomial time bound of the accept generator.** Let $L$ be a layout with label block size
$A$, $K$ stacks and $g$ symbol codes, let $n_1, a, k_1, e, T, H$ be natural numbers with
$n_1 \le A$, $k_1 < K$ and $H > 0$, and let $c = 314\,(A + K + g + n_1 + k_1 + 1)^5$. Start the
accept generator for $L$, $n_1$, $a$, $k_1$, $e$ at its start label, with internal state false,
$T$ and $H$ in unary on its counters $T_n$ and $H_s$, all other counters empty and an arbitrary
bit list $o$ on its output stack. Within at most $c\,(T + H + 1)^4$ steps it reaches the label
done, with some internal state, and its output stack then holds the binary encoding of the accept
family of $L$ for $n_1$, $a$, $k_1$, $e$ at $T$, $H$ followed by $o$. -/
theorem acc_time {L : Layout} {n1 ac k1 ea : ℕ} (hn1 : n1 ≤ L.A) (hk1 : k1 < L.KK) (T H : ℕ)
    (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L n1 ac k1 ea) (accC L n1 k1 * (T + H + 1) ^ 4)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (accFam L n1 ac k1 ea T H) ++ o :=
  let ⟨v, S, h, h'⟩ := acc_run hn1 hk1 T H hH o; ⟨v, S, h.mono (accBound_le L n1 k1 T H), h'⟩

end Poly

/-! ## [FAM] Link to the semantic family `Situation.Enc.accFamily` -/

section Link

variable {M : FinTM2} (E : Cslib.Complexity.CookLevin.Situation.Enc M)

/-- **The concrete accept family is a layout-level accept family.** Let $M$ be a finite
multi-stack Turing machine with encoding $E$, let $\mathit{acc}$ be a symbol of the output stack
of $M$, and let $T$, $H$ be natural numbers. The accept family of $E$ for $\mathit{acc}$ at $T$,
$H$ equals, by definition, the accept family of the layout of $E$ at $T$, $H$ with parameters
$n_1 = A_0$, the number of (label, state) codes of $E$; $a$, the (label, state) code of the
halted configuration (no label, initial state); $k_1$, the number $E$ gives the output stack; and
$e$, the code of $\mathit{acc}$. -/
theorem accFamily_eq (acc : M.Γ M.k₁) (T H : ℕ) :
    E.accFamily acc T H = accFam E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc) T H := rfl

/-- **Time bound of the accept generator for a concrete machine.** Let $M$ be a finite
multi-stack Turing machine with encoding $E$, let $\mathit{acc}$ be a symbol of the output stack
of $M$, and let $T$, $H$ be natural numbers with $H > 0$. Let $L$ be the layout of $E$, with
label block size $A$, $K$ stacks and $g$ symbol codes, let $A_0$ be the number of (label, state)
codes of $E$, let $k_1$ be the number $E$ gives the output stack, and let
$c = 314\,(A + K + g + A_0 + k_1 + 1)^5$. Start the accept generator for $L$, $A_0$, the code of
the halted configuration, $k_1$ and the code of $\mathit{acc}$ at its start label, with internal
state false, $T$ and $H$ in unary on its counters $T_n$ and $H_s$, all other counters empty and
an arbitrary bit list $o$ on its output stack. Within at most $c\,(T + H + 1)^4$ steps it reaches
the label done, with some internal state, and its output stack then holds the binary encoding of
the accept family of $E$ for $\mathit{acc}$ at $T$, $H$ followed by $o$. -/
theorem acc_gen_time (acc : M.Γ M.k₁) (T H : ℕ) (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc))
        (accC E.layout E.A0 (E.kc M.k₁) * (T + H + 1) ^ 4)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (E.accFamily acc T H) ++ o :=
  acc_time (Nat.le_add_right _ _) (E.kc_lt _) T H hH o

end Link

end Cslib.Complexity.CookLevin.Accept
