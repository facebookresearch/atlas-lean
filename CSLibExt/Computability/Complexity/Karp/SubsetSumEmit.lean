/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumDigits
public import MathlibExt.Computability.TuringMachine.BitOps

/-!
# Karp reductions, component: VERTEX-COVER → SUBSET-SUM

One `TM2` machine `prog` computing `reduceSS` of `Cslib.Complexity.Karp` on raw bits, in time
quadratic in the input (`run` states the bound as `40 · (|x| + 1)⁴`).

The input `x` lies on stack `X` as `Sym.bit`s; the output is built on the `Bool` stack `O`, which
reads top first, so the instance `encodeSS (ssNums n bits) (ssTarget k n bits)` is pushed from
its end. The phases:

1. Parse `k` (unary, onto `A`) and `n` (unary, onto `N`, with `n` unmarked vertices on `L`); a
   missing separator writes `noSS`.
2. Move the pair bits to `Y` (reversed, last pair on top), count them on `C`, and push the
   target's low digits onto `T` (bits `false, bit q` for each pair `q`, least significant first).
3. Count the pairs, `tri n`, onto `M` and compare with `C` (`cmpStep`); a mismatch writes
   `noSS`.
4. Edge numbers, from the last pair down: pop each pair bit onto `Z`; an edge `q` writes
   `delimit (encodeNat (4 ^ q))` (its `2q` zero digits by `xferE` from the counter `C = q`).
5. Vertex numbers, from vertex `n - 1` down: the vertex marks lie on `L` (top: vertex `n - 1`)
   with vertex `v` marked. Walking the pairs from the last one means rows `i` descending,
   columns `j` ascending; the marks form a zipper, the row vertex on top of `L` and the columns on
   `R` (`walkM`), so pair `(i, j)` with bit `b` gives digit `b && (mark i || mark j)`, i.e.
   `touches`. Each pair writes four output bits (`blk`). Afterwards `Y` is restored from `Z` and
   the marks move back from `R` to `L`, the mark shifting from `v` to `v - 1`.
6. Target: halve `A` repeatedly, pushing the bits of `encodeNat k` onto `T`; then pop `T` (most
   significant bit first), skip leading zeros, and write the rest delimited.

`run`: from `start` with `x` on `X` and the other stacks empty, `prog` reaches `done` with
`reduceSS x` on `O`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitSS

open Turing Function MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Complexity.SatVerifier
  Computability MetaMathlibExt.BitstringEncoding

/-- **Stacks of the SUBSET-SUM reduction machine.** The machine has fifteen stacks: the input $X$
and the output $O$; $A$, which holds the cover size $k$, and $H$, used to halve it; $N$, which
holds the number $n$ of vertices, and $M$, the pair count; $C$, which counts the pair bits; the
scratch stacks $S_1$ and $S_2$; $Y$ and $Z$, which hold the pair bits; $T$, which holds the
target's bits; and $L$, $R$ and $R_t$, which hold the vertex marks. -/
inductive K | X | O | A | H | N | M | C | S1 | S2 | Y | Z | T | L | R | Rt
  deriving DecidableEq

/-- The stacks, listed. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .O, .A, .H, .N, .M, .C, .S1, .S2, .Y, .Z, .T, .L, .R, .Rt], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabets of the subset-sum emitter.** In the VERTEX-COVER to SUBSET-SUM machine the
output stack $\mathsf{O}$ holds Booleans, and every other stack holds token symbols. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Labels of the subset-sum emitter.** The control labels of the subset-sum emitter machine
are: $\mathrm{rdK}$, $\mathrm{rdN}$ and $\mathrm{mv}$ (parsing the two unary numbers $k$ and $n$
that open the input, and moving the pair bits); $\mathrm{tri}$, $\mathrm{triC}$,
$\mathrm{triC2}$, $\mathrm{cmp}$ and, for every ordering $o$, the labels $\mathrm{rc}(o)$ and
$\mathrm{rcB}(o)$ (counting the pairs and comparing that count with the number of pair bits);
$\mathrm{eg}$, $\mathrm{egX}$, $\mathrm{egR}$, $\mathrm{egR2}$ and $\mathrm{egY}$ (the edge
numbers); $\mathrm{vinit}$, $\mathrm{vtx}$, $\mathrm{pr}$, $\mathrm{rend}$, $\mathrm{rmv}$,
$\mathrm{vend}$, $\mathrm{vchk}$ and $\mathrm{rs}$ (the vertex numbers); $\mathrm{hv}$,
$\mathrm{hv0}$, $\mathrm{hv1}$ and $\mathrm{hvB}$ (the binary digits of $k$); $\mathrm{tem0}$,
$\mathrm{tsk}$ and $\mathrm{tem}$ (writing the target); $\mathrm{bad}$, which writes the fixed
no-instance; and the halting label $\mathrm{done}$. -/
inductive Lab
  | rdK | rdN | mv | tri | triC | triC2 | cmp | rc (o : Ordering) | rcB (o : Ordering)
  | eg | egX | egR | egR2 | egY | vinit | vtx | pr | rend | rmv | vend | vchk | rs
  | hv | hv0 | hv1 | hvB | tem0 | tsk | tem | bad | done
  deriving DecidableEq

/-- The labels, listed. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdK, .rdN, .mv, .tri, .triC, .triC2, .cmp, .rc .lt, .rc .eq, .rc .gt,
    .rcB .lt, .rcB .eq, .rcB .gt, .eg, .egX, .egR, .egR2, .egY, .vinit, .vtx, .pr, .rend, .rmv,
    .vend, .vchk, .rs, .hv, .hv0, .hv1, .hvB, .tem0, .tsk, .tem, .bad, .done], by decide⟩
  complete := fun x => by
    rcases x with _ | _ | _ | _ | _ | _ | _ | o | o <;> try decide
    all_goals cases o <;> decide

/-- **Counter unit of the subset-sum emitter.** The unit symbol of the counters of the
VERTEX-COVER to SUBSET-SUM machine is the token symbol $\mathrm{cl}$; a counter with value $n$
holds exactly $n$ copies of it. -/
abbrev U : Sym := .cl

/-- **Test for the input bit true (SUBSET-SUM reduction machine).** On the result of a pop, which
is either a symbol or nothing (when the stack was empty), the test returns true exactly when the
result is the input-bit symbol $\mathrm{bit}(\mathrm{true})$, and false otherwise. -/
def isT : Option Sym → Bool
  | some (.bit true) => true
  | _ => false

/-- **Test for the value symbol true (SUBSET-SUM reduction machine).** On the result of a pop,
which is either a symbol or nothing (when the stack was empty), the test returns true exactly when
the result is the value symbol $\mathrm{val}(\mathrm{true})$, which this machine uses for a pair
bit or vertex mark that is true, and false otherwise. -/
def isV : Option Sym → Bool
  | some (.val true) => true
  | _ => false

/-- **Reading a pair bit or vertex mark.** The partial map from token symbols to bits that
sends the symbol $\mathrm{val}(b)$ to $b$ and gives no value on every other symbol. -/
def valOf : Sym → Option Bool
  | .val b => some b
  | _ => none

/-- **Branch after the count comparison (SUBSET-SUM reduction machine).** The label the machine
takes after comparing the pair-bit count with the pair count: the result "equal" leads to the
label $\mathrm{eg}$, which starts the edge-number phase, and the results "less than" and
"greater than" lead to the failure label $\mathrm{bad}$, which writes the fixed no-instance of
SUBSET-SUM. -/
def cmpOut : Ordering → Lab
  | .eq => .eg
  | _ => .bad

/-- **The subset-sum emitter machine.** A multi-stack machine with the labels of the subset-sum
emitter as control labels, a Boolean internal state, and the stacks of the emitter: the output
stack $O$ holds bits, every other stack holds symbols. Stacks are read top first, $U$ is the
counter unit, and to prepend a list to $O$ is to push it so that it reads top first. The labels
act as follows.

$\mathrm{rdK}$: if $X$ is empty, go to $\mathrm{bad}$; otherwise pop $X$, and if the popped
symbol is $\mathrm{bit}(\mathrm{true})$ push $U$ on $A$ and repeat, else go to $\mathrm{rdN}$.
$\mathrm{rdN}$: the same, except that each $\mathrm{bit}(\mathrm{true})$ pushes $U$ on $N$ and
$\mathrm{val}(\mathrm{false})$ on $L$, and the other case goes to $\mathrm{mv}$. $\mathrm{mv}$: if
$X$ is empty, go to $\mathrm{tri}$; otherwise pop $X$, let $s$ say whether the popped symbol is
$\mathrm{bit}(\mathrm{true})$, push $\mathrm{val}(s)$ on $Y$, then $\mathrm{bit}(\mathrm{false})$
and $\mathrm{bit}(s)$ on $T$, then $U$ on $C$, and repeat.

$\mathrm{tri}$: pop $N$; if it was empty go to $\mathrm{cmp}$, else go to $\mathrm{triC}$, which
pops $N$ until it is empty, pushing $U$ on $M$ and on $S_1$ for each popped symbol, and then to
$\mathrm{triC2}$, which pops $S_1$ until it is empty, pushing $U$ on $N$ for each, and returns to
$\mathrm{tri}$. $\mathrm{cmp}$: pop $C$ and $M$ together, pushing $U$ on $S_1$ for each symbol
popped from $C$ and on $S_2$ for each symbol popped from $M$, until one of them was empty; go to
$\mathrm{rc}(o)$ where $o$ is $<$, $=$ or $>$ according as only $C$, both, or only $M$ was empty.
$\mathrm{rc}(o)$ pops $S_1$ until empty, pushing $U$ on $C$ for each, then $\mathrm{rcB}(o)$ pops
$S_2$ until empty, pushing $U$ on $M$ for each, then goes to $\mathrm{eg}$ if $o$ is $=$ and to
$\mathrm{bad}$ otherwise.

$\mathrm{eg}$: if $Y$ is empty, go to $\mathrm{egY}$; otherwise pop $Y$, let $s$ say whether the
popped symbol is $\mathrm{val}(\mathrm{true})$, push $\mathrm{val}(s)$ on $Z$, pop $C$ and $M$,
and if $s$ is true prepend $(\mathrm{true}, \mathrm{true}, \mathrm{false})$ to $O$ and go to
$\mathrm{egX}$, else prepend $(\mathrm{false})$ to $O$ and repeat. $\mathrm{egX}$ pops $C$ until
it is empty, prepending $(\mathrm{true}, \mathrm{false}, \mathrm{true}, \mathrm{false})$ to $O$
for each popped symbol; then $\mathrm{egR}$ pops $M$ until empty, pushing $U$ on $C$ and on $S_1$
for each, and $\mathrm{egR2}$ pops $S_1$ until empty, pushing $U$ on $M$ for each, and returns to
$\mathrm{eg}$. $\mathrm{egY}$: while the top of $Z$ is some $\mathrm{val}(b)$, pop it and push
$\mathrm{val}(b)$ on $Y$; then go to $\mathrm{vinit}$.

$\mathrm{vinit}$: pop $L$; if a symbol was popped, push $\mathrm{val}(\mathrm{true})$ on $L$ and
go to $\mathrm{vtx}$, else go to $\mathrm{hv}$. $\mathrm{vtx}$: prepend
$(\mathrm{true}, \mathrm{true}, \mathrm{false})$ to $O$ and go to $\mathrm{pr}$. $\mathrm{pr}$: if
$R$ is empty, go to $\mathrm{rend}$; otherwise pop $R$, let $m$ be true exactly when the popped
symbol is $\mathrm{val}(\mathrm{true})$ and push $\mathrm{val}(m)$ on $\mathrm{Rt}$, let $a$ be
true exactly when the top of $L$ is $\mathrm{val}(\mathrm{true})$, pop $Y$, let $b$ be true
exactly when a $\mathrm{val}(\mathrm{true})$ was popped and push $\mathrm{val}(b)$ on $Z$,
prepend $(\mathrm{true}, b \wedge (m \vee a), \mathrm{true}, \mathrm{false})$ to $O$, and repeat.
$\mathrm{rend}$: while the top of $\mathrm{Rt}$ is some $\mathrm{val}(b)$, pop it and push
$\mathrm{val}(b)$ on $R$; then go to $\mathrm{rmv}$. $\mathrm{rmv}$: pop $L$, push
$\mathrm{val}(t)$ on $R$ where $t$ is true exactly when a $\mathrm{val}(\mathrm{true})$ was
popped, and go to $\mathrm{vend}$ if $L$ is now empty, else to $\mathrm{pr}$. $\mathrm{vend}$:
while the top of $Z$ is some $\mathrm{val}(b)$, pop it and push $\mathrm{val}(b)$ on $Y$; then
go to $\mathrm{vchk}$. $\mathrm{vchk}$: go to $\mathrm{hv}$ if the top of $R$ is
$\mathrm{val}(\mathrm{true})$, else to $\mathrm{rs}$. $\mathrm{rs}$: if $R$ is empty, go to
$\mathrm{vtx}$; otherwise pop $R$; if the popped symbol is $\mathrm{val}(\mathrm{true})$, pop $L$
and push $\mathrm{val}(\mathrm{true})$ and then $\mathrm{val}(\mathrm{false})$ on $L$, else push
$\mathrm{val}(\mathrm{false})$ on $L$; repeat.

$\mathrm{hv}$: go to $\mathrm{tem0}$ if $A$ is empty, else to $\mathrm{hv0}$. $\mathrm{hv0}$: pop
$A$; if it was empty, push $\mathrm{bit}(\mathrm{false})$ on $T$ and go to $\mathrm{hvB}$, else go
to $\mathrm{hv1}$. $\mathrm{hv1}$: pop $A$; if it was empty, push $\mathrm{bit}(\mathrm{true})$
on $T$ and go to $\mathrm{hvB}$, else push $U$ on $H$ and go to $\mathrm{hv0}$. $\mathrm{hvB}$
pops $H$ until it is empty, pushing $U$ on $A$ for each, and returns to $\mathrm{hv}$.
$\mathrm{tem0}$: prepend $(\mathrm{false})$ to $O$ and go to $\mathrm{tsk}$. $\mathrm{tsk}$: if
$T$ is empty, go to $\mathrm{done}$; otherwise pop $T$, and if the popped symbol is
$\mathrm{bit}(\mathrm{true})$ prepend $(\mathrm{true}, \mathrm{true})$ to $O$ and go to
$\mathrm{tem}$, else repeat. $\mathrm{tem}$: if $T$ is empty, go to $\mathrm{done}$; otherwise pop
$T$, let $s$ say whether the popped symbol is $\mathrm{bit}(\mathrm{true})$, prepend
$(\mathrm{true}, s)$ to $O$, and repeat. $\mathrm{bad}$: prepend the encoding of the subset-sum
instance with no numbers and target $1$ to $O$ and go to $\mathrm{done}$. $\mathrm{done}$: halt. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .rdK => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .bad) <|
      .pop .X (fun _ o => isT o) <| .branch id
        (.push .A (fun _ => U) (.goto fun _ => .rdK)) (.goto fun _ => .rdN)
  | .rdN => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .bad) <|
      .pop .X (fun _ o => isT o) <| .branch id
        (.push .N (fun _ => U) <| .push .L (fun _ => .val false) <| .goto fun _ => .rdN)
        (.goto fun _ => .mv)
  | .mv => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .tri) <|
      .pop .X (fun _ o => isT o) <| .push .Y (fun s => .val s) <|
      .push .T (fun _ => .bit false) <| .push .T (fun s => .bit s) <|
      .push .C (fun _ => U) <| .goto fun _ => .mv
  | .tri => decr .N .cmp .triC
  | .triC => xfer .N [⟨.M, U⟩, ⟨.S1, U⟩] .triC .triC2
  | .triC2 => xfer .S1 [⟨.N, U⟩] .triC2 .tri
  | .cmp => cmpStep .C .M .S1 .S2 U U .cmp (.rc .lt) (.rc .eq) (.rc .gt)
  | .rc o => xfer .S1 [⟨.C, U⟩] (.rc o) (.rcB o)
  | .rcB o => xfer .S2 [⟨.M, U⟩] (.rcB o) (cmpOut o)
  | .eg => .peek .Y (fun _ o => o.isNone) <| .branch id (.goto fun _ => .egY) <|
      .pop .Y (fun _ o => isV o) <| .push .Z (fun s => .val s) <|
      .pop .C (fun s _ => s) <| .pop .M (fun s _ => s) <| .branch id
        (.push .O (fun _ => false) <| .push .O (fun _ => true) <| .push .O (fun _ => true) <|
          .goto fun _ => .egX)
        (.push .O (fun _ => false) <| .goto fun _ => .eg)
  | .egX => xferE .C .O [true, false, true, false] .egX .egR
  | .egR => xfer .M [⟨.C, U⟩, ⟨.S1, U⟩] .egR .egR2
  | .egR2 => xfer .S1 [⟨.M, U⟩] .egR2 .eg
  | .egY => moveB .Z .Y valOf Sym.val .egY .vinit
  | .vinit => .pop .L (fun _ o => o.isSome) <| .branch id
      (.push .L (fun _ => .val true) <| .goto fun _ => .vtx) (.goto fun _ => .hv)
  | .vtx => emit .O [false, true, true] .pr
  | .pr => .peek .R (fun _ o => o.isNone) <| .branch id (.goto fun _ => .rend) <|
      .pop .R (fun _ o => isV o) <| .push .Rt (fun s => .val s) <|
      .peek .L (fun s o => s || isV o) <| .branch id
        (.pop .Y (fun _ o => isV o) <| .push .Z (fun s => .val s) <|
          .push .O (fun _ => false) <| .push .O (fun _ => true) <| .push .O (fun s => s) <|
          .push .O (fun _ => true) <| .goto fun _ => .pr)
        (.pop .Y (fun _ o => isV o) <| .push .Z (fun s => .val s) <|
          .push .O (fun _ => false) <| .push .O (fun _ => true) <| .push .O (fun _ => false) <|
          .push .O (fun _ => true) <| .goto fun _ => .pr)
  | .rend => moveB .Rt .R valOf Sym.val .rend .rmv
  | .rmv => .pop .L (fun _ o => isV o) <| .push .R (fun s => .val s) <|
      .peek .L (fun _ o => o.isNone) <| .branch id (.goto fun _ => .vend) (.goto fun _ => .pr)
  | .vend => moveB .Z .Y valOf Sym.val .vend .vchk
  | .vchk => .peek .R (fun _ o => isV o) <| .branch id (.goto fun _ => .hv)
      (.goto fun _ => .rs)
  | .rs => .peek .R (fun _ o => o.isNone) <| .branch id (.goto fun _ => .vtx) <|
      .pop .R (fun _ o => isV o) <| .branch id
        (.pop .L (fun s _ => s) <| .push .L (fun _ => .val true) <|
          .push .L (fun _ => .val false) <| .goto fun _ => .rs)
        (.push .L (fun _ => .val false) <| .goto fun _ => .rs)
  | .hv => .peek .A (fun _ o => o.isNone) <| .branch id (.goto fun _ => .tem0)
      (.goto fun _ => .hv0)
  | .hv0 => .pop .A (fun _ o => o.isSome) <| .branch id (.goto fun _ => .hv1)
      (.push .T (fun _ => .bit false) <| .goto fun _ => .hvB)
  | .hv1 => .pop .A (fun _ o => o.isSome) <| .branch id
      (.push .H (fun _ => U) <| .goto fun _ => .hv0)
      (.push .T (fun _ => .bit true) <| .goto fun _ => .hvB)
  | .hvB => xfer .H [⟨.A, U⟩] .hvB .hv
  | .tem0 => emit .O [false] .tsk
  | .tsk => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .done) <|
      .pop .T (fun _ o => isT o) <| .branch id
        (.push .O (fun _ => true) <| .push .O (fun _ => true) <| .goto fun _ => .tem)
        (.goto fun _ => .tsk)
  | .tem => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .done) <|
      .pop .T (fun _ o => isT o) <| .push .O (fun s => s) <| .push .O (fun _ => true) <|
      .goto fun _ => .tem
  | .bad => emitR .O noSS .done
  | .done => .halt

/-- **Start label of the subset-sum emitter.** The VERTEX-COVER to SUBSET-SUM machine starts at
the label $\mathsf{rdK}$, which begins parsing the input by reading its leading unary number. -/
def start : Lab := .rdK

/-! ### One-step lemmas -/

/-- **Testing a popped input bit.** For every bit $b$, the test for the input bit true of the
SUBSET-SUM reduction machine, applied to the popped symbol $\mathrm{bit}(b)$, returns $b$. -/
@[simp] theorem isT_bit (b : Bool) : isT (some (.bit b)) = b := by cases b <;> rfl

@[simp] theorem isV_val (b : Bool) : isV (some (.val b)) = b := by cases b <;> rfl

theorem isBitBlock_val (l : List Bool) : IsBitBlock valOf (l.map Sym.val) l := by
  simp [IsBitBlock, Function.comp_def, valOf]

section Steps

variable (v : Bool) (St : ∀ k, List (Γ k))

theorem rdK_true (r : List Sym) (h : St .X = Sym.bit true :: r) :
    Run prog 1 ⟨some .rdK, v, St⟩ ⟨some .rdK, true, update (update St .X r) .A (U :: St .A)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdK_false (r : List Sym) (h : St .X = Sym.bit false :: r) :
    Run prog 1 ⟨some .rdK, v, St⟩ ⟨some .rdN, false, update St .X r⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdK_nil (h : St .X = []) : Run prog 1 ⟨some .rdK, v, St⟩ ⟨some .bad, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdN_true (r : List Sym) (h : St .X = Sym.bit true :: r) :
    Run prog 1 ⟨some .rdN, v, St⟩
      ⟨some .rdN, true,
        update (update (update St .X r) .N (U :: St .N)) .L (.val false :: St .L)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdN_false (r : List Sym) (h : St .X = Sym.bit false :: r) :
    Run prog 1 ⟨some .rdN, v, St⟩ ⟨some .mv, false, update St .X r⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdN_nil (h : St .X = []) : Run prog 1 ⟨some .rdN, v, St⟩ ⟨some .bad, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem mv_bit (b : Bool) (r : List Sym) (h : St .X = Sym.bit b :: r) :
    Run prog 1 ⟨some .mv, v, St⟩ ⟨some .mv, b, update (update (update (update St .X r) .Y
      (.val b :: St .Y)) .T (.bit b :: .bit false :: St .T)) .C (U :: St .C)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem mv_nil (h : St .X = []) : Run prog 1 ⟨some .mv, v, St⟩ ⟨some .tri, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem eg_true (ys c m : List Sym) (hY : St .Y = .val true :: ys) (hC : St .C = U :: c)
    (hM : St .M = U :: m) :
    Run prog 1 ⟨some .eg, v, St⟩ ⟨some .egX, true, update (update (update (update (update St .Y ys)
      .Z (.val true :: St .Z)) .C c) .M m) .O ([true, true, false] ++ St .O)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, hY, hC, hM])

theorem eg_false (ys c m : List Sym) (hY : St .Y = .val false :: ys) (hC : St .C = U :: c)
    (hM : St .M = U :: m) :
    Run prog 1 ⟨some .eg, v, St⟩ ⟨some .eg, false, update (update (update (update (update St .Y ys)
      .Z (.val false :: St .Z)) .C c) .M m) .O (false :: St .O)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, hY, hC, hM])

theorem eg_nil (h : St .Y = []) : Run prog 1 ⟨some .eg, v, St⟩ ⟨some .egY, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem vinit_cons (l : List Sym) (h : St .L = .val false :: l) :
    Run prog 1 ⟨some .vinit, v, St⟩ ⟨some .vtx, true, update St .L (.val true :: l)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem vinit_nil (h : St .L = []) : Run prog 1 ⟨some .vinit, v, St⟩ ⟨some .hv, false, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem pr_pair (a mj b : Bool) (l rr ys : List Sym) (hR : St .R = .val mj :: rr)
    (hL : St .L = .val a :: l) (hY : St .Y = .val b :: ys) :
    Run prog 1 ⟨some .pr, v, St⟩ ⟨some .pr, b, update (update (update (update (update St .R rr)
      .Rt (.val mj :: St .Rt)) .Y ys) .Z (.val b :: St .Z)) .O (blk (b && (mj || a)) ++ St .O)⟩ :=
  Run.single (by cases mj <;> cases a <;> cases b <;> simp [prog, TM2.stepAux, hR, hL, hY, blk])

theorem pr_nil (h : St .R = []) : Run prog 1 ⟨some .pr, v, St⟩ ⟨some .rend, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rmv_end (a : Bool) (h : St .L = [.val a]) :
    Run prog 1 ⟨some .rmv, v, St⟩
      ⟨some .vend, true, update (update St .L []) .R (.val a :: St .R)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rmv_more (a : Bool) (x : Sym) (l : List Sym) (h : St .L = .val a :: x :: l) :
    Run prog 1 ⟨some .rmv, v, St⟩
      ⟨some .pr, false, update (update St .L (x :: l)) .R (.val a :: St .R)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem vchk_true (r : List Sym) (h : St .R = .val true :: r) :
    Run prog 1 ⟨some .vchk, v, St⟩ ⟨some .hv, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem vchk_false (r : List Sym) (h : St .R = .val false :: r) :
    Run prog 1 ⟨some .vchk, v, St⟩ ⟨some .rs, false, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rs_false (r : List Sym) (h : St .R = .val false :: r) :
    Run prog 1 ⟨some .rs, v, St⟩
      ⟨some .rs, false, update (update St .R r) .L (.val false :: St .L)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rs_true (r l : List Sym) (x : Sym) (hR : St .R = .val true :: r) (hL : St .L = x :: l) :
    Run prog 1 ⟨some .rs, v, St⟩
      ⟨some .rs, true, update (update St .R r) .L (.val false :: .val true :: l)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, hR, hL])

theorem rs_nil (h : St .R = []) : Run prog 1 ⟨some .rs, v, St⟩ ⟨some .vtx, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem hv_nil (h : St .A = []) : Run prog 1 ⟨some .hv, v, St⟩ ⟨some .tem0, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem hv_cons (x : Sym) (a : List Sym) (h : St .A = x :: a) :
    Run prog 1 ⟨some .hv, v, St⟩ ⟨some .hv0, false, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem hv0_nil (h : St .A = []) :
    Run prog 1 ⟨some .hv0, v, St⟩ ⟨some .hvB, false, update St .T (.bit false :: St .T)⟩ := by
  have hu : update St .A [] = St := by rw [← h, update_eq_self]
  exact Run.single (by simp [prog, TM2.stepAux, h, hu])

theorem hv0_cons (x : Sym) (a : List Sym) (h : St .A = x :: a) :
    Run prog 1 ⟨some .hv0, v, St⟩ ⟨some .hv1, true, update St .A a⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem hv1_nil (h : St .A = []) :
    Run prog 1 ⟨some .hv1, v, St⟩ ⟨some .hvB, false, update St .T (.bit true :: St .T)⟩ := by
  have hu : update St .A [] = St := by rw [← h, update_eq_self]
  exact Run.single (by simp [prog, TM2.stepAux, h, hu])

theorem hv1_cons (x : Sym) (a : List Sym) (h : St .A = x :: a) :
    Run prog 1 ⟨some .hv1, v, St⟩ ⟨some .hv0, true, update (update St .A a) .H (U :: St .H)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem tsk_nil (h : St .T = []) : Run prog 1 ⟨some .tsk, v, St⟩ ⟨some .done, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem tsk_false (t : List Sym) (h : St .T = .bit false :: t) :
    Run prog 1 ⟨some .tsk, v, St⟩ ⟨some .tsk, false, update St .T t⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem tsk_true (t : List Sym) (h : St .T = .bit true :: t) :
    Run prog 1 ⟨some .tsk, v, St⟩
      ⟨some .tem, true, update (update St .T t) .O (true :: true :: St .O)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem tem_nil (h : St .T = []) : Run prog 1 ⟨some .tem, v, St⟩ ⟨some .done, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem tem_bit (b : Bool) (t : List Sym) (h : St .T = .bit b :: t) :
    Run prog 1 ⟨some .tem, v, St⟩
      ⟨some .tem, b, update (update St .T t) .O (true :: b :: St .O)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem bad_run : Run prog 1 ⟨some .bad, v, St⟩ ⟨some .done, v, update St .O (noSS ++ St .O)⟩ :=
  emitR_run (M := prog) (self := .bad) rfl v St

end Steps

/-! ### Loops -/

section Loops

/-- **Subset-sum emitter: reading the unary k.** Let $k$ and $i$ be natural numbers, $v$ a Boolean
state, $r = (r_1, \dots, r_m)$ a list of bits and $S$ stack contents such that stack $X$ holds,
top first, $k$ copies of $\mathrm{bit}(\mathrm{true})$, then $\mathrm{bit}(\mathrm{false})$, then
$\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, and stack $A$ holds exactly $i$ copies of the
counter unit $U$. Then $k + 1$ steps of the subset-sum emitter machine lead from label
$\mathrm{rdK}$ with state $v$ and stacks $S$ to label $\mathrm{rdN}$ with some state and some
stacks $S'$ such that $S'(X)$ is $\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, $S'(A)$ holds
exactly $i + k$ copies of $U$, and every stack other than $X$ and $A$ is unchanged. -/
theorem rdK_some (k : ℕ) : ∀ (i : ℕ) (v : Bool) (St : ∀ k, List (Γ k)) (r : List Bool),
    St .X = (List.replicate k true ++ false :: r).map Sym.bit → St .A = cnt U i →
    ∃ v' S', Run prog (k + 1) ⟨some .rdK, v, St⟩ ⟨some .rdN, v', S'⟩ ∧
      S' .X = r.map Sym.bit ∧ S' .A = cnt U (i + k) ∧ ∀ j, j ≠ .X → j ≠ .A → S' j = St j := by
  induction k with
  | zero =>
      intro i v St r hX hA
      exact ⟨_, _, rdK_false v St _ (by simpa using hX), by simp, by simpa using hA,
        fun j h1 _ => by simp [update_of_ne h1]⟩
  | succ k ih =>
      intro i v St r hX hA
      have h₁ := rdK_true v St ((List.replicate k true ++ false :: r).map Sym.bit)
        (by simp [hX, List.replicate_succ])
      obtain ⟨v', S', h₂, hX', hA', hS'⟩ := ih (i + 1) true
        (update (update St .X ((List.replicate k true ++ false :: r).map Sym.bit)) .A
          (U :: St .A)) r (by simp) (by simp [hA, List.replicate_succ])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), hX', by rw [hA']; congr 1; omega, ?_⟩
      intro j h1 h2
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- **Subset-sum emitter: unterminated unary prefix at rdK.** Let $r = (r_1, \dots, r_m)$ be a
list of bits on which reading a unary length prefix fails (equivalently, no $r_i$ is
$\mathrm{false}$). Then for every Boolean state $v$ and all stack contents $S$ whose stack $X$
holds $\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, top first, $m + 1$ steps of the subset-sum
emitter machine lead from label $\mathrm{rdK}$ with state $v$ and stacks $S$ to label
$\mathrm{bad}$ with some state and some stacks that agree with $S$ on every stack other than $X$
and $A$. -/
theorem rdK_none : ∀ (r : List Bool), readUnaryLength r = none →
    ∀ (v : Bool) (St : ∀ k, List (Γ k)), St .X = r.map Sym.bit →
      ∃ v' S', Run prog (r.length + 1) ⟨some .rdK, v, St⟩ ⟨some .bad, v', S'⟩ ∧
        ∀ j, j ≠ .X → j ≠ .A → S' j = St j
  | [], _, v, St, hX => ⟨_, _, rdK_nil v St (by simpa using hX), fun _ _ _ => rfl⟩
  | false :: r, h, _, _, _ => by simp [readUnaryLength] at h
  | true :: r, h, v, St, hX => by
      have hr : readUnaryLength r = none := by simpa [readUnaryLength] using h
      have h₁ := rdK_true v St (r.map Sym.bit) (by simpa using hX)
      obtain ⟨v', S', h₂, hS'⟩ := rdK_none r hr true
        (update (update St .X (r.map Sym.bit)) .A (U :: St .A)) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), fun j h1 h2 => ?_⟩
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- **Subset-sum emitter: reading the unary n.** Let $n$ and $i$ be natural numbers, $v$ a Boolean
state, $r = (r_1, \dots, r_m)$ a list of bits and $S$ stack contents such that stack $X$ holds,
top first, $n$ copies of $\mathrm{bit}(\mathrm{true})$, then $\mathrm{bit}(\mathrm{false})$, then
$\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, stack $N$ holds exactly $i$ copies of the counter
unit $U$, and stack $L$ holds exactly $i$ copies of $\mathrm{val}(\mathrm{false})$. Then $n + 1$
steps of the subset-sum emitter machine lead from label $\mathrm{rdN}$ with state $v$ and stacks
$S$ to label $\mathrm{mv}$ with some state and some stacks $S'$ such that $S'(X)$ is
$\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, $S'(N)$ holds exactly $i + n$ copies of $U$,
$S'(L)$ holds exactly $i + n$ copies of $\mathrm{val}(\mathrm{false})$, and every stack other than
$X$, $N$ and $L$ is unchanged. -/
theorem rdN_some (n : ℕ) : ∀ (i : ℕ) (v : Bool) (St : ∀ k, List (Γ k)) (r : List Bool),
    St .X = (List.replicate n true ++ false :: r).map Sym.bit → St .N = cnt U i →
    St .L = cnt (.val false) i →
    ∃ v' S', Run prog (n + 1) ⟨some .rdN, v, St⟩ ⟨some .mv, v', S'⟩ ∧
      S' .X = r.map Sym.bit ∧ S' .N = cnt U (i + n) ∧ S' .L = cnt (.val false) (i + n) ∧
      ∀ j, j ≠ .X → j ≠ .N → j ≠ .L → S' j = St j := by
  induction n with
  | zero =>
      intro i v St r hX hN hL
      exact ⟨_, _, rdN_false v St _ (by simpa using hX), by simp, by simpa using hN,
        by simpa using hL, fun j h1 _ _ => by simp [update_of_ne h1]⟩
  | succ n ih =>
      intro i v St r hX hN hL
      have h₁ := rdN_true v St ((List.replicate n true ++ false :: r).map Sym.bit)
        (by simp [hX, List.replicate_succ])
      obtain ⟨v', S', h₂, hX', hN', hL', hS'⟩ := ih (i + 1) true
        (update (update (update St .X ((List.replicate n true ++ false :: r).map Sym.bit)) .N
          (U :: St .N)) .L (.val false :: St .L)) r (by simp) (by simp [hN, List.replicate_succ])
        (by simp [hL, List.replicate_succ])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), hX', by rw [hN']; congr 1; omega,
        by rw [hL']; congr 1; omega, ?_⟩
      intro j h1 h2 h3
      rw [hS' j h1 h2 h3]
      simp [update_of_ne h1, update_of_ne h2, update_of_ne h3]

/-- **Subset-sum emitter: unterminated unary prefix at rdN.** Let $r = (r_1, \dots, r_m)$ be a
list of bits on which reading a unary length prefix fails (equivalently, no $r_i$ is
$\mathrm{false}$). Then for every Boolean state $v$ and all stack contents $S$ whose stack $X$
holds $\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, top first, $m + 1$ steps of the subset-sum
emitter machine lead from label $\mathrm{rdN}$ with state $v$ and stacks $S$ to label
$\mathrm{bad}$ with some state and some stacks that agree with $S$ on every stack other than $X$,
$N$ and $L$. -/
theorem rdN_none : ∀ (r : List Bool), readUnaryLength r = none →
    ∀ (v : Bool) (St : ∀ k, List (Γ k)), St .X = r.map Sym.bit →
      ∃ v' S', Run prog (r.length + 1) ⟨some .rdN, v, St⟩ ⟨some .bad, v', S'⟩ ∧
        ∀ j, j ≠ .X → j ≠ .N → j ≠ .L → S' j = St j
  | [], _, v, St, hX => ⟨_, _, rdN_nil v St (by simpa using hX), fun _ _ _ _ => rfl⟩
  | false :: r, h, _, _, _ => by simp [readUnaryLength] at h
  | true :: r, h, v, St, hX => by
      have hr : readUnaryLength r = none := by simpa [readUnaryLength] using h
      have h₁ := rdN_true v St (r.map Sym.bit) (by simpa using hX)
      obtain ⟨v', S', h₂, hS'⟩ := rdN_none r hr true
        (update (update (update St .X (r.map Sym.bit)) .N (U :: St .N)) .L (.val false :: St .L))
        (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), fun j h1 h2 h3 => ?_⟩
      rw [hS' j h1 h2 h3]
      simp [update_of_ne h1, update_of_ne h2, update_of_ne h3]

/-- **Subset-sum emitter: moving the pair bits.** Let $r = (b_1, \dots, b_m)$ be a list of bits,
$v$ a Boolean state, $c$ a natural number and $S$ stack contents such that stack $X$ holds
$\mathrm{bit}(b_1), \dots, \mathrm{bit}(b_m)$, top first, and stack $C$ holds exactly $c$ copies of
the counter unit $U$. Then $m + 1$ steps of the subset-sum emitter machine lead from label
$\mathrm{mv}$ with state $v$ and stacks $S$ to label $\mathrm{tri}$ with some state and some
stacks $S'$ such that: $S'(Y)$ is $S(Y)$ after pushing $\mathrm{val}(b_1), \dots,
\mathrm{val}(b_m)$ in turn; $S'(T)$ is $S(T)$ after pushing, for $i = 1, \dots, m$ in turn,
$\mathrm{bit}(\mathrm{false})$ and then $\mathrm{bit}(b_i)$; $S'(C)$ holds exactly $c + m$ copies
of $U$; and every stack other than $X$, $Y$, $T$ and $C$ is unchanged. -/
theorem mv_run (r : List Bool) : ∀ (v : Bool) (St : ∀ k, List (Γ k)) (c : ℕ),
    St .X = r.map Sym.bit → St .C = cnt U c →
    ∃ v' S', Run prog (r.length + 1) ⟨some .mv, v, St⟩ ⟨some .tri, v', S'⟩ ∧
      S' .Y = (r.map Sym.val).reverse ++ St .Y ∧
      S' .T = ((r.flatMap fun b => [false, b]).map Sym.bit).reverse ++ St .T ∧
      S' .C = cnt U (c + r.length) ∧ ∀ j, j ≠ .X → j ≠ .Y → j ≠ .T → j ≠ .C → S' j = St j := by
  induction r with
  | nil =>
      intro v St c hX hC
      exact ⟨_, _, mv_nil v St (by simpa using hX), by simp, by simp, by simpa using hC,
        fun _ _ _ _ _ => rfl⟩
  | cons b r ih =>
      intro v St c hX hC
      have h₁ := mv_bit v St b (r.map Sym.bit) (by simpa using hX)
      obtain ⟨v', S', h₂, hY', hT', hC', hS'⟩ := ih b (update (update (update (update St .X
        (r.map Sym.bit)) .Y (.val b :: St .Y)) .T (.bit b :: .bit false :: St .T)) .C (U :: St .C))
        (c + 1) (by simp) (by simp [hC]; rfl)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), by simp [hY'], by simp [hT'],
        by rw [hC']; simp; omega, fun j h1 h2 h3 h4 => ?_⟩
      rw [hS' j h1 h2 h3 h4]
      simp [update_of_ne h1, update_of_ne h2, update_of_ne h3, update_of_ne h4]

/-- **Run of the pair-counting loop of the subset-sum emitter.** Let $n, p \in \mathbb{N}$ and
let $T_n = 0 + 1 + \dots + (n - 1)$. Start the VERTEX-COVER to SUBSET-SUM machine at label
$\mathsf{tri}$ with any state bit and with stacks $S$ in which the counter stacks $\mathsf{N}$ and
$\mathsf{M}$ hold exactly $n$ and $p$ unit symbols and the scratch stack $\mathsf{S1}$ is empty.
Then after exactly $(n + 1)^2$ steps the machine is at label $\mathsf{cmp}$ with some state bit
and stacks $S'$ in which $\mathsf{M}$ holds exactly $p + T_n$ unit symbols and every stack other
than $\mathsf{N}$ and $\mathsf{M}$ is as in $S$. -/
theorem tri_run (n : ℕ) : ∀ (p : ℕ) (v : Bool) (St : ∀ k, List (Γ k)),
    St .N = cnt U n → St .M = cnt U p → St .S1 = [] →
    ∃ v' S', Run prog ((n + 1) ^ 2) ⟨some .tri, v, St⟩ ⟨some .cmp, v', S'⟩ ∧
      S' .M = cnt U (p + tri n) ∧ ∀ j, j ≠ .N → j ≠ .M → S' j = St j := by
  induction n with
  | zero =>
      intro p v St hN hM _
      exact ⟨_, _, decr_run_zero (M := prog) (self := .tri) rfl v hN, by simpa [tri] using hM,
        fun _ _ _ => rfl⟩
  | succ n ih =>
      intro p v St hN hM hS1
      have h₁ := decr_run_cnt (M := prog) (self := .tri) rfl v hN
      have h₂ := copy_run (M := prog) (l₁ := .triC) (l₂ := .triC2) rfl rfl (by decide)
        (by decide) (by decide) n p (Flag.tag true) (update St .N (cnt U n)) (by simp)
        (by simp [hM]) (by simp [hS1])
      obtain ⟨v', S', h₃, hM', hS'⟩ := ih (n + p) (Flag.tag false)
        (update (update St .N (cnt U n)) .M (cnt U (n + p))) (by simp) (by simp) (by simp [hS1])
      refine ⟨v', S', ((h₁.trans h₂).trans h₃).of_eq (by ring), by rw [hM', tri]; congr 1; omega,
        fun j h1 h2 => ?_⟩
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- **Edge-number phase (SUBSET-SUM reduction machine).** Let $d$ be a list of bits (in the
machine, the pair bits listed from the last pair down), $v$ a value of the machine's Boolean flag
and $S$ an assignment of contents to the stacks, and write $\mathrm{val}(d)$ for the list of the
symbols $\mathrm{val}(b)$ for the entries $b$ of $d$, in order. Suppose stack $Y$ holds
$\mathrm{val}(d)$ (first element on top), stacks $C$ and $M$ each hold $|d|$ copies of the unit
symbol, and stack $S_1$ is empty. Then, starting at label $\mathrm{eg}$ with flag $v$ and stacks
$S$, the machine reaches label $\mathrm{egY}$ in at most $|d|(3|d| + 4) + 1$ steps, with some
flag $v'$ and stacks $S'$ such that $S'(Y)$ is empty, $S'(Z)$ is the reverse of
$\mathrm{val}(d)$ followed by $S(Z)$, $S'(O)$ is the edge-number output of $d$ followed by
$S(O)$, and every stack other than $Y$, $Z$, $O$, $C$, $M$ holds the same contents as in $S$.

For each pair $q$ the machine pops its bit onto $Z$ and writes its edge number, using
$C = M = q$. -/
theorem eg_run : ∀ (ds : List Bool) (v : Bool) (St : ∀ k, List (Γ k)),
    St .Y = ds.map Sym.val → St .C = cnt U ds.length → St .M = cnt U ds.length → St .S1 = [] →
    ∃ v' S', RunLe prog (ds.length * (3 * ds.length + 4) + 1) ⟨some .eg, v, St⟩
        ⟨some .egY, v', S'⟩ ∧
      S' .Y = [] ∧ S' .Z = (ds.map Sym.val).reverse ++ St .Z ∧ S' .O = edgeOut ds ++ St .O ∧
      ∀ j, j ≠ .Y → j ≠ .Z → j ≠ .O → j ≠ .C → j ≠ .M → S' j = St j
  | [], v, St, hY, _, _, _ =>
      ⟨_, _, (eg_nil v St (by simpa using hY)).le le_rfl, by simpa using hY, by simp,
        by simp [edgeOut], fun _ _ _ _ _ _ => rfl⟩
  | b :: ds, v, St, hY, hC, hM, hS1 => by
      have hl : ds.length * (3 * ds.length + 4) + 1 + (3 * ds.length + 4) ≤
          (b :: ds).length * (3 * (b :: ds).length + 4) + 1 := by simp; nlinarith
      cases b with
      | false =>
          have h₁ := eg_false v St (ds.map Sym.val) (cnt U ds.length) (cnt U ds.length)
            (by simpa using hY) (by rw [hC]; rfl) (by rw [hM]; rfl)
          obtain ⟨v', S', h₂, hY', hZ', hO', hS'⟩ := eg_run ds false
            (update (update (update (update (update St .Y (ds.map Sym.val)) .Z
              (.val false :: St .Z)) .C (cnt U ds.length)) .M (cnt U ds.length)) .O
              (false :: St .O)) (by simp) (by simp) (by simp) (by simp [hS1])
          refine ⟨v', S', ((h₁.le le_rfl).trans h₂).mono (by omega), hY', by simp [hZ'],
            by simp [hO', edgeOut, edgeEnc], fun j h1 h2 h3 h4 h5 => ?_⟩
          rw [hS' j h1 h2 h3 h4 h5]
          simp [h1, h2, h3, h4, h5]
      | true =>
          have h₁ := eg_true v St (ds.map Sym.val) (cnt U ds.length) (cnt U ds.length)
            (by simpa using hY) (by rw [hC]; rfl) (by rw [hM]; rfl)
          set S₁ := update (update (update (update (update St .Y (ds.map Sym.val)) .Z
            (.val true :: St .Z)) .C (cnt U ds.length)) .M (cnt U ds.length)) .O
            ([true, true, false] ++ St .O) with hS₁
          have h₂ := xferE_run (M := prog) (self := .egX) rfl (by decide) U ds.length
            (Flag.tag true) S₁ (by simp [hS₁])
          set S₂ := update (update S₁ .C []) .O (rep [true, false, true, false] ds.length ++ S₁ .O)
            with hS₂
          have h₃ := copy_run (M := prog) (l₁ := .egR) (l₂ := .egR2) rfl rfl (by decide)
            (by decide) (by decide) ds.length 0 (Flag.tag false) S₂ (by simp [hS₂, hS₁])
            (by simp [hS₂]) (by simp [hS₂, hS₁, hS1])
          obtain ⟨v', S', h₄, hY', hZ', hO', hS'⟩ := eg_run ds (Flag.tag false)
            (update S₂ .C (cnt U (ds.length + 0))) (by simp [hS₂, hS₁]) (by simp)
            (by simp [hS₂, hS₁]) (by simp [hS₂, hS₁, hS1])
          refine ⟨v', S', ((((h₁.trans (h₂.trans h₃)).le le_rfl)).trans h₄).mono (by omega), hY',
            by simp [hZ', hS₂, hS₁], by simp [hO', hS₂, hS₁, edgeOut, edgeEnc],
            fun j h1 h2 h3 h4 h5 => ?_⟩
          rw [hS' j h1 h2 h3 h4 h5]
          simp [hS₂, hS₁, h1, h2, h3, h4, h5]

/-- **Subset-sum emitter: one row of the pair walk.** Stacks are listed top first. Let $a$ be a
bit, $\ell$ a list of symbols, $(m_1, \dots, m_p)$ and $(b_1, \dots, b_p)$ two lists of bits of
the same length $p$, $y$ a list of symbols, $v$ a Boolean state and $S$ stack contents such that
$S(R)$ is $\mathrm{val}(m_1), \dots, \mathrm{val}(m_p)$, $S(L)$ is $\mathrm{val}(a)$ followed by
$\ell$, and $S(Y)$ is $\mathrm{val}(b_1), \dots, \mathrm{val}(b_p)$ followed by $y$. For a bit $t$
let $\mathrm{blk}(t)$ be the list $(\mathrm{true}, t, \mathrm{true}, \mathrm{false})$, and put
$d_i = b_i \wedge (m_i \vee a)$. Then $p + 1$ steps of the subset-sum emitter machine lead from
label $\mathrm{pr}$ with state $v$ and stacks $S$ to label $\mathrm{rend}$ with some state and
some stacks $S'$ such that: $S'(R)$ is empty; $S'(\mathrm{Rt})$ is
$\mathrm{val}(m_p), \dots, \mathrm{val}(m_1)$ followed by $S(\mathrm{Rt})$; $S'(Y) = y$; $S'(Z)$
is $\mathrm{val}(b_p), \dots, \mathrm{val}(b_1)$ followed by $S(Z)$; $S'(O)$ is the concatenation
$\mathrm{blk}(d_p) \cdots \mathrm{blk}(d_1)$ followed by $S(O)$; and every stack other than $R$,
$\mathrm{Rt}$, $Y$, $Z$ and $O$ is unchanged. -/
theorem pr_run (a : Bool) (l : List Sym) : ∀ (rs bs : List Bool) (v : Bool)
    (St : ∀ k, List (Γ k)) (yr : List Sym), rs.length = bs.length →
    St .R = rs.map Sym.val → St .L = .val a :: l → St .Y = bs.map Sym.val ++ yr →
    ∃ v' S', Run prog (rs.length + 1) ⟨some .pr, v, St⟩ ⟨some .rend, v', S'⟩ ∧
      S' .R = [] ∧ S' .Rt = (rs.map Sym.val).reverse ++ St .Rt ∧ S' .Y = yr ∧
      S' .Z = (bs.map Sym.val).reverse ++ St .Z ∧
      S' .O = (List.zipWith (fun mj b => b && (mj || a)) rs bs).reverse.flatMap blk ++ St .O ∧
      ∀ j, j ≠ .R → j ≠ .Rt → j ≠ .Y → j ≠ .Z → j ≠ .O → S' j = St j
  | [], [], v, St, yr, _, hR, _, hY =>
      ⟨_, _, pr_nil v St (by simpa using hR), by simpa using hR, by simp, by simpa using hY,
        by simp, by simp, fun _ _ _ _ _ _ => rfl⟩
  | [], _ :: _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _ => by simp at h
  | mj :: rs, b :: bs, v, St, yr, hlen, hR, hL, hY => by
      have h₁ := pr_pair v St a mj b l (rs.map Sym.val) (bs.map Sym.val ++ yr) (by simpa using hR)
        hL (by simpa using hY)
      obtain ⟨v', S', h₂, hR', hRt', hY', hZ', hO', hS'⟩ := pr_run a l rs bs b
        (update (update (update (update (update St .R (rs.map Sym.val)) .Rt (.val mj :: St .Rt))
          .Y (bs.map Sym.val ++ yr)) .Z (.val b :: St .Z)) .O (blk (b && (mj || a)) ++ St .O)) yr
        (by simpa using hlen) (by simp) (by simp [hL]) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), hR', by simp [hRt'], hY',
        by simp [hZ'], by simp [hO'], fun j h1 h2 h3 h4 h5 => ?_⟩
      rw [hS' j h1 h2 h3 h4 h5]
      simp [h1, h2, h3, h4, h5]

/-- **Run of the subset-sum emitter's pair walk.** Let $L_m \ne []$, $r_m$ and $w$ be lists of
booleans, and for a list $\ell$ of booleans write $\bar\ell$ for the list of mark symbols
$\mathrm{val}(x)$, $x \in \ell$. Let $(a_1, c_1), \dots, (a_m, c_m)$ be the mark pairs
$\mathrm{walkM}(L_m, r_m)$, and suppose $w = (b_1, \dots, b_m)$ has the same length $m$. Start the
emitter machine at label $\mathrm{pr}$ with any internal state $v$ and stacks $S$ such that
$S_L = \bar L_m$, $S_R = \bar r_m$, $S_{Rt}$ is empty and $S_Y = \bar w \mathbin{+\!\!+} y$ for a
list of symbols $y$. Then after exactly $2m + 3|L_m|$ steps the machine is at label
$\mathrm{vend}$, with some internal state $v'$ and stacks $S'$ such that $S'_L$ and $S'_{Rt}$ are
empty, $S'_R = \overline{\mathrm{rev}(L_m) \mathbin{+\!\!+} r_m}$, $S'_Y = y$,
$S'_Z = \mathrm{rev}(\bar w) \mathbin{+\!\!+} S_Z$ and $S'_O = \mathrm{blk}(t_m) \mathbin{+\!\!+}
\cdots \mathbin{+\!\!+} \mathrm{blk}(t_1) \mathbin{+\!\!+} S_O$,
where $t_i = b_i \wedge (c_i \vee a_i)$ and $\mathrm{blk}(t) = [\mathrm{true}, t, \mathrm{true},
\mathrm{false}]$; every stack other than $L$, $R$, $Rt$, $Y$, $Z$ and $O$ is unchanged.

The rows of the walk come from the vertex marks on $L$ (top first) and the columns from the marks
on $R$; after each row the column marks are restored from $Rt$ and the row mark moves onto $R$. -/
theorem walk_run : ∀ (Lm rm wb : List Bool) (v : Bool) (St : ∀ k, List (Γ k)) (yr : List Sym),
    Lm ≠ [] → wb.length = (walkM Lm rm).length → St .L = Lm.map Sym.val →
    St .R = rm.map Sym.val → St .Rt = [] → St .Y = wb.map Sym.val ++ yr →
    ∃ v' S', Run prog (2 * wb.length + 3 * Lm.length) ⟨some .pr, v, St⟩ ⟨some .vend, v', S'⟩ ∧
      S' .L = [] ∧ S' .R = (Lm.reverse ++ rm).map Sym.val ∧ S' .Rt = [] ∧ S' .Y = yr ∧
      S' .Z = (wb.map Sym.val).reverse ++ St .Z ∧
      S' .O = (List.zipWith (fun p b => b && (p.2 || p.1)) (walkM Lm rm) wb).reverse.flatMap blk ++
        St .O ∧
      ∀ j, j ≠ .L → j ≠ .R → j ≠ .Rt → j ≠ .Y → j ≠ .Z → j ≠ .O → S' j = St j
  | [], _, _, _, _, _, h, _, _, _, _, _ => absurd rfl h
  | a :: Lm, rm, wb, v, St, yr, _, hw, hL, hR, hRt, hY => by
      rw [walkM, List.length_append, List.length_map] at hw
      obtain ⟨bs, wb', rfl, hbs⟩ : ∃ bs wb', wb = bs ++ wb' ∧ bs.length = rm.length :=
        ⟨wb.take rm.length, wb.drop rm.length, (List.take_append_drop _ _).symm,
          by simp; omega⟩
      have hwb' : wb'.length = (walkM Lm (a :: rm)).length := by simp at hw; omega
      obtain ⟨v₁, S₁, h₁, hR₁, hRt₁, hY₁, hZ₁, hO₁, hS₁⟩ := pr_run a (Lm.map Sym.val) rm bs v St
        (wb'.map Sym.val ++ yr) hbs.symm hR (by simpa using hL) (by simp [hY])
      obtain ⟨v₂, S₂, h₂, hRt₂, hR₂, hS₂⟩ := moveB_run (M := prog) (self := .rend) rfl
        (by decide) rm.reverse ((rm.map Sym.val).reverse) [] v₁ S₁ (by simp [hRt₁, hRt])
        (by rw [← List.map_reverse]; exact isBitBlock_val _) rfl
      have hL₂ : S₂ .L = .val a :: Lm.map Sym.val := by
        rw [hS₂ _ (by decide) (by decide), hS₁ _ (by decide) (by decide) (by decide) (by decide)
          (by decide), hL, List.map_cons]
      rw [hR₁, List.append_nil, List.map_reverse, List.reverse_reverse] at hR₂
      have hO : (List.zipWith (fun p b => b && (p.2 || p.1)) (walkM (a :: Lm) rm)
          (bs ++ wb')) = List.zipWith (fun mj b => b && (mj || a)) rm bs ++
            List.zipWith (fun p b => b && (p.2 || p.1)) (walkM Lm (a :: rm)) wb' := by
        rw [walkM, List.zipWith_append (by simp [hbs]), List.zipWith_map_left]
      cases Lm with
      | nil =>
          have h₃ := rmv_end v₂ S₂ a (by simpa using hL₂)
          have hwb : wb' = [] := List.eq_nil_of_length_eq_zero (by simpa [walkM] using hwb')
          subst hwb
          refine ⟨_, _, ((h₁.trans h₂).trans h₃).of_eq (by simp; omega), by simp, ?_, ?_, ?_,
            ?_, ?_, ?_⟩
          · simp [hR₂]
          · rw [update_of_ne (by decide), update_of_ne (by decide), hRt₂]
          · rw [update_of_ne (by decide), update_of_ne (by decide),
              hS₂ _ (by decide) (by decide), hY₁, List.map_nil, List.nil_append]
          · rw [update_of_ne (by decide), update_of_ne (by decide),
              hS₂ _ (by decide) (by decide), hZ₁]
            simp
          · rw [update_of_ne (by decide), update_of_ne (by decide),
              hS₂ _ (by decide) (by decide), hO₁, hO]
            simp [walkM]
          · intro j h1 h2 h3 h4 h5 h6
            rw [update_of_ne h2, update_of_ne h1, hS₂ j h3 h2, hS₁ j h2 h3 h4 h5 h6]
      | cons x Lm =>
          have h₃ := rmv_more v₂ S₂ a (.val x) (Lm.map Sym.val) (by simpa using hL₂)
          obtain ⟨v', S', h₄, hL', hR', hRt', hY', hZ', hO', hS'⟩ := walk_run (x :: Lm) (a :: rm)
            wb' false (update (update S₂ .L (.val x :: Lm.map Sym.val)) .R
              (.val a :: S₂ .R)) yr (by simp) hwb' (by simp) (by simp [hR₂])
            (by simp [hRt₂]) (by rw [update_of_ne (by decide), update_of_ne (by decide),
              hS₂ .Y (by decide) (by decide), hY₁])
          refine ⟨v', S', (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by simp; omega), hL',
            by simp [hR'], hRt', hY', ?_, ?_, ?_⟩
          · rw [hZ', update_of_ne (by decide), update_of_ne (by decide),
              hS₂ _ (by decide) (by decide), hZ₁]
            simp
          · rw [hO', update_of_ne (by decide), update_of_ne (by decide),
              hS₂ _ (by decide) (by decide), hO₁, hO]
            simp
          · intro j h1 h2 h3 h4 h5 h6
            rw [hS' j h1 h2 h3 h4 h5 h6, update_of_ne h2, update_of_ne h1, hS₂ j h3 h2,
              hS₁ j h2 h3 h4 h5 h6]

/-- **Subset-sum emitter: one vertex number.** Stacks are listed top first. Let $n$ be a natural
number, $p_0, \dots, p_{P-1}$ the pairs $(i, j)$ with $i < j < n$ in encoding order (rows $i$
ascending, within a row $j$ descending), $(\beta_0, \dots, \beta_{P-1})$ a list of $P$ pair bits
and $w < n$ a vertex. Let $N_w = 4^P + \sum_q 4^q$, the sum over the $q < P$ such that $\beta_q$
is true and $w$ is an endpoint of $p_q$, and let $m_u$ be true if $u = w$ and false otherwise.
Let $v$ be a Boolean state and $S$ stack contents such that $S(L)$ is
$\mathrm{val}(m_{n-1}), \dots, \mathrm{val}(m_0)$, $S(Y)$ is
$\mathrm{val}(\beta_{P-1}), \dots, \mathrm{val}(\beta_0)$, and $S(R)$, $S(\mathrm{Rt})$ and $S(Z)$
are empty. Then $3P + 3n + 2$ steps of the subset-sum emitter machine lead from label
$\mathrm{vtx}$ with state $v$ and stacks $S$ to label $\mathrm{vchk}$ with some state and some
stacks $S'$ such that: $S'(L)$, $S'(\mathrm{Rt})$ and $S'(Z)$ are empty; $S'(R)$ is
$\mathrm{val}(m_0), \dots, \mathrm{val}(m_{n-1})$; $S'(Y) = S(Y)$; $S'(O)$ is the self-delimiting
encoding of the binary representation of $N_w$ (least significant bit first) followed by $S(O)$;
and every stack other than $L$, $R$, $\mathrm{Rt}$, $Y$, $Z$ and $O$ is unchanged. -/
theorem round_run (n : ℕ) (bits : List Bool) (hb : bits.length = (pairs n).length) (w : ℕ)
    (hw : w < n) (v : Bool) (St : ∀ k, List (Γ k)) (hL : St .L = (mkL n w).map Sym.val)
    (hR : St .R = []) (hRt : St .Rt = []) (hY : St .Y = bits.reverse.map Sym.val)
    (hZ : St .Z = []) :
    ∃ v' S', Run prog (3 * (pairs n).length + 3 * n + 2) ⟨some .vtx, v, St⟩
        ⟨some .vchk, v', S'⟩ ∧
      S' .L = [] ∧ S' .R = ((List.range n).map (· == w)).map Sym.val ∧ S' .Rt = [] ∧
      S' .Y = bits.reverse.map Sym.val ∧ S' .Z = [] ∧
      S' .O = delimit (encodeNat (vtxNum n bits w)) ++ St .O ∧
      ∀ j, j ≠ .L → j ≠ .R → j ≠ .Rt → j ≠ .Y → j ≠ .Z → j ≠ .O → S' j = St j := by
  have h₁ := emit_run (M := prog) (self := .vtx) rfl v St
  have hlen : (mkL n w).length = n := by simp [mkL]
  obtain ⟨v₂, S₂, h₂, hL₂, hR₂, hRt₂, hY₂, hZ₂, hO₂, hS₂⟩ := walk_run (mkL n w) [] bits.reverse v
    (update St .O ([false, true, true].reverse ++ St .O)) []
    (by rw [← List.length_pos_iff, hlen]; omega) (by rw [walkM_mkL]; simp [hb])
    (by simp [hL]) (by simp [hR]) (by simp [hRt]) (by simp [hY])
  obtain ⟨v₃, S₃, h₃, hZ₃, hY₃, hS₃⟩ := moveB_run (M := prog) (self := .vend) rfl (by decide)
    bits (bits.map Sym.val) [] v₂ S₂ (by simp [hZ₂, hZ]) (isBitBlock_val bits) rfl
  refine ⟨v₃, S₃, ((h₁.trans h₂).trans h₃).of_eq (by simp [hlen, hb]; omega), ?_, ?_, ?_, ?_,
    hZ₃, ?_, ?_⟩
  · rw [hS₃ _ (by decide) (by decide), hL₂]
  · rw [hS₃ _ (by decide) (by decide), hR₂, mkL]; simp
  · rw [hS₃ _ (by decide) (by decide), hRt₂]
  · rw [hY₃, hY₂]; simp
  · rw [hS₃ _ (by decide) (by decide), hO₂, walk_touches n bits w hb, delimit_vtx]
    simp
  · intro j h1 h2 h3 h4 h5 h6
    rw [hS₃ j h5 h4, hS₂ j h1 h2 h3 h4 h5 h6, update_of_ne h6]

theorem replicate_append_cons {α : Type} (a : ℕ) (x : α) (l : List α) :
    List.replicate a x ++ x :: l = x :: (List.replicate a x ++ l) := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, ih]

/-- **Subset-sum emitter: moving unmarked vertices back to L.** Let $c$ be a natural number,
$\rho = (\rho_1, \dots, \rho_k)$ a list of bits, $v$ a Boolean state and $S$ stack contents whose
stack $R$ holds, top first, $c$ copies of $\mathrm{val}(\mathrm{false})$ followed by
$\mathrm{val}(\rho_1), \dots, \mathrm{val}(\rho_k)$. Then $c$ steps of the subset-sum emitter
machine lead from label $\mathrm{rs}$ with state $v$ and stacks $S$ back to label $\mathrm{rs}$
with some state and some stacks $S'$ such that $S'(R)$ is
$\mathrm{val}(\rho_1), \dots, \mathrm{val}(\rho_k)$, $S'(L)$ is $c$ copies of
$\mathrm{val}(\mathrm{false})$ followed by $S(L)$, and every stack other than $R$ and $L$ is
unchanged. -/
theorem rsF_run (c : ℕ) : ∀ (v : Bool) (St : ∀ k, List (Γ k)) (rest : List Bool),
    St .R = (List.replicate c false ++ rest).map Sym.val →
    ∃ v' S', Run prog c ⟨some .rs, v, St⟩ ⟨some .rs, v', S'⟩ ∧ S' .R = rest.map Sym.val ∧
      S' .L = cnt (.val false) c ++ St .L ∧ ∀ j, j ≠ .R → j ≠ .L → S' j = St j := by
  induction c with
  | zero => exact fun v St rest hR => ⟨v, St, Run.zero _, by simpa using hR, rfl, fun _ _ _ => rfl⟩
  | succ c ih =>
      intro v St rest hR
      have h₁ := rs_false v St ((List.replicate c false ++ rest).map Sym.val)
        (by simpa [List.replicate_succ] using hR)
      obtain ⟨v', S', h₂, hR', hL', hS'⟩ := ih false (update (update St .R
        ((List.replicate c false ++ rest).map Sym.val)) .L (.val false :: St .L)) rest (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), hR', ?_, fun j h1 h2 => ?_⟩
      · rw [hL']; simp [List.replicate_succ']
      · rw [hS' j h1 h2]; simp [h1, h2]

/-- **Run of the mark-return loop of the subset-sum emitter.** Let $n, w \in \mathbb{N}$ with
$w + 1 < n$. Start the VERTEX-COVER to SUBSET-SUM machine at label $\mathsf{rs}$ with any state
bit and with stacks $S$ in which stack $\mathsf{L}$ is empty and stack $\mathsf{R}$ holds, top
first, the symbols $\mathrm{val}(b_0), \dots, \mathrm{val}(b_{n-1})$, where $b_i$ is true exactly
when $i = w + 1$. Then after exactly $n + 1$ steps the machine is at label $\mathsf{vtx}$ with
some state bit and stacks $S'$ in which $\mathsf{R}$ is empty, $\mathsf{L}$ holds, top first, the
symbols $\mathrm{val}(c_{n-1}), \dots, \mathrm{val}(c_0)$, where $c_i$ is true exactly when
$i = w$, and every stack other than $\mathsf{R}$ and $\mathsf{L}$ is as in $S$. So the vertex
mark moves from vertex $w + 1$ to vertex $w$. -/
theorem rs_run (n w : ℕ) (hw : w + 1 < n) (v : Bool) (St : ∀ k, List (Γ k))
    (hR : St .R = ((List.range n).map (· == w + 1)).map Sym.val) (hL : St .L = []) :
    ∃ v' S', Run prog (n + 1) ⟨some .rs, v, St⟩ ⟨some .vtx, v', S'⟩ ∧
      S' .L = (mkL n w).map Sym.val ∧ S' .R = [] ∧ ∀ j, j ≠ .R → j ≠ .L → S' j = St j := by
  rw [map_range_beq n (w + 1) hw] at hR
  obtain ⟨v₁, S₁, h₁, hR₁, hL₁, hS₁⟩ := rsF_run (w + 1) v St _ hR
  have h₂ := rs_true v₁ S₁ ((List.replicate (n - 1 - (w + 1)) false).map Sym.val)
    (cnt (.val false) w) (.val false) (by simpa using hR₁)
    (by simp [hL₁, hL, List.replicate_succ])
  obtain ⟨v₃, S₃, h₃, hR₃, hL₃, hS₃⟩ := rsF_run (n - 1 - (w + 1)) true
    (update (update S₁ .R ((List.replicate (n - 1 - (w + 1)) false).map Sym.val)) .L
      (.val false :: .val true :: cnt (.val false) w)) [] (by simp)
  have h₄ := rs_nil v₃ S₃ (by simpa using hR₃)
  refine ⟨_, _, (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by omega), ?_, by simpa using hR₃,
    fun j h1 h2 => ?_⟩
  · rw [hL₃, mkL, map_range_beq n w (by omega), show n - 1 - w = n - 1 - (w + 1) + 1 by omega]
    simp [List.replicate_succ, replicate_append_cons]
  · rw [hS₃ j h1 h2]; simp [h1, h2, hS₁ j h1 h2]

/-- **Run of the vertex-number phase of the subset-sum emitter.** Let $n \in \mathbb{N}$, let
$p_0, \dots, p_{P-1}$ be the vertex pairs $(i, j)$ with $i < j < n$, listed with $i$ ascending
and, for each $i$, with $j$ descending, let $\beta_0, \dots, \beta_{P-1}$ be bits, and let
$w < n$. For a vertex $u$ let $a_u$ be $4^P$ plus the sum of $4^q$ over the indices $q < P$ such
that $\beta_q$ is true and $p_q$ contains $u$. Start the VERTEX-COVER to SUBSET-SUM machine at
label $\mathsf{vtx}$ with any state bit and with stacks $S$ in which stack $\mathsf{L}$ holds, top
first, the symbols $\mathrm{val}(c_{n-1}), \dots, \mathrm{val}(c_0)$, where $c_i$ is true exactly
when $i = w$, the stacks $\mathsf{R}$, $\mathsf{Rt}$ and $\mathsf{Z}$ are empty, and stack
$\mathsf{Y}$ holds, top first, the symbols
$\mathrm{val}(\beta_{P-1}), \dots, \mathrm{val}(\beta_0)$. Then within at most
$(w + 1)(3P + 4n + 4)$ steps the machine reaches label $\mathsf{hv}$ with some state bit and
stacks $S'$ in which the output stack $\mathsf{O}$ holds, top first, the self-delimiting binary
encodings of $a_0, a_1, \dots, a_w$ followed by the contents of $\mathsf{O}$ in $S$, and every
stack other than $\mathsf{L}$, $\mathsf{R}$, $\mathsf{Rt}$, $\mathsf{Y}$, $\mathsf{Z}$ and
$\mathsf{O}$ is as in $S$. Here the binary encoding lists the bits least significant first, and
the self-delimiting encoding replaces each bit $b$ by $\mathrm{true}, b$ and appends
$\mathrm{false}$. -/
theorem vtx_run (n : ℕ) (bits : List Bool) (hb : bits.length = (pairs n).length) (w : ℕ) :
    w < n → ∀ (v : Bool) (St : ∀ k, List (Γ k)), St .L = (mkL n w).map Sym.val → St .R = [] →
    St .Rt = [] → St .Y = bits.reverse.map Sym.val → St .Z = [] →
    ∃ v' S', RunLe prog ((w + 1) * (3 * (pairs n).length + 4 * n + 4)) ⟨some .vtx, v, St⟩
        ⟨some .hv, v', S'⟩ ∧
      S' .O = ((List.range (w + 1)).map (vtxNum n bits)).flatMap (fun a => delimit (encodeNat a)) ++
        St .O ∧
      ∀ j, j ≠ .L → j ≠ .R → j ≠ .Rt → j ≠ .Y → j ≠ .Z → j ≠ .O → S' j = St j := by
  induction w with
  | zero =>
      intro hw v St hL hR hRt hY hZ
      obtain ⟨v₁, S₁, h₁, -, hR₁, -, -, -, hO₁, hS₁⟩ :=
        round_run n bits hb 0 hw v St hL hR hRt hY hZ
      rw [map_range_beq n 0 hw] at hR₁
      have h₂ := vchk_true v₁ S₁ _ (by simpa using hR₁)
      exact ⟨_, _, (h₁.trans h₂).le (by nlinarith), by simp [hO₁], hS₁⟩
  | succ w ih =>
      intro hw v St hL hR hRt hY hZ
      obtain ⟨v₁, S₁, h₁, hL₁, hR₁, hRt₁, hY₁, hZ₁, hO₁, hS₁⟩ :=
        round_run n bits hb (w + 1) hw v St hL hR hRt hY hZ
      have hR₁' := hR₁
      rw [map_range_beq n (w + 1) hw] at hR₁'
      have h₂ := vchk_false v₁ S₁ _ (by simpa [List.replicate_succ] using hR₁')
      obtain ⟨v₃, S₃, h₃, hL₃, hR₃, hS₃⟩ := rs_run n w hw false S₁ hR₁ hL₁
      obtain ⟨v₄, S₄, h₄, hO₄, hS₄⟩ := ih (by omega) v₃ S₃ hL₃ hR₃
        (by rw [hS₃ _ (by decide) (by decide), hRt₁]) (by rw [hS₃ _ (by decide) (by decide), hY₁])
        (by rw [hS₃ _ (by decide) (by decide), hZ₁])
      refine ⟨v₄, S₄, ((((h₁.trans h₂).trans h₃).le le_rfl).trans h₄).mono (by nlinarith), ?_,
        fun j h1 h2 h3 h4 h5 h6 => ?_⟩
      · rw [hO₄, hS₃ _ (by decide) (by decide), hO₁, List.range_succ (n := w + 1),
          List.map_append, List.flatMap_append]
        simp
      · rw [hS₄ j h1 h2 h3 h4 h5 h6, hS₃ j h2 h1, hS₁ j h1 h2 h3 h4 h5 h6]

/-- **One halving step of the binary conversion (SUBSET-SUM reduction machine).** Let $c$ and $p$
be natural numbers, $r$ a bit (read as $0$ or $1$ in arithmetic), $v$ a value of the machine's
Boolean flag and $S$ an assignment of contents to the stacks. Suppose stack $A$ holds $2c + r$
copies of the unit symbol and stack $H$ holds $p$ copies. Then, starting at label $\mathrm{hv0}$
with flag $v$ and stacks $S$, the machine reaches label $\mathrm{hvB}$ in exactly $2c + r + 1$
steps, with some flag $v'$ and stacks $S'$ such that $S'(A)$ is empty, $S'(H)$ holds $p + c$
copies of the unit symbol, $S'(T)$ is the input-bit symbol $\mathrm{bit}(r)$ on top of $S(T)$,
and every stack other than $A$, $H$, $T$ holds the same contents as in $S$. -/
theorem hv0_run : ∀ (c : ℕ) (r : Bool) (p : ℕ) (v : Bool) (St : ∀ k, List (Γ k)),
    St .A = cnt U (2 * c + r.toNat) → St .H = cnt U p →
    ∃ v' S', Run prog (2 * c + r.toNat + 1) ⟨some .hv0, v, St⟩ ⟨some .hvB, v', S'⟩ ∧
      S' .A = [] ∧ S' .H = cnt U (p + c) ∧ S' .T = .bit r :: St .T ∧
      ∀ j, j ≠ .A → j ≠ .H → j ≠ .T → S' j = St j
  | 0, false, p, v, St, hA, hH => ⟨_, _, hv0_nil v St (by simpa using hA), by simpa using hA,
      by simpa using hH, by simp, fun j _ _ h3 => by simp [h3]⟩
  | 0, true, p, v, St, hA, hH => by
      have h₁ := hv0_cons v St U [] (by simpa using hA)
      have h₂ := hv1_nil true (update St .A []) (by simp)
      exact ⟨_, _, h₁.trans h₂, by simp, by simpa using hH, by simp,
        fun j h1 _ h3 => by simp [h1, h3]⟩
  | c + 1, r, p, v, St, hA, hH => by
      have h₁ := hv0_cons v St U (cnt U (2 * c + r.toNat + 1))
        (by rw [hA]; rw [show 2 * (c + 1) + r.toNat = 2 * c + r.toNat + 1 + 1 by ring]; rfl)
      have h₂ := hv1_cons true (update St .A (cnt U (2 * c + r.toNat + 1))) U
        (cnt U (2 * c + r.toNat)) (by simp; rfl)
      obtain ⟨v', S', h₃, hA', hH', hT', hS'⟩ := hv0_run c r (p + 1) true
        (update (update (update St .A (cnt U (2 * c + r.toNat + 1))) .A (cnt U (2 * c + r.toNat)))
          .H (U :: update (update St .A (cnt U (2 * c + r.toNat + 1))) .A
            (cnt U (2 * c + r.toNat)) .H)) (by simp) (by simp [hH]; rfl)
      refine ⟨v', S', ((h₁.trans h₂).trans h₃).of_eq (by ring), hA', by rw [hH']; congr 1; omega,
        by simp [hT'], fun j h1 h2 h3 => ?_⟩
      rw [hS' j h1 h2 h3]; simp [h1, h2]

/-- **Binary conversion (SUBSET-SUM reduction machine).** Let $k$ be a natural number, $v$ a value
of the machine's Boolean flag and $S$ an assignment of contents to the stacks, and list the binary
digits of $k$ least significant first, without leading zeros (so there are none for $k = 0$).
Suppose stack $A$ holds $k$ copies of the unit symbol and stack $H$ is empty. Then, starting at
label $\mathrm{hv}$ with flag $v$ and stacks $S$, the machine reaches label $\mathrm{tem0}$ in at
most $6k + 1$ steps, with some flag $v'$ and stacks $S'$ such that $S'(T)$ is the reverse of the
list of input-bit symbols $\mathrm{bit}(b)$ for these binary digits $b$ of $k$, followed by
$S(T)$, and every stack other than $A$, $H$, $T$ holds the same contents as in $S$.

The machine thus pushes the binary digits of $k$ onto $T$ least significant first. -/
theorem hv_run (k : ℕ) : ∀ (v : Bool) (St : ∀ k, List (Γ k)), St .A = cnt U k → St .H = [] →
    ∃ v' S', RunLe prog (6 * k + 1) ⟨some .hv, v, St⟩ ⟨some .tem0, v', S'⟩ ∧
      S' .T = ((encodeNat k).map Sym.bit).reverse ++ St .T ∧
      ∀ j, j ≠ .A → j ≠ .H → j ≠ .T → S' j = St j := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro v St hA hH
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨_, _, (hv_nil v St (by simpa using hA)).le (by omega),
          by simp [MetaMathlibExt.TM2Recursive.encodeNat_zero], fun _ _ _ _ => rfl⟩
      obtain ⟨c, r, hc, hr⟩ : ∃ c r, c = k / 2 ∧ r = decide (k % 2 = 1) := ⟨_, _, rfl, rfl⟩
      have hkr : k = 2 * c + r.toNat := by
        subst hc hr; rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h] <;> omega
      have h₁ := hv_cons v St U (cnt U (k - 1)) (by rw [hA, show k = k - 1 + 1 by omega]; rfl)
      obtain ⟨v₂, S₂, h₂, hA₂, hH₂, hT₂, hS₂⟩ := hv0_run c r 0 false St (by rw [hA, ← hkr])
        (by simpa using hH)
      have h₃ := xfer_run (M := prog) (self := .hvB) (next := .hv) (k := .H) (ps := [⟨.A, U⟩]) rfl
        (single_nodupKeys _) (by simp [List.keys]) U c v₂ S₂ (by simpa using hH₂)
      obtain ⟨v₄, S₄, h₄, hT₄, hS₄⟩ := ih c (by omega) (Flag.tag false)
        (addU [⟨.A, U⟩] c (update S₂ .H []))
        (by rw [addU_single_self, update_of_ne (by decide), hA₂, List.append_nil])
        (by rw [addU_single_ne _ _ _ (by decide), update_self])
      refine ⟨v₄, S₄, ((((h₁.trans h₂).trans h₃).le le_rfl).trans h₄).mono (by omega), ?_,
        fun j h1 h2 h3 => ?_⟩
      · rw [hT₄, addU_single_ne _ _ _ (by decide), update_of_ne (by decide), hT₂,
          MetaMathlibExt.TM2Recursive.encodeNat_eq_cons (n := k) (by omega), ← hc, ← hr]
        simp
      · rw [hS₄ j h1 h2 h3, addU_single_ne _ _ _ h1, update_of_ne h2, hS₂ j h1 h2 h3]

/-- **Run of the target-bit loop of the subset-sum emitter.** Let $l = (b_1, \dots, b_m)$ be a
list of bits. Start the VERTEX-COVER to SUBSET-SUM machine at label $\mathsf{tem}$ with any state
bit and with stacks $S$ in which stack $\mathsf{T}$ holds exactly the bit symbols of
$b_1, \dots, b_m$, top first. Then after exactly $m + 1$ steps the machine is at label
$\mathsf{done}$ with some state bit and stacks $S'$ in which the output stack $\mathsf{O}$ holds,
top first, $\mathrm{true}, b_m, \mathrm{true}, b_{m-1}, \dots, \mathrm{true}, b_1$ followed by the
contents of $\mathsf{O}$ in $S$, and every stack other than $\mathsf{T}$ and $\mathsf{O}$ is as in
$S$. That is, each popped bit $b$ is written as $b$ and then $\mathrm{true}$. -/
theorem tem_run : ∀ (l : List Bool) (v : Bool) (St : ∀ k, List (Γ k)), St .T = l.map Sym.bit →
    ∃ v' S', Run prog (l.length + 1) ⟨some .tem, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = l.reverse.flatMap (fun b => [true, b]) ++ St .O ∧
      ∀ j, j ≠ .T → j ≠ .O → S' j = St j
  | [], v, St, hT => ⟨_, _, tem_nil v St (by simpa using hT), by simp, fun _ _ _ => rfl⟩
  | b :: l, v, St, hT => by
      have h₁ := tem_bit v St b (l.map Sym.bit) (by simpa using hT)
      obtain ⟨v', S', h₂, hO', hS'⟩ := tem_run l b
        (update (update St .T (l.map Sym.bit)) .O (true :: b :: St .O)) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), by simp [hO'],
        fun j h1 h2 => ?_⟩
      rw [hS' j h1 h2]; simp [h1, h2]

/-- **Run of the target-output phase of the subset-sum emitter.** Let $l$ be a list of bits, let
$l'$ be $l$ with its leading $\mathrm{false}$ bits removed, and let $o$ be a list of bits. Start
the VERTEX-COVER to SUBSET-SUM machine at label $\mathsf{tsk}$ with any state bit and with stacks
$S$ in which stack $\mathsf{T}$ holds exactly the bit symbols of $l$, first bit on top, and the
output stack $\mathsf{O}$ holds $\mathrm{false}$ followed by $o$. Then after exactly $|l| + 1$
steps the machine is at label $\mathsf{done}$ with some state bit and stacks $S'$ in which
$\mathsf{O}$ holds the self-delimiting encoding of the reverse of $l'$ followed by $o$, and every
stack other than $\mathsf{T}$ and $\mathsf{O}$ is as in $S$. Here the self-delimiting encoding of
a list replaces each bit $b$ by $\mathrm{true}, b$ and appends $\mathrm{false}$. -/
theorem tsk_run : ∀ (l : List Bool) (v : Bool) (St : ∀ k, List (Γ k)) (o : List Bool),
    St .T = l.map Sym.bit → St .O = false :: o →
    ∃ v' S', Run prog (l.length + 1) ⟨some .tsk, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = delimit (l.dropWhile (!·)).reverse ++ o ∧ ∀ j, j ≠ .T → j ≠ .O → S' j = St j
  | [], v, St, o, hT, hO => ⟨_, _, tsk_nil v St (by simpa using hT), by simp [hO, delimit],
      fun _ _ _ => rfl⟩
  | false :: l, v, St, o, hT, hO => by
      have h₁ := tsk_false v St (l.map Sym.bit) (by simpa using hT)
      obtain ⟨v', S', h₂, hO', hS'⟩ := tsk_run l false (update St .T (l.map Sym.bit)) o (by simp)
        (by simp [hO])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), by simp [hO'], fun j h1 h2 => ?_⟩
      rw [hS' j h1 h2]; simp [h1]
  | true :: l, v, St, o, hT, hO => by
      have h₁ := tsk_true v St (l.map Sym.bit) (by simpa using hT)
      obtain ⟨v', S', h₂, hO', hS'⟩ := tem_run l true
        (update (update St .T (l.map Sym.bit)) .O (true :: true :: St .O)) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), ?_, fun j h1 h2 => ?_⟩
      · rw [hO']; simp [hO, delimit_append_true]
      · rw [hS' j h1 h2]; simp [h1, h2]

end Loops

theorem mkL_top (w : ℕ) : mkL (w + 1) w = true :: List.replicate w false := by
  rw [mkL, map_range_beq (w + 1) w (by omega)]; simp

theorem cmpOut_ne {m n : ℕ} (h : m ≠ n) : cmpOut (compare m n) = .bad := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · rw [Nat.compare_eq_lt.2 h]; rfl
  · rw [Nat.compare_eq_gt.2 h]; rfl

/-- **Run of the VERTEX-COVER to SUBSET-SUM machine.** Let $x$ be a bit string. Start the
VERTEX-COVER to SUBSET-SUM machine at its start label with any state bit and with stacks in
which the input stack $\mathsf{X}$ holds the bit symbols of $x$, first bit on top, and every other
stack is empty. Then within at most $40(|x| + 1)^4$ steps the machine reaches the label
$\mathsf{done}$ with some state bit and stacks in which the output stack $\mathsf{O}$ holds,
top first, the image of $x$ under the bit-string reduction from VERTEX-COVER to SUBSET-SUM. -/
theorem run (x : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hX : St .X = x.map Sym.bit) (h0 : ∀ k, k ≠ .X → St k = []) :
    ∃ v' S', RunLe prog (40 * (x.length + 1) ^ 4) ⟨some start, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = reduceSS x := by
  have hN : ∀ B, B ≤ 40 * (x.length + 1) ^ 2 → B ≤ 40 * (x.length + 1) ^ 4 := fun B hB =>
    hB.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  rcases h1 : readUnaryLength x with _ | ⟨k, x'⟩
  · obtain ⟨v₁, S₁, h₁, hS₁⟩ := rdK_none x h1 v St hX
    have h₂ := bad_run v₁ S₁
    refine ⟨_, _, (h₁.trans h₂).le (hN _ (by nlinarith)), ?_⟩
    rw [update_self, hS₁ _ (by decide) (by decide), h0 _ (by decide)]
    simp [reduceSS, decodeKG, h1]
  obtain rfl := (readUnaryLength_eq_some_iff x k x').1 h1
  obtain ⟨v₁, S₁, h₁, hX₁, hA₁, hS₁⟩ := rdK_some k 0 v St x' hX (h0 _ (by decide))
  rcases h2 : readUnaryLength x' with _ | ⟨n, r⟩
  · obtain ⟨v₂, S₂, h₂, hS₂⟩ := rdN_none x' h2 v₁ S₁ hX₁
    have h₃ := bad_run v₂ S₂
    refine ⟨_, _, ((h₁.trans h₂).trans h₃).le (hN _ (by simp; nlinarith)), ?_⟩
    rw [update_self, hS₂ _ (by decide) (by decide) (by decide), hS₁ _ (by decide) (by decide),
      h0 _ (by decide)]
    simp [reduceSS, decodeKG, h2]
  obtain rfl := (readUnaryLength_eq_some_iff x' n r).1 h2
  obtain ⟨v₂, S₂, h₂, hX₂, hN₂, hL₂, hS₂⟩ := rdN_some n 0 v₁ S₁ r hX₁
    (by simp (disch := decide) only [hS₁, h0]; rfl) (by simp (disch := decide) only [hS₁, h0]; rfl)
  obtain ⟨v₃, S₃, h₃, hY₃, hT₃, hC₃, hS₃⟩ := mv_run r v₂ S₂ 0 hX₂
    (by simp (disch := decide) only [hS₂, hS₁, h0]; rfl)
  obtain ⟨v₄, S₄, h₄, hM₄, hS₄⟩ := tri_run n 0 v₃ S₃
    (by simp (disch := decide) only [hS₃, hN₂, Nat.zero_add])
    (by simp (disch := decide) only [hS₃, hS₂, hS₁, h0]; rfl)
    (by simp (disch := decide) only [hS₃, hS₂, hS₁, h0])
  have h₅ := cmp_run (M := prog) (self := .cmp) (r := Lab.rc) (rB := Lab.rcB) (out := cmpOut) rfl
    (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) r.length (tri n) v₄ S₄ (by simp (disch := decide) only [hS₄, hC₃, Nat.zero_add])
    (by rw [hM₄, Nat.zero_add]) (by simp (disch := decide) only [hS₄, hS₃, hS₂, hS₁, h0])
    (by simp (disch := decide) only [hS₄, hS₃, hS₂, hS₁, h0])
  have hO₄ : S₄ .O = [] := by simp (disch := decide) only [hS₄, hS₃, hS₂, hS₁, h0]
  have hmin := min_le_left r.length (tri n)
  by_cases heq : r.length = tri n
  swap
  · rw [cmpOut_ne heq] at h₅
    have h₆ := bad_run (Flag.tag false) S₄
    refine ⟨_, _, (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).le
      (hN _ ?_), ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons, heq, ↓reduceIte]
      nlinarith
    · rw [update_self, hO₄]
      simp [reduceSS, decodeKG, length_pairs_eq_tri, heq]
  rw [heq, Nat.compare_eq_eq.2 rfl] at h₅
  have hb : r.length = (pairs n).length := by rw [length_pairs_eq_tri, heq]
  obtain ⟨v₅, S₅, h₅', hY₅, hZ₅, hO₅, hS₅⟩ := eg_run r.reverse (Flag.tag false) S₄
    (by simp (disch := decide) only [hS₄, hY₃, hS₂, hS₁, h0]; simp)
    (by simp (disch := decide) only [hS₄, hC₃]; simp)
    (by rw [hM₄]; simp [heq])
    (by simp (disch := decide) only [hS₄, hS₃, hS₂, hS₁, h0])
  obtain ⟨v₆, S₆, h₆, hZ₆, hY₆, hS₆⟩ := moveB_run (M := prog) (self := .egY) rfl (by decide)
    r (r.map Sym.val) [] v₅ S₅ (by simp (disch := decide) only [hZ₅, hS₄, hS₃, hS₂, hS₁, h0]; simp)
    (isBitBlock_val r) rfl
  have hvert : ∃ v' S', RunLe prog (n * (3 * r.length + 4 * n + 4) + 1) ⟨some .vinit, v₆, S₆⟩
      ⟨some .hv, v', S'⟩ ∧
      S' .O = ((List.range n).map (vtxNum n r)).flatMap (fun a => delimit (encodeNat a)) ++
        S₆ .O ∧
      ∀ j, j ≠ .L → j ≠ .R → j ≠ .Rt → j ≠ .Y → j ≠ .Z → j ≠ .O → S' j = S₆ j := by
    have hL₆ : S₆ .L = cnt (.val false) n := by
      simp (disch := decide) only [hS₆, hS₅, hS₄, hS₃, hL₂, Nat.zero_add]
    rcases n with _ | w
    · exact ⟨_, _, (vinit_nil v₆ S₆ hL₆).le (by omega), by simp, fun _ _ _ _ _ _ _ => rfl⟩
    · have h₇ := vinit_cons v₆ S₆ (cnt (.val false) w) hL₆
      obtain ⟨v₈, S₈, h₈, hO₈, hS₈⟩ := vtx_run (w + 1) r hb w (by omega) true
        (update S₆ .L (.val true :: cnt (.val false) w)) (by simp [mkL_top])
        (by simp (disch := decide) only [update_of_ne, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, h0])
        (by simp (disch := decide) only [update_of_ne, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, h0])
        (by simp (disch := decide) only [update_of_ne, hY₆, hY₅]; simp)
        (by simp (disch := decide) only [update_of_ne, hZ₆])
      refine ⟨v₈, S₈, ((h₇.le le_rfl).trans h₈).mono (by rw [← hb]; nlinarith),
        by simp [hO₈], fun j h1 h2 h3 h4 h5 h6 => ?_⟩
      rw [hS₈ j h1 h2 h3 h4 h5 h6, update_of_ne h1]
  obtain ⟨v₇, S₇, h₇, hO₇, hS₇⟩ := hvert
  obtain ⟨v₈, S₈, h₈, hT₈, hS₈⟩ := hv_run k v₇ S₇
    (by simp (disch := decide) only [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hA₁, Nat.zero_add])
    (by simp (disch := decide) only [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, h0])
  have h₉ := emit_run (M := prog) (self := .tem0) rfl v₈ S₈
  obtain ⟨v₁₀, S₁₀, h₁₀, hO₁₀, -⟩ :=
    tsk_run (r.flatMap (fun b => [false, b]) ++ encodeNat k).reverse v₈
    (update S₈ .O ([false].reverse ++ S₈ .O)) (S₈ .O)
    (by
      rw [update_of_ne (by decide), hT₈]
      simp (disch := decide) only [hS₇, hS₆, hS₅, hS₄, hT₃, hS₂, hS₁, h0]
      simp)
    (by simp)
  have hlen := encodeNat_length_le k
  have hrun := ((((((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).le le_rfl).trans h₅').trans
    (h₆.le le_rfl)).trans h₇).trans h₈).trans ((h₉.trans h₁₀).le le_rfl))
  refine ⟨v₁₀, S₁₀, hrun.mono (hN _ ?_), ?_⟩
  · simp only [List.length_append, List.length_replicate, List.length_cons, List.length_reverse,
      length_flatMap2 _ (fun _ => rfl : ∀ b : Bool, [false, b].length = 2), ← heq, ↓reduceIte,
      min_self]
    nlinarith
  · rw [hO₁₀, hS₈ _ (by decide) (by decide) (by decide), hO₇, hS₆ _ (by decide) (by decide), hO₅,
      hO₄, List.append_nil]
    have hred : reduceSS (List.replicate k true ++ false :: (List.replicate n true ++ false :: r)) =
        encodeSS (ssNums n r) (ssTarget k n r) := by simp [reduceSS, decodeKG, hb]
    rw [hred, encodeSS, ssTarget_eq_bitsVal k n r hb, encodeNat_bitsVal_rev, ssNums,
      List.flatMap_append,
      List.flatMap_map, List.flatMap_map, edgeOut_reverse, ← hb]
    simp only [edgeEnc_eq]

end Cslib.Complexity.Karp.EmitSS
