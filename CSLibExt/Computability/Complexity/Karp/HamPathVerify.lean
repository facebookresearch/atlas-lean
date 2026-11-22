/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathCheck
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps

/-!
# The NP verifier for HAMPATH: the machine

`prog` is a `TM2` component on thirteen stacks over the alphabet `Sym` (bits as `Sym.bit`) that
decides `hamCheck x w` (`CSLibExt.Computability.Complexity.Karp.HamPathCheck`) with `x` on `X`
and `w` on `W`.

* Parse: read `s`, `t`, `n` in unary off `X` onto the counters `S`, `T`, `N` (`readU`); check
  that the rest of `X` is an edge list by moving it to `E` one unary number at a time (`skipU`,
  `valE_run`) and put it back (`moveB`); check that `w` is a list of unary numbers the same way
  (`valW_run`), through `Z`.
* Walk the vertices (`loop_run`): read the next vertex `a` onto `A`; compare it with `n`
  (`cmp_run`); if no vertex was seen yet (`C` empty) compare it with `s`, otherwise scan the
  edge list for the pair `(b, a)`, `b` the previous vertex on `B` (`scan_run`: each edge's ends
  are compared with `B` and `A` while its bits move to `E`, `cmpN_run`); compare `a` with every
  later vertex (`nd_run`, through `Z`); count `a` on `C` and make it the previous vertex. With
  no vertex left, `C` must equal `n` and be nonzero, and `B` must equal `t`.
* `run`: from `start`, `prog` reaches `yes` iff `hamCheck x w` and `no` otherwise, within
  `100 (|x| + |w| + 1)⁴` steps (quadratically many, in fact). The machine's order of checks is
  `walkOk`, which `walkOk_eq` identifies with the check.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.HamVerify

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin
open Cslib.Complexity.SatVerifier (Sym)

/-! ### The machine -/

/-- **Stacks of the Hamiltonian path verifier.** The verifier has twelve stacks: the input $X$
and the witness $W$; the counters $S$, $T$, $N$ (holding $s$, $t$, $n$), $C$ (the number of
vertices seen), $A$ (the current vertex) and $B$ (the previous one); the save stacks $E$ (for
$X$) and $Z$ (for $W$); and the scratch stacks $R$ and $Q$. -/
inductive K | X | W | S | T | N | C | A | B | E | Z | R | Q
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .S, .T, .N, .C, .A, .B, .E, .Z, .R, .Q], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Counter comparisons of the HAMPATH verifier.** The four-element type of the comparisons the
verifier makes between its counters: the current vertex $a$ with the vertex count $n$, the
current vertex $a$ with the start vertex $s$, the number $c$ of vertices seen with $n$, and the
previous vertex $b$ with the end vertex $t$. -/
inductive CI | an | as | cn | bt
  deriving DecidableEq

/-- `CI` is finite. -/
instance CI.instFintypeEnumFix : Fintype CI where
  elems := ⟨↑[CI.an, .as, .cn, .bt], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the Hamiltonian path verifier.** The instruction labels of the verifier: reading
$s$, $t$, $n$; validating the edge list and putting it back; validating the witness and putting
it back; the vertex loop, reading a vertex, and the head-or-edge dispatch; for each of the four
counter comparisons, the comparison itself and, for each of its three outcomes, the two loops
restoring the compared counters; the edge scan (comparing an edge's ends, with a flag for the
verdict so far, restoring the counters, putting the edge list back); the repeat scan (likewise
flagged comparisons and restores, then putting the witness back); the final nonzero-count
check; counting the vertex and making it the previous one; accept; and reject. -/
inductive Lab
  | rdS | rdT | rdN | vE | vEU | vEV | vEb | vW | vWU | vWb | loop | rdA | hd
  | cmp (i : CI) | cr (i : CI) (o : Ordering) | crb (i : CI) (o : Ordering)
  | scan | ceU (ok : Bool) | rsU (ok : Bool) | ceV (ok : Bool) | rsV (ok : Bool) | scB
  | nd | cbN (ok : Bool) | rsN (ok : Bool) | ndB | fin | incC | dB | mA | yes | no
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdS, .rdT, .rdN, .vE, .vEU, .vEV, .vEb, .vW, .vWU, .vWb, .loop, .rdA, .hd,
    .cmp .an, .cmp .as, .cmp .cn, .cmp .bt,
    .cr .an .lt, .cr .an .eq, .cr .an .gt, .cr .as .lt, .cr .as .eq, .cr .as .gt,
    .cr .cn .lt, .cr .cn .eq, .cr .cn .gt, .cr .bt .lt, .cr .bt .eq, .cr .bt .gt,
    .crb .an .lt, .crb .an .eq, .crb .an .gt, .crb .as .lt, .crb .as .eq, .crb .as .gt,
    .crb .cn .lt, .crb .cn .eq, .crb .cn .gt, .crb .bt .lt, .crb .bt .eq, .crb .bt .gt,
    .scan, .ceU false, .ceU true, .rsU false, .rsU true, .ceV false, .ceV true,
    .rsV false, .rsV true, .scB, .nd, .cbN false, .cbN true, .rsN false, .rsN true, .ndB,
    .fin, .incC, .dB, .mA, .yes, .no], by decide⟩
  complete := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _⟩ |
      ⟨_ | _ | _ | _, _ | _ | _⟩ | ⟨_ | _ | _ | _, _ | _ | _⟩ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ |
      ⟨_ | _⟩ | ⟨_ | _⟩ | _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _) <;> decide

/-- **Statements of the Hamiltonian-path verifier.** A statement of the verifier is a statement of
a multi-stack Turing machine whose stacks are indexed by the verifier's stacks $K$, each stack
over the alphabet $\mathrm{Sym}$, with labels $\mathrm{Lab}$ and a Boolean internal variable. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- **The unary reader of the Hamiltonian path verifier.** For stacks $\mathsf{src}$ and $c$ and
labels $\ell$ (its own) and $m$ (the next one), the statement that goes to label $\mathrm{no}$
if $\mathsf{src}$ is empty; otherwise it pops the top symbol of $\mathsf{src}$ and, if that
symbol is the bit `true`, pushes the bit `true` (one unit) onto $c$ and goes to $\ell$, while
if it is anything else it goes to $m$. Each of the two tests also stores its outcome in the
Boolean variable.

Run in a loop at $\ell$, it reads a unary number off $\mathsf{src}$ onto the counter $c$ and
consumes the terminator. -/
def readU (src c : K) (self next : Lab) : Stmt :=
  .peek src (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop src (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.push c (fun _ => .bit true) (.goto fun _ => self)) (.goto fun _ => next)

/-- **The unary mover of the Hamiltonian path verifier.** For stacks $\mathsf{src}$ and
$\mathsf{dst}$ and labels $\ell$ (its own) and $m$ (the next one), the statement that goes to
label $\mathrm{no}$ if $\mathsf{src}$ is empty; otherwise it pops the top symbol of
$\mathsf{src}$, reads it as the bit `true` if it is the bit `true` and as `false` otherwise,
pushes that bit onto $\mathsf{dst}$, and goes to $\ell$ if the bit is `true` and to $m$ if it
is `false`. Each of the two tests also stores its outcome in the Boolean variable.

Run in a loop at $\ell$, it moves a unary number, terminator included, from $\mathsf{src}$ to
$\mathsf{dst}$. -/
def skipU (src dst : K) (self next : Lab) : Stmt :=
  .peek src (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop src (fun _ o => bitOf Sym.bit? o) <| .push dst (fun b => .bit b) <| .branch id
      (.goto fun _ => self) (.goto fun _ => next)

/-- **Emptiness test.** For a stack $k$ and labels $e$ and $ne$, the verifier instruction that
looks at the top of stack $k$ without changing any stack, then goes to $e$ if $k$ is empty and
to $ne$ otherwise. -/
def ifE (k : K) (e ne : Lab) : Stmt :=
  .peek k (fun _ o => o.isNone) <| .branch id (.goto fun _ => e) (.goto fun _ => ne)

/-- **Step of the HAMPATH verifier's unary comparison loop.** For stacks $\mathit{src}$,
$\mathit{sv}$, $c$ of the HAMPATH verifier, label families $\mathit{self}$ and $\mathit{fin}$
indexed by booleans, and a boolean verdict $\mathit{ok}$, this is the instruction that pops the top
of $\mathit{src}$, reads it as a bit $b$ (false if $\mathit{src}$ is empty or its top is not a bit
symbol), and pushes the bit symbol of $b$ onto $\mathit{sv}$. If $b$ is true, it pops $c$; if $c$
was nonempty it pushes the bit symbol of true onto the scratch stack $R$ and goes to
$\mathit{self}(\mathit{ok})$, and otherwise it goes to $\mathit{self}(\mathrm{false})$. If $b$ is
false, it goes to $\mathit{fin}(\mathit{ok})$ when $c$ is empty and to
$\mathit{fin}(\mathrm{false})$ otherwise.

Iterated, it compares the next unary number of $\mathit{src}$ with the counter $c$, one unit of $c$
per true, parked on $R$: $\mathit{ok}$ is the verdict so far, falsified when $c$ runs out early. -/
def cbS (src sv c : K) (self fin : Bool → Lab) (ok : Bool) : Stmt :=
  .pop src (fun _ o => bitOf Sym.bit? o) <| .push sv (fun b => .bit b) <| .branch id
    (.pop c (fun _ o => o.isSome) <| .branch id
      (.push .R (fun _ => .bit true) (.goto fun _ => self ok)) (.goto fun _ => self false))
    (.peek c (fun _ o => o.isNone) <| .branch id (.goto fun _ => fin ok)
      (.goto fun _ => fin false))

/-- **First counter of a HAMPATH-verifier comparison.** The function from the four counter
comparisons of the HAMPATH verifier to its stacks that sends the comparisons of the current
vertex with the vertex count and of the current vertex with the start vertex to the
current-vertex counter $A$, the comparison of the number of vertices seen with the vertex count
to the vertices-seen counter $C$, and the comparison of the previous vertex with the end vertex
to the previous-vertex counter $B$. -/
def ca : CI → K
  | .an => .A
  | .as => .A
  | .cn => .C
  | .bt => .B

/-- **Second counter of a HAMPATH-verifier comparison.** The function from the four counter
comparisons of the HAMPATH verifier to its stacks that sends the comparisons of the current
vertex with the vertex count and of the number of vertices seen with the vertex count to the
vertex-count counter $N$, the comparison of the current vertex with the start vertex to the
start-vertex counter $S$, and the comparison of the previous vertex with the end vertex to the
end-vertex counter $T$. -/
def cb : CI → K
  | .an => .N
  | .as => .S
  | .cn => .N
  | .bt => .T

/-- **Exit labels of the counter comparisons.** The label the verifier goes to after comparing
two counters, where $a$ is the current vertex, $b$ the previous one, $c$ the number of vertices
seen, $n$ the number of vertices and $s$, $t$ the two ends: after comparing $a$ with $n$ it goes
to the head-or-edge dispatch if $a < n$; after comparing $a$ with $s$ it goes to the repeat scan
if $a = s$; after comparing $c$ with $n$ it goes to the nonzero-count check if $c = n$; after
comparing $b$ with $t$ it goes to the accept label if $b = t$; in every other case it goes to
the reject label. -/
def cout : CI → Ordering → Lab
  | .an, .lt => .hd
  | .as, .eq => .nd
  | .cn, .eq => .fin
  | .bt, .eq => .yes
  | _, _ => .no

/-- **The Hamiltonian path verifier machine.** The verifier is the program of the multi-stack
machine with the stacks and labels of the Hamiltonian path verifier, every stack over the
alphabet $\mathrm{Sym}$, and a Boolean internal variable, given below label by label. Write
$\mathrm{bit}(x)$ for the bit symbol of a boolean $x$. Write $(a, n)$, $(a, s)$, $(c, n)$ and
$(b, t)$ for the four counter comparisons, and $\alpha(i)$ and $\beta(i)$ for the first and the
second counter of comparison $i$. Every unary reader, unary mover, bit-moving loop and transfer
below has the label it sits at as its own label; the bit-moving loops read bit symbols as bits
and every other symbol as a marker, and push $\mathrm{bit}(x)$ for a bit $x$. The transfer from a
stack $k$ onto a list of stacks with next label $m$ pops $k$; if it popped a symbol, it pushes
$\mathrm{bit}(\mathrm{true})$ onto each listed stack and returns to its own label, and otherwise
it goes to $m$. An emptiness test of a stack "to $e$, else $e'$" goes to $e$ if the stack is
empty and to $e'$ otherwise. A transfer also stores in the Boolean variable whether its pop
found a symbol, and an emptiness test stores there whether the stack is empty.

- $\mathsf{rdS}$, $\mathsf{rdT}$, $\mathsf{rdN}$: the unary reader from $X$ onto $S$, $T$, $N$
  respectively, with next labels $\mathsf{rdT}$, $\mathsf{rdN}$, $\mathsf{vE}$ respectively.
- $\mathsf{vE}$: the emptiness test of $X$ to $\mathsf{vEb}$, else $\mathsf{vEU}$. $\mathsf{vEU}$
  and $\mathsf{vEV}$: the unary mover from $X$ to $E$, with next labels $\mathsf{vEV}$ and
  $\mathsf{vE}$ respectively. $\mathsf{vEb}$: the bit-moving loop from $E$ to $X$ with next label
  $\mathsf{vW}$.
- $\mathsf{vW}$: the emptiness test of $W$ to $\mathsf{vWb}$, else $\mathsf{vWU}$. $\mathsf{vWU}$:
  the unary mover from $W$ to $Z$ with next label $\mathsf{vW}$. $\mathsf{vWb}$: the bit-moving
  loop from $Z$ to $W$ with next label $\mathsf{loop}$.
- $\mathsf{loop}$: the emptiness test of $W$ to $\mathsf{cmp}(c, n)$, else $\mathsf{rdA}$.
  $\mathsf{rdA}$: the unary reader from $W$ onto $A$ with next label $\mathsf{cmp}(a, n)$.
  $\mathsf{hd}$: the emptiness test of $C$ to $\mathsf{cmp}(a, s)$, else $\mathsf{scan}$.
- For each comparison $i$, $\mathsf{cmp}(i)$ is one round of counter comparison of $\alpha(i)$
  and $\beta(i)$, with scratch stacks $R$ (for $\alpha(i)$) and $Q$ (for $\beta(i)$), both units
  $\mathrm{bit}(\mathrm{true})$, own label $\mathsf{cmp}(i)$, and $\mathsf{cr}(i, <)$,
  $\mathsf{cr}(i, =)$, $\mathsf{cr}(i, >)$ as its labels $\mathit{lt}$, $\mathit{eq}$ and
  $\mathit{gt}$. For each ordering $o$, $\mathsf{cr}(i, o)$ is the transfer from $R$ onto
  $\alpha(i)$ with next label $\mathsf{crb}(i, o)$, and $\mathsf{crb}(i, o)$ is the transfer from
  $Q$ onto $\beta(i)$ whose next label is the exit label of the counter comparison $i$ with
  outcome $o$.
- $\mathsf{scan}$: the emptiness test of $X$ to $\mathsf{no}$, else
  $\mathsf{ceU}(\mathrm{true})$. For each boolean $\mathit{ok}$: $\mathsf{ceU}(\mathit{ok})$ is
  the step of the unary comparison loop with source $X$, save stack $E$, counter $B$, label
  families $\mathsf{ceU}$ and $\mathsf{rsU}$, and verdict $\mathit{ok}$; $\mathsf{rsU}(\mathit{ok})$
  is the transfer from $R$ onto $B$ with next label $\mathsf{ceV}(\mathit{ok})$;
  $\mathsf{ceV}(\mathit{ok})$ is the step of the unary comparison loop with source $X$, save stack
  $E$, counter $A$, label families $\mathsf{ceV}$ and $\mathsf{rsV}$, and verdict $\mathit{ok}$;
  and $\mathsf{rsV}(\mathit{ok})$ is the transfer from $R$ onto $A$ with next label $\mathsf{scB}$
  if $\mathit{ok}$ is true and $\mathsf{scan}$ otherwise. $\mathsf{scB}$: the bit-moving loop from
  $E$ to $X$ with next label $\mathsf{nd}$.
- $\mathsf{nd}$: the emptiness test of $W$ to $\mathsf{ndB}$, else $\mathsf{cbN}(\mathrm{true})$.
  For each boolean $\mathit{ok}$: $\mathsf{cbN}(\mathit{ok})$ is the step of the unary comparison
  loop with source $W$, save stack $Z$, counter $A$, label families $\mathsf{cbN}$ and
  $\mathsf{rsN}$, and verdict $\mathit{ok}$; and $\mathsf{rsN}(\mathit{ok})$ is the transfer from
  $R$ onto $A$ with next label $\mathsf{no}$ if $\mathit{ok}$ is true and $\mathsf{nd}$
  otherwise. $\mathsf{ndB}$: the bit-moving loop from $Z$ to $W$ with next label $\mathsf{incC}$.
- $\mathsf{fin}$: the emptiness test of $C$ to $\mathsf{no}$, else $\mathsf{cmp}(b, t)$.
  $\mathsf{incC}$: the counter increment pushing $\mathrm{bit}(\mathrm{true})$ onto $C$ and going
  to $\mathsf{dB}$. $\mathsf{dB}$: the transfer from $B$ onto no stack (it drains $B$) with next
  label $\mathsf{mA}$. $\mathsf{mA}$: the transfer from $A$ onto $B$ with next label
  $\mathsf{loop}$.
- $\mathsf{yes}$ and $\mathsf{no}$: halt.

The verifier parses and validates the input and the witness, then walks the vertices. -/
def prog : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .rdS => readU .X .S .rdS .rdT
  | .rdT => readU .X .T .rdT .rdN
  | .rdN => readU .X .N .rdN .vE
  | .vE => ifE .X .vEb .vEU
  | .vEU => skipU .X .E .vEU .vEV
  | .vEV => skipU .X .E .vEV .vE
  | .vEb => moveB .E .X Sym.bit? Sym.bit .vEb .vW
  | .vW => ifE .W .vWb .vWU
  | .vWU => skipU .W .Z .vWU .vW
  | .vWb => moveB .Z .W Sym.bit? Sym.bit .vWb .loop
  | .loop => ifE .W (.cmp .cn) .rdA
  | .rdA => readU .W .A .rdA (.cmp .an)
  | .hd => ifE .C (.cmp .as) .scan
  | .cmp i => cmpStep (ca i) (cb i) .R .Q (Sym.bit true) (Sym.bit true) (.cmp i) (.cr i .lt)
      (.cr i .eq) (.cr i .gt)
  | .cr i o => xfer .R [⟨ca i, Sym.bit true⟩] (.cr i o) (.crb i o)
  | .crb i o => xfer .Q [⟨cb i, Sym.bit true⟩] (.crb i o) (cout i o)
  | .scan => ifE .X .no (.ceU true)
  | .ceU ok => cbS .X .E .B .ceU .rsU ok
  | .rsU ok => xfer .R [⟨.B, Sym.bit true⟩] (.rsU ok) (.ceV ok)
  | .ceV ok => cbS .X .E .A .ceV .rsV ok
  | .rsV ok => xfer .R [⟨.A, Sym.bit true⟩] (.rsV ok) (if ok then .scB else .scan)
  | .scB => moveB .E .X Sym.bit? Sym.bit .scB .nd
  | .nd => ifE .W .ndB (.cbN true)
  | .cbN ok => cbS .W .Z .A .cbN .rsN ok
  | .rsN ok => xfer .R [⟨.A, Sym.bit true⟩] (.rsN ok) (if ok then .no else .nd)
  | .ndB => moveB .Z .W Sym.bit? Sym.bit .ndB .incC
  | .fin => ifE .C .no (.cmp .bt)
  | .incC => incr .C (Sym.bit true) .dB
  | .dB => xfer .B [] .dB .mA
  | .mA => xfer .A [⟨.B, Sym.bit true⟩] .mA .loop
  | .yes => .halt
  | .no => .halt

/-- **Start label of the Hamiltonian-path verifier.** The verifier starts at the label
$\mathsf{rdS}$, where it reads the first unary number of the input stack $X$ (the start vertex
$s$) onto the counter stack $S$. -/
def start : Lab := .rdS

/-! ### Generic phases -/

/-- **Interleaved stack updates in the Hamiltonian-path verifier.** Let $a \ne b$ be two stacks of
the verifier, $S$ an assignment of a list of symbols to each stack, and $p, p', t, t'$ lists of
symbols. Setting $a$ to $p$, then $b$ to $t$, then $a$ to $p'$, then $b$ to $t'$ in $S$ gives the
same assignment as setting $a$ to $p'$ and then $b$ to $t'$. -/
theorem update_update_update_update {a b : K} (hab : a ≠ b) (S : ∀ _ : K, List Sym)
    (p p' t t' : List Sym) :
    update (update (update (update S a p) b t) a p') b t' = update (update S a p') b t' := by
  rw [update_comm hab.symm, update_idem, update_idem]

/-- **A single step of the Hamiltonian-path verifier.** Let $l, l'$ be labels, $v$ a flag value
and $S, S'$ assignments of a list of symbols to each stack. If executing the verifier's statement
at $l$ with flag $v$ and stacks $S$ jumps to the label $l'$ and leaves the stacks $S'$, then the
verifier goes in exactly one step from label $l$, flag $v$ and stacks $S$ to label $l'$ and
stacks $S'$, with some flag value. -/
theorem step1 {l l' : Lab} {v : Bool} {S S' : ∀ _ : K, List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some l') (h' : (TM2.stepAux (prog l) v S).stk = S') :
    ∃ v', Run prog 1 ⟨some l, v, S⟩ ⟨some l', v', S'⟩ :=
  ⟨_, Run.single (d := ⟨some l', (TM2.stepAux (prog l) v S).var, S'⟩) (by rw [← h, ← h'])⟩

/-- **One step of the emptiness test.** If the verifier's instruction at label $l$ is the
emptiness test of stack $k$ with targets $e$ and $ne$, then from label $l$, in any internal state
and on any stacks, exactly one step of the verifier leads to label $e$ if stack $k$ is empty and
to label $ne$ otherwise, in some internal state and with the stacks unchanged. -/
theorem ifE_run {l e ne : Lab} {k : K} (hp : prog l = ifE k e ne) (v : Bool)
    (St : ∀ _ : K, List Sym) :
    ∃ v', Run prog 1 ⟨some l, v, St⟩ ⟨some (if St k = [] then e else ne), v', St⟩ :=
  step1 (by cases h : St k <;> simp [hp, ifE, TM2.stepAux, h])
    (by cases h : St k <;> simp [hp, ifE, TM2.stepAux, h])

/-- **The unary reader of the Hamiltonian path verifier reads a terminated number.** Let
$\mathsf{src} \ne c$ be stacks and $\ell$, $m$ labels such that the verifier's statement at
$\ell$ is the unary reader from $\mathsf{src}$ onto $c$ with own label $\ell$ and next label
$m$. Let $k, j$ be natural numbers and $r$ a bit list, and suppose that $\mathsf{src}$ holds
$k$ copies of `true`, then `false`, then $r$ (as bit symbols, first bit on top) and that $c$
holds $j$ copies of the bit `true`. Then from label $\ell$, with either value of the Boolean
variable, the verifier reaches label $m$ in exactly $k + 1$ steps, with $\mathsf{src}$ holding
the bits of $r$, $c$ holding $k + j$ copies of the bit `true`, and every other stack
unchanged. -/
theorem readU_run {src c : K} {self next : Lab} (hp : prog self = readU src c self next)
    (hc : c ≠ src) : ∀ (k j : ℕ) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St src = (List.replicate k true ++ false :: r).map Sym.bit → St c = cnt (Sym.bit true) j →
      ∃ v', Run prog (k + 1) ⟨some self, v, St⟩ ⟨some next, v',
        update (update St src (r.map Sym.bit)) c (cnt (Sym.bit true) (k + j))⟩ := by
  intro k
  induction k with
  | zero =>
      intro j r v St hX hC
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hX
      have e : update (update St src (r.map Sym.bit)) c (cnt (Sym.bit true) (0 + j)) =
          update St src (r.map Sym.bit) := by
        rw [zero_add, ← hC, ← update_of_ne hc (r.map Sym.bit) St, update_eq_self]
      rw [e]
      exact step1 (by simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?])
        (by simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?])
  | succ k ih =>
      intro j r v St hX hC
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hX
      obtain ⟨v', hrun⟩ := ih (j + 1) r true
        (update (update St src ((List.replicate k true ++ false :: r).map Sym.bit)) c
          (Sym.bit true :: St c)) (by simp [update_of_ne hc.symm]) (by simp [hC, cnt_succ])
      rw [update_update_update_update hc.symm, show k + (j + 1) = k + 1 + j by omega] at hrun
      exact ⟨v', Run.head (by simp [TM2.step, hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?,
        update_of_ne hc]) hrun⟩

/-- **The unary reader of the Hamiltonian path verifier rejects an unterminated number.** Let
$\mathsf{src} \ne c$ be stacks and $\ell$, $m$ labels such that the verifier's statement at
$\ell$ is the unary reader from $\mathsf{src}$ onto $c$ with own label $\ell$ and next label
$m$. Let $l$ be a bit list from which no unary length can be read (that is, $l$ contains no
`false`), and suppose that $\mathsf{src}$ holds the bits of $l$ (as bit symbols, first bit on
top). Then from label $\ell$, with either value of the Boolean variable and any contents of the
other stacks, the verifier reaches label $\mathrm{no}$ within $|l| + 1$ steps. -/
theorem readU_none {src c : K} {self next : Lab} (hp : prog self = readU src c self next)
    (hc : c ≠ src) : ∀ (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      readUnaryLength l = none → St src = l.map Sym.bit →
      ∃ v' S', RunLe prog (l.length + 1) ⟨some self, v, St⟩ ⟨some .no, v', S'⟩ := by
  intro l
  induction l with
  | nil =>
      intro v St _ hX
      obtain ⟨v', h⟩ := step1 (l := self) (v := v) (S := St) (l' := .no) (S' := St)
        (by simp [hp, readU, TM2.stepAux, hX]) (by simp [hp, readU, TM2.stepAux, hX])
      exact ⟨v', St, h.le (by simp)⟩
  | cons b l ih =>
      intro v St hl hX
      cases b with
      | false => simp [readUnaryLength] at hl
      | true =>
          have hl' : readUnaryLength l = none := by simpa [readUnaryLength] using hl
          obtain ⟨v', S', h⟩ := ih true
            (update (update St src (l.map Sym.bit)) c (Sym.bit true :: St c)) hl'
            (by simp [update_of_ne hc.symm])
          refine ⟨v', S', (((Run.single ?_).le le_rfl).trans h).mono (by simp; omega)⟩
          simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hc]

/-- **Extending a reversed unary block.** For $a \in \mathbb{N}$, let $\beta_a$ be the list of
symbols obtained by mapping the bit symbol over the reversal of the unary block of $a$ ($a$ copies
of true followed by one false), that is, the bit symbol of false followed by $a$ bit symbols of
true. Then for every list $L$ of symbols, $\beta_a$ followed by the bit symbol of true and then
$L$ equals $\beta_{a+1}$ followed by $L$. -/
theorem blk_succ (a : ℕ) (L : List Sym) :
    (List.replicate a true ++ [false]).reverse.map Sym.bit ++ Sym.bit true :: L =
      (List.replicate (a + 1) true ++ [false]).reverse.map Sym.bit ++ L := by
  have e : ∀ (n : ℕ) (x : Sym) (L : List Sym),
      List.replicate n x ++ x :: L = x :: (List.replicate n x ++ L) := by
    intro n x L
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  simp [e, List.replicate_succ]

/-- **The unary mover of the Hamiltonian path verifier moves a terminated number.** Let
$\mathsf{src} \ne \mathsf{dst}$ be stacks and $\ell$, $m$ labels such that the verifier's
statement at $\ell$ is the unary mover from $\mathsf{src}$ to $\mathsf{dst}$ with own label
$\ell$ and next label $m$. Let $k$ be a natural number and $r$ a bit list, and suppose that
$\mathsf{src}$ holds $k$ copies of `true`, then `false`, then $r$ (as bit symbols, first bit on
top). Then from label $\ell$, with either value of the Boolean variable, the verifier reaches
label $m$ in exactly $k + 1$ steps, with $\mathsf{src}$ holding the bits of $r$, with
$\mathsf{dst}$ holding the bit `false` followed by $k$ copies of the bit `true` on top of its
previous contents, and with every other stack unchanged. -/
theorem skipU_run {src dst : K} {self next : Lab} (hp : prog self = skipU src dst self next)
    (hd : dst ≠ src) : ∀ (k : ℕ) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St src = (List.replicate k true ++ false :: r).map Sym.bit →
      ∃ v', Run prog (k + 1) ⟨some self, v, St⟩ ⟨some next, v',
        update (update St src (r.map Sym.bit)) dst
          ((List.replicate k true ++ [false]).reverse.map Sym.bit ++ St dst)⟩ := by
  intro k
  induction k with
  | zero =>
      intro r v St hX
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hX
      exact step1 (by simp [hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?])
        (by simp [hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hd])
  | succ k ih =>
      intro r v St hX
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hX
      obtain ⟨v', hrun⟩ := ih r true
        (update (update St src ((List.replicate k true ++ false :: r).map Sym.bit)) dst
          (Sym.bit true :: St dst)) (by simp [update_of_ne hd.symm])
      rw [update_update_update_update hd.symm, update_self, blk_succ] at hrun
      exact ⟨v', Run.head (by simp [TM2.step, hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?,
        update_of_ne hd]) hrun⟩

/-- **The unary mover of the Hamiltonian path verifier rejects an unterminated number.** Let
$\mathsf{src} \ne \mathsf{dst}$ be stacks and $\ell$, $m$ labels such that the verifier's
statement at $\ell$ is the unary mover from $\mathsf{src}$ to $\mathsf{dst}$ with own label
$\ell$ and next label $m$. Let $l$ be a bit list from which no unary length can be read (that
is, $l$ contains no `false`), and suppose that $\mathsf{src}$ holds the bits of $l$ (as bit
symbols, first bit on top). Then from label $\ell$, with either value of the Boolean variable
and any contents of the other stacks, the verifier reaches label $\mathrm{no}$ within
$|l| + 1$ steps. -/
theorem skipU_none {src dst : K} {self next : Lab} (hp : prog self = skipU src dst self next)
    (hd : dst ≠ src) : ∀ (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      readUnaryLength l = none → St src = l.map Sym.bit →
      ∃ v' S', RunLe prog (l.length + 1) ⟨some self, v, St⟩ ⟨some .no, v', S'⟩ := by
  intro l
  induction l with
  | nil =>
      intro v St _ hX
      obtain ⟨v', h⟩ := step1 (l := self) (v := v) (S := St) (l' := .no) (S' := St)
        (by simp [hp, skipU, TM2.stepAux, hX]) (by simp [hp, skipU, TM2.stepAux, hX])
      exact ⟨v', St, h.le (by simp)⟩
  | cons b l ih =>
      intro v St hl hX
      cases b with
      | false => simp [readUnaryLength] at hl
      | true =>
          have hl' : readUnaryLength l = none := by simpa [readUnaryLength] using hl
          obtain ⟨v', S', h⟩ := ih true
            (update (update St src (l.map Sym.bit)) dst (Sym.bit true :: St dst)) hl'
            (by simp [update_of_ne hd.symm])
          refine ⟨v', S', (((Run.single ?_).le le_rfl).trans h).mono (by simp; omega)⟩
          simp [hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hd]

/-- **Moving a stack of bits.** Suppose the verifier's instruction at label $p$ is the bit-moving
loop from a stack $a$ to a different stack $b$, continuing at label $p'$ when done. If stack $a$
holds exactly the bits of a list $l$, then from label $p$ in any internal state the verifier
takes exactly $|l| + 1$ steps to reach label $p'$, in some internal state, with stack $a$ empty,
stack $b$ holding the bits of $l$ in reverse order followed by its old contents, and every other
stack unchanged. -/
theorem mv_run {self next : Lab} {a b : K} (hp : prog self = moveB a b Sym.bit? Sym.bit self next)
    (hab : a ≠ b) (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (ha : St a = l.map Sym.bit) :
    ∃ v', Run prog (l.length + 1) ⟨some self, v, St⟩
      ⟨some next, v', update (update St a []) b ((l.map Sym.bit).reverse ++ St b)⟩ := by
  obtain ⟨v', S', h, ha', hb', hk'⟩ := moveB_run hp hab l (l.map Sym.bit) [] v St (by simp [ha])
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
  refine ⟨v', ?_⟩
  have e : S' = update (update St a []) b ((l.map Sym.bit).reverse ++ St b) := by
    funext k
    by_cases h1 : k = b
    · subst h1; simpa using hb'
    · by_cases h2 : k = a
      · subst h2; simp [ha', update_of_ne h1]
      · simp [update_of_ne h1, update_of_ne h2, hk' k h2 h1]
  exact e ▸ h

/-- **Run of a HAMPATH-verifier counter comparison.** Let $i$ be one of the four counter
comparisons of the HAMPATH verifier, with first counter $\mathrm{ca}(i)$ and second counter
$\mathrm{cb}(i)$, and let $m, n \in \mathbb{N}$. Suppose the stacks $\sigma$ hold $m$ units (bit
symbols of true) on $\mathrm{ca}(i)$, $n$ units on $\mathrm{cb}(i)$, and nothing on the scratch
stacks $R$ and $Q$. Then for every flag $v$ the verifier goes, in at most
$3 \min(m, n) + 4$ steps, from label $\mathrm{cmp}(i)$ with flag $v$ and stacks $\sigma$ to the
label $\mathrm{cout}(i, o)$ that comparison $i$ picks on the ordering
$o = \mathrm{compare}(m, n) \in \{\mathrm{lt}, \mathrm{eq}, \mathrm{gt}\}$ of $m$ and $n$, with flag
false and the same stacks $\sigma$. -/
theorem cmpI_run (i : CI) (m n : ℕ) (v : Bool) (St : ∀ _ : K, List Sym)
    (ha : St (ca i) = cnt (Sym.bit true) m) (hb : St (cb i) = cnt (Sym.bit true) n)
    (hR : St .R = []) (hQ : St .Q = []) :
    RunLe prog (3 * min m n + 4) ⟨some (.cmp i), v, St⟩ ⟨some (cout i (compare m n)), false, St⟩ :=
  by cases i <;>
    exact (cmp_run (M := prog) rfl (fun _ => rfl) (fun _ => rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) m n v St ha hb hR hQ).le (by split <;> omega)

/-- **Outcome of the HAMPATH verifier's vertex-range comparison.** For all $m, n \in \mathbb{N}$,
the label that the comparison of the current vertex with the vertex count picks on the ordering
$\mathrm{compare}(m, n)$ of $m$ and $n$ is the head-or-edge dispatch label $\mathrm{hd}$ if
$m < n$, and the reject label $\mathrm{no}$ otherwise. -/
theorem cout_an (m n : ℕ) : cout .an (compare m n) = if m < n then .hd else .no := by
  rcases lt_trichotomy m n with h | rfl | h
  · simp [cout, Nat.compare_eq_lt.2 h, h]
  · simp [cout]
  · simp [cout, Nat.compare_eq_gt.2 h, Nat.not_lt.2 h.le]

/-- **Outcome of a HAMPATH-verifier equality comparison.** Write $\mathrm{cout}(i, o)$ for the
label that counter comparison $i$ of the HAMPATH verifier picks on the ordering
$o \in \{\mathrm{lt}, \mathrm{eq}, \mathrm{gt}\}$. Let $i$ be a counter comparison and $l$ a label
such that $\mathrm{cout}(i, \mathrm{eq}) = l$ and $\mathrm{cout}(i, o)$ is the reject label
$\mathrm{no}$ for every ordering $o \ne \mathrm{eq}$. Then for all $m, n \in \mathbb{N}$, the label
$\mathrm{cout}(i, \mathrm{compare}(m, n))$ on the ordering of $m$ and $n$ is $l$ if $m = n$ and
$\mathrm{no}$ otherwise. -/
theorem cout_eq (i : CI) (l : Lab) (hl : cout i .eq = l) (hne : ∀ o, o ≠ .eq → cout i o = .no)
    (m n : ℕ) : cout i (compare m n) = if m = n then l else .no := by
  by_cases h : m = n
  · subst h; simpa using hl
  · rw [ite_eq_right h, hne]
    rwa [Ne, Nat.compare_eq_eq]

/-- **Run of the HAMPATH verifier's unary comparison loop.** Let $\mathit{src}$, $\mathit{sv}$, $c$
and the scratch stack $R$ be four distinct stacks of the HAMPATH verifier, and let $\mathrm{cb}$ and
$\mathrm{fin}$ be families of labels indexed by booleans such that for every boolean $\mathit{ok}$
the instruction at $\mathrm{cb}(\mathit{ok})$ is the unary comparison step on $\mathit{src}$,
$\mathit{sv}$, $c$ with loop labels $\mathrm{cb}$, exit labels $\mathrm{fin}$ and verdict
$\mathit{ok}$. Write $1$ and $0$ for the bit symbols of true and false, $1^k$ for $k$ copies of
$1$, and $\bar r$ for the list of bit symbols of a list of booleans $r$; stacks are listed from the
top. Then for all $a, u, j \in \mathbb{N}$, every boolean $\mathit{ok}$, every list of booleans
$r$, every flag $v$ and all stack contents $\sigma$ with $\sigma(\mathit{src}) = 1^a\,0\,\bar r$,
$\sigma(c) = 1^u$ and $\sigma(R) = 1^j$, the verifier runs in exactly $a + 1$ steps from label
$\mathrm{cb}(\mathit{ok})$ with flag $v$ and stacks $\sigma$ to label $\mathrm{fin}(b)$, where $b$
is true exactly when $\mathit{ok}$ is true and $a = u$, with some flag and some stacks $\sigma'$
such that $\sigma'(\mathit{src}) = \bar r$, $\sigma'(\mathit{sv}) = 0\,1^a\,\sigma(\mathit{sv})$,
$\sigma'(c) = 1^{\max(u - a, 0)}$, $\sigma'(R) = 1^{\min(a, u) + j}$, and $\sigma'(k) = \sigma(k)$
for every other stack $k$. -/
theorem cb_run {src sv c : K} {cb fin : Bool → Lab}
    (hp : ∀ ok, prog (cb ok) = cbS src sv c cb fin ok) (h1 : sv ≠ src) (h2 : c ≠ src)
    (h3 : K.R ≠ src) (h4 : c ≠ sv) (h5 : K.R ≠ sv) (h6 : K.R ≠ c) :
    ∀ (a u j : ℕ) (ok : Bool) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St src = (List.replicate a true ++ false :: r).map Sym.bit → St c = cnt (Sym.bit true) u →
      St .R = cnt (Sym.bit true) j →
      ∃ v' S', Run prog (a + 1) ⟨some (cb ok), v, St⟩
        ⟨some (fin (ok && decide (a = u))), v', S'⟩ ∧ S' src = r.map Sym.bit ∧
        S' sv = (List.replicate a true ++ [false]).reverse.map Sym.bit ++ St sv ∧
        S' c = cnt (Sym.bit true) (u - a) ∧ S' .R = cnt (Sym.bit true) (min a u + j) ∧
        ∀ k, k ≠ src → k ≠ sv → k ≠ c → k ≠ .R → S' k = St k := by
  intro a
  induction a with
  | zero =>
      intro u j ok r v St hs hc hR
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hs
      obtain ⟨v', h⟩ := step1 (l := cb ok) (v := v) (S := St)
        (l' := fin (ok && decide (0 = u)))
        (S' := update (update St src (r.map Sym.bit)) sv (Sym.bit false :: St sv))
        (by cases u <;> simp [hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, update_of_ne h1,
          update_of_ne h2, update_of_ne h4])
        (by cases u <;> simp [hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, update_of_ne h1,
          update_of_ne h2, update_of_ne h4])
      refine ⟨v', _, h, by simp [update_of_ne h1.symm], by simp, ?_, ?_, fun k k1 k2 _ _ => ?_⟩
      · simp [update_of_ne h4, update_of_ne h2, hc]
      · simp [update_of_ne h5, update_of_ne h3, hR]
      · simp [update_of_ne k1, update_of_ne k2]
  | succ a ih =>
      intro u j ok r v St hs hc hR
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hs
      cases u with
      | zero =>
          set St₁ := update (update (update St src
            ((List.replicate a true ++ false :: r).map Sym.bit)) sv (Sym.bit true :: St sv)) c []
            with hSt₁
          obtain ⟨v', S', hrun, hs', hsv', hc', hR', hF'⟩ := ih 0 j false r false St₁
            (by simp [hSt₁, update_of_ne h1.symm, update_of_ne h2.symm])
            (by simp [hSt₁])
            (by simp [hSt₁, update_of_ne h6, update_of_ne h5, update_of_ne h3, hR])
          have hstep :
              TM2.step prog ⟨some (cb ok), v, St⟩ = some ⟨some (cb false), false, St₁⟩ := by
            simp [TM2.step, hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, hSt₁,
              update_of_ne h1, update_of_ne h2, update_of_ne h4]
          refine ⟨v', S', by simpa using Run.head hstep hrun, hs', ?_, by simpa using hc', ?_,
            fun k k1 k2 k3 k4 => ?_⟩
          · rw [hsv', hSt₁, update_of_ne h4.symm, update_self, blk_succ]
          · simpa using hR'
          · rw [hF' k k1 k2 k3 k4, hSt₁, update_of_ne k3, update_of_ne k2, update_of_ne k1]
      | succ u =>
          set St₁ := update (update (update (update St src
            ((List.replicate a true ++ false :: r).map Sym.bit)) sv (Sym.bit true :: St sv)) c
            (cnt (Sym.bit true) u)) .R (Sym.bit true :: St .R) with hSt₁
          obtain ⟨v', S', hrun, hs', hsv', hc', hR', hF'⟩ := ih u (j + 1) ok r true St₁
            (by simp [hSt₁, update_of_ne h1.symm, update_of_ne h2.symm, update_of_ne h3.symm])
            (by simp [hSt₁, update_of_ne h6.symm]) (by simp [hSt₁, hR, cnt_succ])
          have hstep : TM2.step prog ⟨some (cb ok), v, St⟩ = some ⟨some (cb ok), true, St₁⟩ := by
            simp [TM2.step, hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, hSt₁, cnt_succ,
              update_of_ne h1, update_of_ne h2, update_of_ne h4, update_of_ne h6,
              update_of_ne h5, update_of_ne h3]
          refine ⟨v', S', by simpa using Run.head hstep hrun, hs', ?_, by simpa using hc', ?_,
            fun k k1 k2 k3 k4 => ?_⟩
          · rw [hsv', hSt₁, update_of_ne h5.symm, update_of_ne h4.symm, update_self, blk_succ]
          · rw [hR']; congr 1; omega
          · rw [hF' k k1 k2 k3 k4, hSt₁, update_of_ne k4, update_of_ne k3, update_of_ne k2,
              update_of_ne k1]

/-- **HAMPATH-verifier unary comparison with the counter restored.** Let $\mathit{src}$,
$\mathit{sv}$, $c$ and the scratch stack $R$ be four distinct stacks of the HAMPATH verifier, and
let $\mathrm{cb}$, $\mathrm{rs}$ and $\mathrm{nx}$ be families of labels indexed by booleans such
that for every boolean $\mathit{ok}$ the instruction at $\mathrm{cb}(\mathit{ok})$ is the unary
comparison step on $\mathit{src}$, $\mathit{sv}$, $c$ with loop labels $\mathrm{cb}$, exit labels
$\mathrm{rs}$ and verdict $\mathit{ok}$, and the instruction at $\mathrm{rs}(\mathit{ok})$ is the
transfer loop that pops $R$ until it is empty, pushing one unit (the bit symbol of true) on $c$
per symbol popped, and then goes to $\mathrm{nx}(\mathit{ok})$. Write $1$ and $0$ for the bit
symbols of true and false, $1^k$ for $k$ copies of $1$, and $\bar r$ for the list of bit symbols
of a list of booleans $r$; stacks are listed from the top. Let $a, u \in \mathbb{N}$, let
$\mathit{ok}$ be a boolean, $r$ a list of booleans, $v$ a flag, and $\sigma$ stack contents with
$\sigma(\mathit{src}) = 1^a\,0\,\bar r$, $\sigma(c) = 1^u$ and $\sigma(R)$ empty. Then the verifier
runs in exactly $(a + 1) + (\min(a, u) + 1)$ steps from label $\mathrm{cb}(\mathit{ok})$ with flag
$v$ and stacks $\sigma$ to label $\mathrm{nx}(b)$, where $b$ is true exactly when $\mathit{ok}$ is
true and $a = u$, with some flag and with the stacks of $\sigma$ except that $\mathit{src}$ now
holds $\bar r$ and $\mathit{sv}$ holds $0\,1^a$ followed by $\sigma(\mathit{sv})$. -/
theorem cmpN_run {src sv c : K} {cb rs nx : Bool → Lab}
    (hp : ∀ ok, prog (cb ok) = cbS src sv c cb rs ok)
    (hr : ∀ ok, prog (rs ok) = xfer .R [⟨c, Sym.bit true⟩] (rs ok) (nx ok))
    (h1 : sv ≠ src) (h2 : c ≠ src) (h3 : K.R ≠ src) (h4 : c ≠ sv) (h5 : K.R ≠ sv)
    (h6 : K.R ≠ c) (a u : ℕ) (ok : Bool) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hs : St src = (List.replicate a true ++ false :: r).map Sym.bit)
    (hc : St c = cnt (Sym.bit true) u) (hR : St .R = []) :
    ∃ v', Run prog (a + 1 + (min a u + 1)) ⟨some (cb ok), v, St⟩
      ⟨some (nx (ok && decide (a = u))), v', update (update St src (r.map Sym.bit)) sv
        ((List.replicate a true ++ [false]).reverse.map Sym.bit ++ St sv)⟩ := by
  obtain ⟨v₁, S₁, h₁, hs₁, hsv₁, hc₁, hR₁, hF₁⟩ :=
    cb_run hp h1 h2 h3 h4 h5 h6 a u 0 ok r v St hs hc (by simp [hR])
  have h₂ := xfer_run (hr (ok && decide (a = u))) (single_nodupKeys _) (by simpa using h6)
    (Sym.bit true) (min a u + 0) v₁ S₁ hR₁
  have e : addU [⟨c, Sym.bit true⟩] (min a u + 0) (update S₁ .R []) =
      update (update St src (r.map Sym.bit)) sv
        ((List.replicate a true ++ [false]).reverse.map Sym.bit ++ St sv) := by
    funext k
    by_cases hk : k = c
    · subst hk
      rw [addU_single_self, update_of_ne h6.symm, hc₁, update_of_ne h4, update_of_ne h2, hc,
        cnt_add]
      congr 1; omega
    · rw [addU_single_ne _ _ _ hk]
      by_cases hkR : k = .R
      · subst hkR; rw [update_self, update_of_ne h5, update_of_ne h3, hR]
      · rw [update_of_ne hkR]
        by_cases hks : k = sv
        · subst hks; rw [update_self, hsv₁]
        · rw [update_of_ne hks]
          by_cases hks' : k = src
          · subst hks'; rw [update_self, hs₁]
          · rw [update_of_ne hks', hF₁ k hks' hks hk hkR]
  rw [e] at h₂
  exact ⟨_, (h₁.trans h₂).of_eq (by omega)⟩

/-! ### Validation -/

/-- **The edge-list check of the Hamiltonian-path verifier.** Let $r$ and $acc$ be bit lists, and
let the stacks $St$ hold $r$ on the input stack $X$ and the reverse of $acc$ on the save stack
$E$. Started at the label $\mathsf{vE}$ with any flag value, the verifier reaches within at most
$2|r| + 1$ steps the label $\mathsf{vEb}$ if $r$ decodes as an edge list (a sequence of pairs of
unary numbers, each a block of ones ended by a zero) and the label $\mathsf{no}$ otherwise. When
$r$ decodes, the final stacks are $St$ with $X$ emptied and $E$ holding the reverse of the
concatenation of $acc$ and $r$ (that is, $r$ reversed on top of $acc$ reversed), all other
stacks unchanged. -/
theorem valE_run : ∀ (r acc : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
    St .X = r.map Sym.bit → St .E = acc.reverse.map Sym.bit →
    ∃ v' S', RunLe prog (2 * r.length + 1) ⟨some .vE, v, St⟩
      ⟨some (if (Karp.decodeEs r).isSome then .vEb else .no), v', S'⟩ ∧
      ((Karp.decodeEs r).isSome →
        S' = update (update St .X []) .E ((acc ++ r).reverse.map Sym.bit)) := by
  intro r
  induction hL : r.length using Nat.strong_induction_on generalizing r with
  | _ L ih =>
  intro acc v St hX hE
  subst hL
  obtain ⟨v₀, h₀⟩ := ifE_run (l := .vE) rfl v St
  by_cases hr : r = []
  · subst hr
    rw [ite_eq_left (by simpa using hX)] at h₀
    refine ⟨v₀, St, by simpa [Karp.decodeEs_nil] using h₀.le le_rfl, fun _ => ?_⟩
    funext k; cases k <;> simp_all
  have hpos : 1 ≤ r.length := List.length_pos_of_ne_nil hr
  rw [ite_eq_right (by rw [hX]; simpa using hr)] at h₀
  cases h₁ : readUnaryLength r with
  | none =>
      obtain ⟨v₁, S₁, r₁⟩ := skipU_none (src := .X) (dst := .E) (self := .vEU) (next := .vEV) rfl
        (by decide) r v₀ St h₁ hX
      rw [Karp.decodeEs_of_none hr h₁]
      exact ⟨v₁, S₁, ((h₀.le le_rfl).trans r₁).mono (by omega), by simp⟩
  | some p =>
      obtain ⟨u, r₁⟩ := p
      have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      have hl₁ : r.length = u + 1 + r₁.length := by rw [hx₁]; simp; omega
      obtain ⟨v₁, run₁⟩ := skipU_run (src := .X) (dst := .E) (self := .vEU) (next := .vEV) rfl
        (by decide) u r₁ v₀ St (by rw [hX, hx₁])
      set St₁ := update (update St .X (r₁.map Sym.bit)) .E
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .E) with hSt₁
      cases h₂ : readUnaryLength r₁ with
      | none =>
          obtain ⟨v₂, S₂, run₂⟩ := skipU_none (src := .X) (dst := .E) (self := .vEV) (next := .vE)
            rfl (by decide) r₁ v₁ St₁ h₂ (by simp [hSt₁])
          rw [Karp.decodeEs_of_some_none h₁ h₂]
          exact ⟨v₂, S₂, (((h₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono (by omega),
            by simp⟩
      | some q =>
          obtain ⟨u', r₂⟩ := q
          have hx₂ := (readUnaryLength_eq_some_iff _ _ _).1 h₂
          have hl₂ : r₁.length = u' + 1 + r₂.length := by rw [hx₂]; simp; omega
          obtain ⟨v₂, run₂⟩ := skipU_run (src := .X) (dst := .E) (self := .vEV) (next := .vE) rfl
            (by decide) u' r₂ v₁ St₁ (by simp [hSt₁, hx₂])
          set St₂ := update (update St₁ .X (r₂.map Sym.bit)) .E
            ((List.replicate u' true ++ [false]).reverse.map Sym.bit ++ St₁ .E) with hSt₂
          obtain ⟨v₃, S₃, run₃, hF₃⟩ := ih r₂.length (by omega) r₂ rfl
            (acc ++ (List.replicate u true ++ [false]) ++ (List.replicate u' true ++ [false]))
            v₂ St₂ (by simp [hSt₂]) (by simp [hSt₂, hSt₁, hE])
          rw [Karp.decodeEs_of_some_some h₁ h₂, Option.isSome_map]
          refine ⟨v₃, S₃, ((((h₀.le le_rfl).trans (run₁.le le_rfl)).trans
            (run₂.le le_rfl)).trans run₃).mono (by omega), fun h => ?_⟩
          rw [hF₃ h, hSt₂, hSt₁, update_update_update_update (by decide),
            update_update_update_update (by decide), hx₁, hx₂]
          simp

/-- **The witness check of the Hamiltonian-path verifier.** Let $w$ and $acc$ be bit lists, and
let the stacks $St$ hold $w$ on the witness stack $W$ and the reverse of $acc$ on the save stack
$Z$. Started at the label $\mathsf{vW}$ with any flag value, the verifier reaches within at most
$2|w| + 1$ steps the label $\mathsf{vWb}$ if $w$ decodes as a vertex list (a sequence of unary
numbers, each a block of ones ended by a zero) and the label $\mathsf{no}$ otherwise. When $w$
decodes, the final stacks are $St$ with $W$ emptied and $Z$ holding the reverse of the
concatenation of $acc$ and $w$ (that is, $w$ reversed on top of $acc$ reversed), all other
stacks unchanged. -/
theorem valW_run : ∀ (w acc : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
    St .W = w.map Sym.bit → St .Z = acc.reverse.map Sym.bit →
    ∃ v' S', RunLe prog (2 * w.length + 1) ⟨some .vW, v, St⟩
      ⟨some (if (decodeW w).isSome then .vWb else .no), v', S'⟩ ∧
      ((decodeW w).isSome → S' = update (update St .W []) .Z ((acc ++ w).reverse.map Sym.bit)) := by
  intro w
  induction hL : w.length using Nat.strong_induction_on generalizing w with
  | _ L ih =>
  intro acc v St hW hZ
  subst hL
  obtain ⟨v₀, h₀⟩ := ifE_run (l := .vW) rfl v St
  by_cases hw : w = []
  · subst hw
    rw [ite_eq_left (by simpa using hW)] at h₀
    refine ⟨v₀, St, by simpa [decodeW_nil] using h₀.le le_rfl, fun _ => ?_⟩
    funext k; cases k <;> simp_all
  have hpos : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  rw [ite_eq_right (by rw [hW]; simpa using hw)] at h₀
  cases h₁ : readUnaryLength w with
  | none =>
      obtain ⟨v₁, S₁, r₁⟩ := skipU_none (src := .W) (dst := .Z) (self := .vWU) (next := .vW) rfl
        (by decide) w v₀ St h₁ hW
      rw [decodeW_of_none hw h₁]
      exact ⟨v₁, S₁, ((h₀.le le_rfl).trans r₁).mono (by omega), by simp⟩
  | some p =>
      obtain ⟨u, r₁⟩ := p
      have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      have hl₁ : w.length = u + 1 + r₁.length := by rw [hx₁]; simp; omega
      obtain ⟨v₁, run₁⟩ := skipU_run (src := .W) (dst := .Z) (self := .vWU) (next := .vW) rfl
        (by decide) u r₁ v₀ St (by rw [hW, hx₁])
      set St₁ := update (update St .W (r₁.map Sym.bit)) .Z
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .Z) with hSt₁
      obtain ⟨v₂, S₂, run₂, hF₂⟩ := ih r₁.length (by omega) r₁ rfl
        (acc ++ (List.replicate u true ++ [false])) v₁ St₁ (by simp [hSt₁]) (by simp [hSt₁, hZ])
      rw [decodeW_of_some h₁, Option.isSome_map]
      refine ⟨v₂, S₂, (((h₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono (by omega),
        fun h => ?_⟩
      rw [hF₂ h, hSt₁, update_update_update_update (by decide), hx₁]
      simp

/-! ### The scans -/

/-- **The edge scan of the Hamiltonian path verifier.** For a list $e$ of pairs of natural
numbers write $\mathrm{bits}(e)$ for its edge-list encoding, in which each pair $(u, u')$
contributes $u$ copies of `true`, then `false`, then $u'$ copies of `true`, then `false`. Let
$a, b$ be natural numbers and $r$, $d$ lists of pairs of natural numbers. Suppose that the
verifier's stacks hold, as bit symbols with the first bit on top, $\mathrm{bits}(r)$ on
$\mathsf{X}$, $\mathrm{bits}(d)$ in reverse order on $\mathsf{E}$, $a$ copies of the bit `true`
on $\mathsf{A}$, $b$ copies of the bit `true` on $\mathsf{B}$, and nothing on $\mathsf{R}$, the
other stacks being arbitrary. Started at label $\mathrm{scan}$ with either value of its Boolean
variable, the verifier reaches, within $4|\mathrm{bits}(r)| + |\mathrm{bits}(d)| + 2$ steps, the
label $\mathrm{nd}$ if $(b, a)$ is one of the pairs of $r$ and the label $\mathrm{no}$
otherwise. In the first case its stacks are then the initial ones except that $\mathsf{X}$
holds the encoding $\mathrm{bits}$ of the list $d$ followed by $r$, and $\mathsf{E}$ is empty. -/
theorem scan_run (a b : ℕ) : ∀ (rest done : List (ℕ × ℕ)) (v : Bool) (St : ∀ _ : K, List Sym),
    St .X = (Karp.edgeBits rest).map Sym.bit → St .E = (Karp.edgeBits done).reverse.map Sym.bit →
    St .A = cnt (Sym.bit true) a → St .B = cnt (Sym.bit true) b → St .R = [] →
    ∃ v' S', RunLe prog (4 * (Karp.edgeBits rest).length + (Karp.edgeBits done).length + 2)
      ⟨some .scan, v, St⟩ ⟨some (if (b, a) ∈ rest then .nd else .no), v', S'⟩ ∧
      ((b, a) ∈ rest →
        S' = update (update St .X ((Karp.edgeBits (done ++ rest)).map Sym.bit)) .E [])
  | [], done, v, St, hX, _, _, _, _ => by
      obtain ⟨v', h⟩ := ifE_run (l := .scan) rfl v St
      rw [ite_eq_left (by simpa using hX)] at h
      exact ⟨v', St, by simpa using h.le (by omega), by simp⟩
  | (u, u') :: rest, done, v, St, hX, hE, hA, hB, hR => by
      have hX' : St .X = (List.replicate u true ++ false ::
          (List.replicate u' true ++ false :: Karp.edgeBits rest)).map Sym.bit := by
        rw [hX, edgeBits_cons]
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .scan) rfl v St
      rw [ite_eq_right (by rw [hX']; simp)] at h₀
      obtain ⟨v₁, run₁⟩ := cmpN_run (src := .X) (sv := .E) (c := .B) (cb := .ceU) (rs := .rsU)
        (nx := .ceV) (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) u b true _ v₀ St hX' hB hR
      set St₁ := update (update St .X
        ((List.replicate u' true ++ false :: Karp.edgeBits rest).map Sym.bit)) .E
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .E) with hSt₁
      obtain ⟨v₂, run₂⟩ := cmpN_run (src := .X) (sv := .E) (c := .A) (cb := .ceV) (rs := .rsV)
        (nx := fun ok => if ok then .scB else .scan) (fun _ => rfl) (fun _ => rfl) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) u' a (true && decide (u = b))
        (Karp.edgeBits rest) v₁ St₁ (by simp [hSt₁]) (by simp [hSt₁, hA]) (by simp [hSt₁, hR])
      set St₂ := update (update St₁ .X ((Karp.edgeBits rest).map Sym.bit)) .E
        ((List.replicate u' true ++ [false]).reverse.map Sym.bit ++ St₁ .E) with hSt₂
      have hE₂ : St₂ .E = (Karp.edgeBits (done ++ [(u, u')])).reverse.map Sym.bit := by
        simp [hSt₂, hSt₁, hE, edgeBits_append, edgeBits_cons]
      have hlen : (Karp.edgeBits ((u, u') :: rest)).length =
          u + u' + 2 + (Karp.edgeBits rest).length := by simp [edgeBits_cons]; omega
      have hlen' : (Karp.edgeBits (done ++ [(u, u')])).length =
          (Karp.edgeBits done).length + u + u' + 2 := by
        simp [edgeBits_append, edgeBits_cons]; omega
      have m₁ := Nat.min_le_left u b
      have m₂ := Nat.min_le_left u' a
      by_cases hf : u = b ∧ u' = a
      · obtain ⟨rfl, rfl⟩ := hf
        simp only [decide_true, Bool.and_self, ↓reduceIte] at run₁ run₂
        rw [ite_eq_left List.mem_cons_self]
        obtain ⟨v₃, run₃⟩ := mv_run (self := .scB) (next := .nd) (a := .E) (b := .X) rfl
          (by decide) _ v₂ St₂ hE₂
        refine ⟨v₃, _, ((((h₀.le le_rfl).trans (run₁.le le_rfl)).trans (run₂.le le_rfl)).trans
          (run₃.le le_rfl)).mono ?_, fun _ => ?_⟩
        · simp only [List.length_reverse]; omega
        · funext k
          cases k <;> simp [hSt₂, hSt₁, edgeBits_append, edgeBits_cons, List.map_reverse]
      · have hf' : (true && decide (u = b) && decide (u' = a)) = false := by
          simpa [not_and] using hf
        rw [hf'] at run₂
        obtain ⟨v₃, S₃, run₃, hF₃⟩ := scan_run a b rest (done ++ [(u, u')]) v₂ St₂
          (by simp [hSt₂]) hE₂ (by simp [hSt₂, hSt₁, hA]) (by simp [hSt₂, hSt₁, hB])
          (by simp [hSt₂, hSt₁, hR])
        have hm : (b, a) ∈ (u, u') :: rest ↔ (b, a) ∈ rest := by
          simp only [List.mem_cons, Prod.mk.injEq]
          exact ⟨fun h => h.resolve_left fun h' => hf ⟨h'.1.symm, h'.2.symm⟩, Or.inr⟩
        rw [if_congr hm rfl rfl]
        refine ⟨v₃, S₃, ((((h₀.le le_rfl).trans (run₁.le le_rfl)).trans
          (run₂.le le_rfl)).trans run₃).mono ?_, fun h => ?_⟩
        · rw [hlen', hlen]; omega
        · rw [hF₃ (hm.1 h)]
          funext k
          cases k <;> simp [hSt₂, hSt₁]

/-- **The repeat scan of the Hamiltonian path verifier.** For a list $p$ of natural numbers
write $\mathrm{enc}(p)$ for its witness encoding: each entry in unary (that many copies of
`true`) followed by `false`. Let $a$ be a natural number and $q$, $d$ lists of natural numbers.
Suppose that the verifier's stacks hold, as bit symbols with the first bit on top, the bits of
$\mathrm{enc}(q)$ on $\mathsf{W}$, the bits of $\mathrm{enc}(d)$ in reverse order on
$\mathsf{Z}$, $a$ copies of the bit `true` on $\mathsf{A}$, and nothing on $\mathsf{R}$, the
other stacks being arbitrary. Started at label $\mathrm{nd}$ with either value of its Boolean
variable, the verifier reaches, within $4|\mathrm{enc}(q)| + |\mathrm{enc}(d)| + 2$ steps, the
label $\mathrm{no}$ if $a$ is an entry of $q$ and the label $\mathrm{incC}$ otherwise. In the
second case its stacks are then the initial ones except that $\mathsf{W}$ holds the bits of the
encoding of $d$ followed by $q$, and $\mathsf{Z}$ is empty. -/
theorem nd_run (a : ℕ) : ∀ (q done : List ℕ) (v : Bool) (St : ∀ _ : K, List Sym),
    St .W = (encW q).map Sym.bit → St .Z = (encW done).reverse.map Sym.bit →
    St .A = cnt (Sym.bit true) a → St .R = [] →
    ∃ v' S', RunLe prog (4 * (encW q).length + (encW done).length + 2) ⟨some .nd, v, St⟩
      ⟨some (if a ∈ q then .no else .incC), v', S'⟩ ∧
      (a ∉ q → S' = update (update St .W ((encW (done ++ q)).map Sym.bit)) .Z [])
  | [], done, v, St, hW, hZ, _, _ => by
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .nd) rfl v St
      rw [ite_eq_left (by simpa using hW)] at h₀
      obtain ⟨v₁, h₁⟩ := mv_run (self := .ndB) (next := .incC) (a := .Z) (b := .W) rfl
        (by decide) _ v₀ St hZ
      refine ⟨v₁, _, ((h₀.le le_rfl).trans (h₁.le le_rfl)).mono (by simp; omega), fun _ => ?_⟩
      funext k
      cases k <;> simp [hW, List.map_reverse]
  | u :: q, done, v, St, hW, hZ, hA, hR => by
      have hW' : St .W = (List.replicate u true ++ false :: encW q).map Sym.bit := by
        rw [hW, encW_cons]
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .nd) rfl v St
      rw [ite_eq_right (by rw [hW']; simp)] at h₀
      obtain ⟨v₁, run₁⟩ := cmpN_run (src := .W) (sv := .Z) (c := .A) (cb := .cbN) (rs := .rsN)
        (nx := fun ok => if ok then .no else .nd) (fun _ => rfl) (fun _ => rfl) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) u a true _ v₀ St hW' hA hR
      set St₁ := update (update St .W ((encW q).map Sym.bit)) .Z
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .Z) with hSt₁
      have hlen : (encW (u :: q)).length = u + 1 + (encW q).length := by simp [encW_cons]; omega
      have m₁ := Nat.min_le_left u a
      by_cases hua : u = a
      · subst hua
        simp only [Bool.true_and, decide_true, ↓reduceIte] at run₁
        rw [ite_eq_left List.mem_cons_self]
        refine ⟨v₁, _, ((h₀.le le_rfl).trans (run₁.le le_rfl)).mono (by omega), ?_⟩
        simp
      · have hf : (true && decide (u = a)) = false := by simpa using hua
        rw [hf] at run₁
        obtain ⟨v₂, S₂, run₂, hF₂⟩ := nd_run a q (done ++ [u]) v₁ St₁ (by simp [hSt₁])
          (by simp [hSt₁, hZ, encW_append, encW_cons]) (by simp [hSt₁, hA]) (by simp [hSt₁, hR])
        have hm : a ∈ u :: q ↔ a ∈ q := by
          simp only [List.mem_cons]
          exact ⟨fun h => h.resolve_left fun h' => hua h'.symm, Or.inr⟩
        rw [if_congr hm rfl rfl]
        have hlen' : (encW (done ++ [u])).length = (encW done).length + u + 1 := by
          simp [encW_append, encW_cons]; omega
        refine ⟨v₂, S₂, (((h₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono ?_,
          fun h => ?_⟩
        · rw [hlen', hlen]; omega
        · rw [hF₂ (fun h' => h (hm.2 h'))]
          funext k
          cases k <;> simp [hSt₁]

/-! ### The vertex walk -/

/-- **Stack layout between vertex steps.** For an edge list $es$, numbers $s, t, n, c, b$ and a
list $q$ of vertices, the stacks of the verifier between two vertex steps: $X$ holds the bits of
the edge list $es$, $W$ holds the bits of the witness encoding of $q$, the counters $S$, $T$,
$N$, $C$ and $B$ hold $s$, $t$, $n$, $c$ and $b$ in unary, and the stacks $A$, $E$, $Z$, $R$
and $Q$ are empty. -/
def lay (es : List (ℕ × ℕ)) (s t n c b : ℕ) (q : List ℕ) : K → List Sym
  | .X => (Karp.edgeBits es).map Sym.bit
  | .W => (encW q).map Sym.bit
  | .S => cnt (Sym.bit true) s
  | .T => cnt (Sym.bit true) t
  | .N => cnt (Sym.bit true) n
  | .C => cnt (Sym.bit true) c
  | .A => []
  | .B => cnt (Sym.bit true) b
  | .E => []
  | .Z => []
  | .R => []
  | .Q => []

/-- **Stack layout during a vertex step.** For an edge list $es$, numbers $s, t, n, c, b, a$ and
a list $q$ of vertices, the stacks of the verifier during the step on vertex $a$: the layout
between vertex steps for $es, s, t, n, c, b, q$, except that stack $A$ holds $a$ in unary. -/
def mid (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) : K → List Sym :=
  update (lay es s t n c b q) .A (cnt (Sym.bit true) a)

/-- **Running the head-or-edge check.** Let $es$ be an edge list, $s, t, n, c, b, a$ numbers and
$q$ a list of vertices, and say the check passes when $a = s$ in case $c = 0$, and
$(b, a) \in es$ in case $c \neq 0$. Started at the head-or-edge dispatch, in any internal state,
on the stack layout during the step on vertex $a$ for $es, s, t, n, c, b, a, q$, the verifier
reaches within $3a + 4\ell + 7$ steps, where $\ell$ is the number of bits of $es$, the repeat
scan if the check passes and the reject label otherwise, in some internal state and with some
stacks; if the check passes, these stacks are the ones it started on. -/
theorem hd_run (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) (v : Bool) :
    ∃ v' S', RunLe prog (3 * a + 4 * (Karp.edgeBits es).length + 7)
      ⟨some .hd, v, mid es s t n c b a q⟩
      ⟨some (if (if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) = true then .nd
        else .no), v', S'⟩ ∧
      ((if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) = true →
        S' = mid es s t n c b a q) := by
  obtain ⟨v₀, h₀⟩ := ifE_run (l := .hd) rfl v (mid es s t n c b a q)
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left (by simp [mid, lay])] at h₀
    have h₁ := cmpI_run .as a s v₀ (mid es s t n 0 b a q) (by simp [mid, ca])
      (by simp [mid, lay, cb]) (by simp [mid, lay]) (by simp [mid, lay])
    rw [cout_eq .as .nd rfl (by intro o ho; cases o <;> simp_all [cout]) a s] at h₁
    simp only [↓reduceIte, decide_eq_true_eq]
    refine ⟨false, _, ((h₀.le le_rfl).trans h₁).mono ?_, fun _ => rfl⟩
    have := Nat.min_le_left a s
    omega
  · rw [ite_eq_right (by simp [mid, lay, hc])] at h₀
    obtain ⟨v₁, S₁, h₁, hF₁⟩ := scan_run a b es [] v₀ (mid es s t n c b a q) (by simp [mid, lay])
      (by simp [mid, lay]) (by simp [mid]) (by simp [mid, lay]) (by simp [mid, lay])
    simp only [hc, ↓reduceIte, decide_eq_true_eq]
    refine ⟨v₁, S₁, ((h₀.le le_rfl).trans h₁).mono (by simp; omega), fun h => ?_⟩
    rw [hF₁ h]
    funext k
    cases k <;> simp [mid, lay]

/-- **The rest of a vertex step in the Hamiltonian-path verifier.** Let $es$ be an edge list,
$s, t, n, c, b, a$ natural numbers and $q$ a list of natural numbers. Start the verifier, with
any flag value, at the label $\mathsf{nd}$ (the repeat scan) with its stacks in the mid-step
layout: the between-steps layout for $es$, $s$, $t$, $n$, count $c$, previous vertex $b$ and
remaining vertices $q$, with $a$ in unary on the stack $A$. Let $w$ be the unary encoding of $q$.
Then within at most $4|w| + a + b + 6$ steps it reaches the label $\mathsf{no}$ if $a \in q$ and
the label $\mathsf{loop}$ if $a \notin q$. In the second case ($a$ has been counted and become
the previous vertex) the stacks end in the between-steps layout for $es$, $s$, $t$, $n$, count
$c + 1$, previous vertex $a$ and remaining vertices $q$. -/
theorem tail_run (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) (v : Bool) :
    ∃ v' S', RunLe prog (4 * (encW q).length + a + b + 6) ⟨some .nd, v, mid es s t n c b a q⟩
      ⟨some (if a ∈ q then .no else .loop), v', S'⟩ ∧
      (a ∉ q → S' = lay es s t n (c + 1) a q) := by
  obtain ⟨v₁, S₁, h₁, hF₁⟩ := nd_run a q [] v (mid es s t n c b a q) (by simp [mid, lay])
    (by simp [mid, lay]) (by simp [mid]) (by simp [mid, lay])
  by_cases ha : a ∈ q
  · rw [ite_eq_left ha] at h₁ ⊢
    exact ⟨v₁, S₁, h₁.mono (by simp; omega), fun h => absurd ha h⟩
  · rw [ite_eq_right ha] at h₁ ⊢
    have e₁ : S₁ = mid es s t n c b a q := by
      rw [hF₁ ha]
      funext k
      cases k <;> simp [mid, lay]
    subst e₁
    have h₂ := incr_run (M := prog) (self := .incC) (next := .dB) (k := .C) (u := Sym.bit true)
      rfl v₁ (mid es s t n c b a q)
    set S₂ := update (mid es s t n c b a q) .C (Sym.bit true :: mid es s t n c b a q .C) with hS₂
    have h₃ := xfer_run (M := prog) (self := .dB) (next := .mA) (k := .B) (ps := []) rfl
      (by simp) (by simp) (Sym.bit true) b v₁ S₂ (by simp [hS₂, mid, lay])
    set S₃ := addU ([] : List (Σ _ : K, Sym)) b (update S₂ .B []) with hS₃
    have h₄ := xfer_run (M := prog) (self := .mA) (next := .loop) (k := .A)
      (ps := [⟨.B, Sym.bit true⟩]) rfl (single_nodupKeys _) (by simp) (Sym.bit true) a
      (Flag.tag false) S₃
      (by simp [hS₃, hS₂, addU, mid])
    refine ⟨_, _, (((h₁.trans (h₂.le le_rfl)).trans (h₃.le le_rfl)).trans
      (h₄.le le_rfl)).mono (by simp; omega), fun _ => ?_⟩
    funext k
    cases k <;> simp [hS₃, hS₂, mid, lay, addU, cnt_succ]

/-- **One vertex step of the Hamiltonian-path verifier.** Let $es$ be an edge list,
$s, t, n, c, b, a$ natural numbers and $q$ a list of natural numbers. Start the verifier, with
any flag value, at the label $\mathsf{rdA}$ (read the next vertex) with its stacks in the
between-steps layout for $es$, $s$, $t$, $n$, count $c$, previous vertex $b$ and remaining
vertices $a, q$. Let $e$ be the bit encoding of $es$ and $w$ the unary encoding of $q$. Then
within at most $8a + b + 4|e| + 4|w| + 20$ steps it reaches the label $\mathsf{loop}$ if the
step check on $a$ passes and the label $\mathsf{no}$ otherwise. The step check passes when
$a < n$, $a = s$ in case $c = 0$ and $(b, a) \in es$ in case $c \ne 0$, and $a \notin q$. When
it passes, the stacks end in the between-steps layout for $es$, $s$, $t$, $n$, count $c + 1$,
previous vertex $a$ and remaining vertices $q$. -/
theorem step_run (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) (v : Bool) :
    ∃ v' S', RunLe prog (8 * a + b + 4 * (Karp.edgeBits es).length + 4 * (encW q).length + 20)
      ⟨some .rdA, v, lay es s t n c b (a :: q)⟩
      ⟨some (if stepOk s n es c b a q then .loop else .no), v', S'⟩ ∧
      (stepOk s n es c b a q = true → S' = lay es s t n (c + 1) a q) := by
  obtain ⟨v₁, h₁⟩ := readU_run (src := .W) (c := .A) (self := .rdA) (next := .cmp .an) rfl
    (by decide) a 0 (encW q) v (lay es s t n c b (a :: q)) (by simp [lay, encW_cons])
    (by simp [lay])
  have e₁ : update (update (lay es s t n c b (a :: q)) .W ((encW q).map Sym.bit)) .A
      (cnt (Sym.bit true) (a + 0)) = mid es s t n c b a q := by
    funext k
    cases k <;> simp [mid, lay]
  rw [e₁] at h₁
  have h₂ := cmpI_run .an a n v₁ (mid es s t n c b a q) (by simp [mid, ca])
    (by simp [mid, lay, cb]) (by simp [mid, lay]) (by simp [mid, lay])
  rw [cout_an] at h₂
  have m₁ := Nat.min_le_left a n
  by_cases han : a < n
  · rw [ite_eq_left han] at h₂
    obtain ⟨v₃, S₃, h₃, hF₃⟩ := hd_run es s t n c b a q false
    by_cases hh : (if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) = true
    · rw [ite_eq_left hh, hF₃ hh] at h₃
      obtain ⟨v₄, S₄, h₄, hF₄⟩ := tail_run es s t n c b a q v₃
      have hs : stepOk s n es c b a q = !decide (a ∈ q) := by
        simp only [stepOk, han, decide_true, Bool.true_and, hh]
      refine ⟨v₄, S₄, ?_, fun h => hF₄ (by simpa [hs] using h)⟩
      have e : (if stepOk s n es c b a q = true then Lab.loop else Lab.no) =
          if a ∈ q then .no else .loop := by
        by_cases ha : a ∈ q <;> simp [hs, ha]
      rw [e]
      exact ((((h₁.le le_rfl).trans h₂).trans h₃).trans h₄).mono (by omega)
    · rw [ite_eq_right hh] at h₃
      have hs : stepOk s n es c b a q = false := by
        simp only [stepOk, Bool.eq_false_iff.2 hh, Bool.and_false, Bool.false_and]
      refine ⟨v₃, S₃, ?_, fun h => by simp [hs] at h⟩
      rw [hs]
      exact (((h₁.le le_rfl).trans h₂).trans h₃).mono (by omega)
  · rw [ite_eq_right han] at h₂
    have hs : stepOk s n es c b a q = false := by simp [stepOk, han]
    refine ⟨false, mid es s t n c b a q, ?_, fun h => by simp [hs] at h⟩
    rw [hs]
    exact ((h₁.le le_rfl).trans h₂).mono (by omega)

/-- **Running the vertex loop.** Let $es$ be an edge list, $s, t, n$ numbers and $L$ a bound
with $n \le L$, $t \le L$ and at most $L$ bits in the encoding of $es$. For every list $q$ of
vertices whose witness encoding has at most $L$ bits, every count $c$, every previous vertex
$b \le L$ and every internal state, the verifier started at the vertex loop on the stack layout
between vertex steps for $es, s, t, n, c, b, q$ reaches within $(|q| + 1)(20L + 20)$ steps, with
some internal state and stacks, the accept label if the walk check for $s, t, n, es, c, b, q$
passes and the reject label otherwise. -/
theorem loop_run (es : List (ℕ × ℕ)) (s t n L : ℕ) (hn : n ≤ L) (ht : t ≤ L)
    (he : (Karp.edgeBits es).length ≤ L) : ∀ (q : List ℕ) (c b : ℕ) (v : Bool),
    (encW q).length ≤ L → b ≤ L →
    ∃ v' S', RunLe prog ((q.length + 1) * (20 * L + 20)) ⟨some .loop, v, lay es s t n c b q⟩
      ⟨some (if walkOk s t n es c b q then .yes else .no), v', S'⟩
  | [], c, b, v, _, _ => by
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .loop) rfl v (lay es s t n c b [])
      rw [ite_eq_left (by simp [lay])] at h₀
      have h₁ := cmpI_run .cn c n v₀ (lay es s t n c b []) (by simp [lay, ca]) (by simp [lay, cb])
        (by simp [lay]) (by simp [lay])
      rw [cout_eq .cn .fin rfl (by intro o ho; cases o <;> simp_all [cout]) c n] at h₁
      have m₁ := Nat.min_le_right c n
      by_cases hcn : c = n
      · rw [ite_eq_left hcn] at h₁
        obtain ⟨v₂, h₂⟩ := ifE_run (l := .fin) rfl false (lay es s t n c b [])
        by_cases hc0 : c = 0
        · rw [ite_eq_left (by simp [lay, hc0])] at h₂
          have hw : walkOk s t n es c b [] = false := by simp [walkOk, hc0]
          rw [hw]
          exact ⟨v₂, _, (((h₀.le le_rfl).trans h₁).trans (h₂.le le_rfl)).mono
            (by simp only [List.length_nil]; omega)⟩
        · rw [ite_eq_right (by simp [lay, hc0])] at h₂
          have h₃ := cmpI_run .bt b t v₂ (lay es s t n c b []) (by simp [lay, ca])
            (by simp [lay, cb]) (by simp [lay]) (by simp [lay])
          rw [cout_eq .bt .yes rfl (by intro o ho; cases o <;> simp_all [cout]) b t] at h₃
          have m₂ := Nat.min_le_right b t
          have hw : walkOk s t n es c b [] = decide (b = t) := by subst hcn; simp [walkOk, hc0]
          rw [hw]
          simp only [decide_eq_true_eq]
          exact ⟨false, _, ((((h₀.le le_rfl).trans h₁).trans (h₂.le le_rfl)).trans h₃).mono
            (by simp only [List.length_nil]; omega)⟩
      · rw [ite_eq_right hcn] at h₁
        have hw : walkOk s t n es c b [] = false := by simp [walkOk, hcn]
        rw [hw]
        exact ⟨false, _, ((h₀.le le_rfl).trans h₁).mono (by simp only [List.length_nil]; omega)⟩
  | a :: q, c, b, v, hq, hb => by
      have hq' : a + 1 + (encW q).length ≤ L := by simp [encW_cons] at hq; omega
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .loop) rfl v (lay es s t n c b (a :: q))
      rw [ite_eq_right (by simp [lay, encW_cons])] at h₀
      obtain ⟨v₁, S₁, h₁, hF₁⟩ := step_run es s t n c b a q v₀
      by_cases hst : stepOk s n es c b a q = true
      · rw [ite_eq_left hst, hF₁ hst] at h₁
        obtain ⟨v₂, S₂, h₂⟩ := loop_run es s t n L hn ht he q (c + 1) a v₁ (by omega) (by omega)
        refine ⟨v₂, S₂, ?_⟩
        rw [walkOk, hst, Bool.true_and]
        refine (((h₀.le le_rfl).trans h₁).trans h₂).mono ?_
        simp only [List.length_cons]
        nlinarith
      · have hst' : stepOk s n es c b a q = false := by simpa using hst
        rw [ite_eq_right hst] at h₁
        refine ⟨v₁, S₁, ?_⟩
        rw [walkOk, hst', Bool.false_and]
        refine ((h₀.le le_rfl).trans h₁).mono ?_
        simp only [List.length_cons]
        nlinarith

/-! ### The verifier -/

/-- **Correctness and running time of the Hamiltonian path verifier.** Let $x$ and $w$ be bit
lists. Start the verifier at its start label, with either value of its Boolean variable, with
$x$ on stack $\mathsf{X}$ and $w$ on stack $\mathsf{W}$ (as bit symbols, first bit on top) and
all other stacks empty. Then within $100(|x| + |w| + 1)^4$ steps it reaches the label
$\mathrm{yes}$ if the Hamiltonian path check accepts $x$ and $w$, and the label $\mathrm{no}$
otherwise.

The machine in fact takes quadratically many steps; the theorem states only the quartic bound. -/
theorem run (x w : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hX : St .X = x.map Sym.bit) (hW : St .W = w.map Sym.bit)
    (h0 : ∀ k, k ≠ .X → k ≠ .W → St k = []) :
    ∃ v' S', RunLe prog (100 * (x.length + w.length + 1) ^ 4) ⟨some start, v, St⟩
      ⟨some (if hamCheck x w then .yes else .no), v', S'⟩ := by
  set L := x.length + w.length + 1 with hL
  have hL1 : 1 ≤ L := by omega
  have hLL : L ≤ L * L := Nat.le_mul_self L
  have hL4 : L * L ≤ L ^ 4 := by
    calc L * L = L ^ 2 := (sq L).symm
      _ ≤ L ^ 4 := Nat.pow_le_pow_right hL1 (by omega)
  have hS : St .S = [] := h0 .S (by decide) (by decide)
  have hT : St .T = [] := h0 .T (by decide) (by decide)
  have hN : St .N = [] := h0 .N (by decide) (by decide)
  have hC : St .C = [] := h0 .C (by decide) (by decide)
  have hA : St .A = [] := h0 .A (by decide) (by decide)
  have hB : St .B = [] := h0 .B (by decide) (by decide)
  have hE : St .E = [] := h0 .E (by decide) (by decide)
  have hZ : St .Z = [] := h0 .Z (by decide) (by decide)
  have hR : St .R = [] := h0 .R (by decide) (by decide)
  have hQ : St .Q = [] := h0 .Q (by decide) (by decide)
  cases h₁ : readUnaryLength x with
  | none =>
      obtain ⟨v', S', r⟩ := readU_none (src := .X) (c := .S) (self := .rdS) (next := .rdT) rfl
        (by decide) x v St h₁ hX
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, h₁])]
      exact ⟨v', S', r.mono (by nlinarith)⟩
  | some p =>
  obtain ⟨s, r₁⟩ := p
  have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
  obtain ⟨v₁, run₁⟩ := readU_run (src := .X) (c := .S) (self := .rdS) (next := .rdT) rfl
    (by decide) s 0 r₁ v St (by rw [hX, hx₁]) (by simp [hS])
  set St₁ := update (update St .X (r₁.map Sym.bit)) .S (cnt (Sym.bit true) (s + 0)) with hSt₁
  have hl₁ : x.length = s + 1 + r₁.length := by rw [hx₁]; simp; omega
  cases h₂ : readUnaryLength r₁ with
  | none =>
      obtain ⟨v', S', r⟩ := readU_none (src := .X) (c := .T) (self := .rdT) (next := .rdN) rfl
        (by decide) r₁ v₁ St₁ h₂ (by simp [hSt₁])
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, h₁, h₂])]
      exact ⟨v', S', ((run₁.le le_rfl).trans r).mono (by nlinarith)⟩
  | some p =>
  obtain ⟨t, r₂⟩ := p
  have hx₂ := (readUnaryLength_eq_some_iff _ _ _).1 h₂
  obtain ⟨v₂, run₂⟩ := readU_run (src := .X) (c := .T) (self := .rdT) (next := .rdN) rfl
    (by decide) t 0 r₂ v₁ St₁ (by simp [hSt₁, hx₂]) (by simp [hSt₁, hT])
  set St₂ := update (update St₁ .X (r₂.map Sym.bit)) .T (cnt (Sym.bit true) (t + 0)) with hSt₂
  have hl₂ : r₁.length = t + 1 + r₂.length := by rw [hx₂]; simp; omega
  cases h₃ : readUnaryLength r₂ with
  | none =>
      obtain ⟨v', S', r⟩ := readU_none (src := .X) (c := .N) (self := .rdN) (next := .vE) rfl
        (by decide) r₂ v₂ St₂ h₃ (by simp [hSt₂])
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, Karp.decodeE, h₁, h₂, h₃])]
      exact ⟨v', S', (((run₁.le le_rfl).trans (run₂.le le_rfl)).trans r).mono (by nlinarith)⟩
  | some p =>
  obtain ⟨n, r₃⟩ := p
  have hx₃ := (readUnaryLength_eq_some_iff _ _ _).1 h₃
  obtain ⟨v₃, run₃⟩ := readU_run (src := .X) (c := .N) (self := .rdN) (next := .vE) rfl
    (by decide) n 0 r₃ v₂ St₂ (by simp [hSt₂, hx₃]) (by simp [hSt₂, hSt₁, hN])
  set St₃ := update (update St₂ .X (r₃.map Sym.bit)) .N (cnt (Sym.bit true) (n + 0)) with hSt₃
  have hl₃ : r₂.length = n + 1 + r₃.length := by rw [hx₃]; simp; omega
  obtain ⟨v₄, S₄, run₄, hF₄⟩ := valE_run r₃ [] v₃ St₃ (by simp [hSt₃])
    (by simp [hSt₃, hSt₂, hSt₁, hE])
  have run₀₃ := ((run₁.le le_rfl).trans (run₂.le le_rfl)).trans (run₃.le le_rfl)
  cases h₄ : Karp.decodeEs r₃ with
  | none =>
      simp only [h₄, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at run₄
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, Karp.decodeE, h₁, h₂, h₃, h₄])]
      exact ⟨v₄, S₄, (run₀₃.trans run₄).mono (by nlinarith)⟩
  | some es =>
  have hr₃ : Karp.edgeBits es = r₃ := Karp.edgeBits_of_decodeEs h₄
  simp only [h₄, Option.isSome_some, ↓reduceIte, forall_const, List.nil_append] at run₄ hF₄
  rw [hF₄] at run₄
  obtain ⟨v₅, run₅⟩ := mv_run (self := .vEb) (next := .vW) (a := .E) (b := .X) rfl (by decide)
    r₃.reverse v₄ (update (update St₃ .X []) .E (r₃.reverse.map Sym.bit)) (by simp)
  set St₅ := update (update (update (update St₃ .X []) .E (r₃.reverse.map Sym.bit)) .E []) .X
    ((r₃.reverse.map Sym.bit).reverse ++
      update (update St₃ .X []) .E (r₃.reverse.map Sym.bit) .X) with hSt₅
  obtain ⟨v₆, S₆, run₆, hF₆⟩ := valW_run w [] v₅ St₅ (by simp [hSt₅, hSt₃, hSt₂, hSt₁, hW])
    (by simp [hSt₅, hSt₃, hSt₂, hSt₁, hZ])
  have run₀₅ := (run₀₃.trans run₄).trans (run₅.le le_rfl)
  cases h₅ : decodeW w with
  | none =>
      simp only [h₅, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at run₆
      rw [hamCheck_of_decodeW x h₅]
      exact ⟨v₆, S₆, (run₀₅.trans run₆).mono (by simp only [List.length_reverse]; nlinarith)⟩
  | some p =>
  have hw₅ : encW p = w := encW_of_decodeW h₅
  simp only [h₅, Option.isSome_some, ↓reduceIte, forall_const, List.nil_append] at run₆ hF₆
  rw [hF₆] at run₆
  obtain ⟨v₇, run₇⟩ := mv_run (self := .vWb) (next := .loop) (a := .Z) (b := .W) rfl (by decide)
    w.reverse v₆ (update (update St₅ .W []) .Z (w.reverse.map Sym.bit)) (by simp)
  have e₇ : update (update (update (update St₅ .W []) .Z (w.reverse.map Sym.bit)) .Z []) .W
      ((w.reverse.map Sym.bit).reverse ++
        update (update St₅ .W []) .Z (w.reverse.map Sym.bit) .W) = lay es s t n 0 0 p := by
    funext k
    cases k <;> simp [hSt₅, hSt₃, hSt₂, hSt₁, lay, hr₃, hw₅, List.map_reverse, hC, hA, hB, hR,
      hQ]
  rw [e₇] at run₇
  have hpw : p.length ≤ w.length := hw₅ ▸ length_le_length_encW p
  obtain ⟨v₈, S₈, run₈⟩ := loop_run es s t n L (by omega) (by omega)
    (by rw [hr₃]; omega) p 0 0 v₇ (by rw [hw₅]; omega) (by omega)
  have hx : x = Path.encodeP s t n es := by
    rw [hx₁, hx₂, hx₃, ← hr₃]; rfl
  have hc : hamCheck x w = walkOk s t n es 0 0 p := by
    rw [hx, ← hw₅, hamCheck_encode, walkOk_eq]
  rw [hc]
  refine ⟨v₈, S₈, ((run₀₅.trans run₆).trans ((run₇.le le_rfl).trans run₈)).mono ?_⟩
  have hp1 : (p.length + 1) * (20 * L + 20) ≤ L * (20 * L + 20) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [List.length_reverse]
  nlinarith

end Cslib.Complexity.Karp.HamVerify
