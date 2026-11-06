/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.PathCorrect
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps
public import Mathlib.Tactic.Linarith

/-!
# The marking machine for PATH

A `TM2` component deciding `pathCheck` (`Cslib.Complexity.Path`), for the decider host
`Host.isPolyTime_decider`. The input `x` lies on `X` as `Sym.bit`s; the answer is pushed on the
`Bool` stack `O`.

* Parse: `s`, `t`, `n` in unary onto the counters `S`, `T`, `N` (`readS`, the parsed bits going to
  the junk stack `J`); reading `n` also pushes `n` cleared marks on `M`. A cut-off number writes
  `false` (`bad`).
* Validate: the rest must be an edge list (pairs of unary numbers); it is moved onto `E`, which
  reverses it (`val0`, `valU`, `valV`); a dangling half-pair or a cut-off number writes `false`.
* Marks: `M` holds one cell per vertex, vertex `0` on top. Walking to vertex `j` parks the cells
  `0, …, j - 1` on `P` (`walkS`, one step per unit of the counter); `setS` sets the mark on top,
  and `moveB P → M` puts the parked cells back. First the walk to `s` sets `initMarks n s`.
* Passes (`pass`, one per unit of `N`): move `E` back onto `X` (`ld`), then scan the edges in
  order (`edge`): read `u` and `v` onto `U` and `V`, moving their bits back to `E`; walk to `u`,
  read its mark and restore (`go1`, `back1`); if it is set, walk to `v`, set its mark and restore
  (`go2`, `back2`), else drain `V` (`drV`). A vertex past the last one is never found: its mark
  reads as clear and is never set, as in `markPass`.
* Answer: walk to `t` and push its mark (`false` past the last vertex) on `O` (`goT`).

`run`: from `start` with `x` on `X` and the other stacks empty, `prog` reaches `done` with
`O = [pathCheck x]` within `8 (|x| + 1)⁴` steps (quadratically many, in fact).
-/

@[expose] public section

namespace Cslib.Complexity.Path.Machine

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin
open Cslib.Complexity.SatVerifier (Sym)
open Cslib.Complexity.Karp (edgeBits decodeEs)

/-! ### The machine -/

/-- **Stacks of the PATH marking machine.** The PATH marking machine, run on an instance with
source $s$, target $t$ and $n$ vertices, has eleven stacks: the input stack $X$, the output stack
$O$, the stack $E$ of the edge bits (reversed between passes), the junk stack $J$, the counters
$S$, $T$ and $N$ for $s$, $t$ and $n$ ($N$ counts the passes left), the counters $U$ and $V$ for
the endpoints $u$ and $v$ of an arc, the mark stack $M$ (with the mark of vertex $0$ on top) and
the stack $P$ of parked marks. -/
inductive K | X | O | E | J | S | T | N | U | V | M | P
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .O, .E, .J, .S, .T, .N, .U, .V, .M, .P], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabets of the PATH marking machine.** The output stack $O$ of the PATH marking
machine holds Booleans, and every other stack holds symbols of the SAT verifier's symbol
alphabet. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Labels of the PATH marking machine.** For an instance with source $s$, target $t$, $n$
vertices and arcs $(u, v)$, the labels of the PATH marking machine are $\mathsf{rdS}$,
$\mathsf{rdT}$ and $\mathsf{rdN}$ (read $s$, $t$ and $n$); $\mathsf{val0}$, $\mathsf{valU}$ and
$\mathsf{valV}$ (validate the edge list: at a pair, inside $u$, inside $v$); $\mathsf{goS}$ and
$\mathsf{backS}$ (walk to $s$ and set its mark, then restore); $\mathsf{pass}$ (the pass loop),
$\mathsf{ld}$ (reload the edges) and $\mathsf{edge}$ (the edge loop); $\mathsf{rdU}$ and
$\mathsf{rdV}$ (read $u$ and $v$); $\mathsf{go1}$ and, for each bit $b$, $\mathsf{back1}(b)$
(walk to $u$, then restore holding its mark $b$); $\mathsf{go2}$ and $\mathsf{back2}$ (walk to
$v$ and set its mark, then restore); $\mathsf{drV}$ (drain the counter stack $V$);
$\mathsf{goT}$ (walk to $t$ and answer); $\mathsf{bad}$ (answer false); and $\mathsf{done}$
(halt). -/
inductive Lab | rdS | rdT | rdN | val0 | valU | valV | goS | backS | pass | ld | edge | rdU | rdV
  | go1 | back1 (b : Bool) | go2 | back2 | drV | goT | bad | done
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdS, .rdT, .rdN, .val0, .valU, .valV, .goS, .backS, .pass, .ld, .edge, .rdU,
    .rdV, .go1, .back1 false, .back1 true, .go2, .back2, .drV, .goT, .bad, .done], by decide⟩
  complete := fun x => by
    cases x with
    | back1 b => cases b <;> decide
    | _ => decide

/-- **Statements of the PATH marking machine.** The statements of the multi-stack Turing machine
(TM2) model whose stacks carry the stack alphabets $\Gamma$ of the marking machine, whose labels
are the labels of the marking machine, and whose internal state is a boolean. -/
abbrev Stmt := TM2.Stmt Γ Lab Bool

/-- **The counter unit of the PATH marking machine.** The unit symbol of the counters of the PATH
marking machine is the clause-end symbol $\mathrm{cl}$ of the SAT verifier's symbol alphabet. -/
abbrev one : Sym := .cl

/-- **The unary read instruction.** Given a stack $d$, an encoding $g$ of bits as symbols of $d$,
a list $ps$ of stack–symbol pairs and labels $\ell$ and $\ell'$, the instruction of the marking
machine that jumps to `bad` if $X$ is empty, and otherwise pops the top of $X$ as a bit $b$ (a
symbol that is not a bit counts as false) and pushes $g(b)$ on $d$; then, if $b$ is true, it
pushes $a$ on $q$ for each pair $(q, a)$ of $ps$, in order, and jumps to $\ell$, and if $b$ is
false it jumps to $\ell'$. Run at its own label $\ell$, it reads a unary number off $X$. -/
def readS (d : K) (g : Bool → Γ d) (ps : List (Σ k, Γ k)) (self next : Lab) : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .bad) <|
    .pop .X (fun _ o => bitOf Sym.bit? o) <| .push d g <| .branch id
      (pushAll ps (.goto fun _ => self)) (.goto fun _ => next)

/-- **Walk step of the PATH marking machine.** Given a counter stack $c$, a label $\ell$ and a
final statement $f$, the walk step pops the top of $c$. If $c$ was nonempty, it goes to $\ell$
after moving the top mark of the marks stack $M$, if there is one, onto the parked stack $P$:
the mark is popped, read as a bit (a symbol that is not a bit reads as false), and pushed on
$P$ as that bit. If $c$ was empty, it runs $f$. -/
def walkS (c : K) (self : Lab) (fin : Stmt) : Stmt :=
  .pop c (fun _ o => o.isSome) <| .branch id
    (.peek .M (fun _ o => o.isNone) <| .branch id (.goto fun _ => self) <|
      .pop .M (fun _ o => bitOf Sym.bit? o) <| .push .P (fun b => .bit b) <|
        .goto fun _ => self)
    fin

/-- **Mark-setting step.** For a label $\ell$, the statement of the marking machine that pops the
top cell of the mark stack $M$ and, if there was one, pushes the set mark (the bit true) onto $M$
in its place; in either case it then goes to $\ell$. -/
def setS (next : Lab) : Stmt :=
  .pop .M (fun _ o => o.isSome) <| .branch id
    (.push .M (fun _ => .bit true) <| .goto fun _ => next) (.goto fun _ => next)

/-- **The marking machine for PATH.** The multi-stack machine program whose input lies on the
stack $X$ and whose answer is pushed on the Boolean stack $O$. To read a unary number off $X$ onto
a stack $d$, it pops a bit off $X$ and pushes it on $d$, repeating while the bit is true and
moving on after the first false bit; an empty $X$ jumps to `bad`. To walk along a counter $c$, it
pops units off $c$ one at a time, each time moving the top mark of $M$ (if there is one) onto $P$,
until $c$ is empty. To restore, it moves the bits on top of $P$ back onto $M$ one at a time.

At `rdS`, `rdT` and `rdN` it reads $s$, $t$ and $n$ in turn off $X$ onto $J$, pushing a counter
unit on $S$, $T$ or $N$ respectively for each true bit, and at `rdN` also a cleared mark on $M$;
then it goes to `val0`. At `val0` it goes to `goS` if $X$ is empty, and otherwise reads two unary
numbers off $X$ onto $E$ (at `valU` and `valV`) and returns to `val0`. At `goS` it walks along $S$
and then sets the top mark of $M$ (if any); at `backS` it restores and goes to `pass`. At `pass`
it pops a unit off $N$ and goes to `ld`, or to `goT` if $N$ is empty. At `ld` it moves the bits on
top of $E$ onto $X$, then goes to `edge`. At `edge` it goes to `pass` if $X$ is empty, and
otherwise reads $u$ and $v$ off $X$ onto $E$ (at `rdU` and `rdV`), pushing a counter unit on $U$,
respectively $V$, for each true bit, and then goes to `go1`. At `go1` it walks along $U$ and reads
the top mark $b$ of $M$ (false if there is none); at `back1 b` it restores and goes to `go2` if $b$
is true and to `drV` otherwise. At `go2` it walks along $V$ and sets the top mark of $M$ (if any);
at `back2` it restores and goes to `edge`. At `drV` it empties $V$ and goes to `edge`. At `goT` it
walks along $T$, pushes the top mark of $M$ (false if there is none) on $O$ and goes to `done`. At
`bad` it pushes false on $O$ and goes to `done`. At `done` it halts. -/
def prog : Lab → Stmt
  | .rdS => readS .J Sym.bit [⟨.S, one⟩] .rdS .rdT
  | .rdT => readS .J Sym.bit [⟨.T, one⟩] .rdT .rdN
  | .rdN => readS .J Sym.bit [⟨.N, one⟩, ⟨.M, .bit false⟩] .rdN .val0
  | .val0 => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .goS)
      (.goto fun _ => .valU)
  | .valU => readS .E Sym.bit [] .valU .valV
  | .valV => readS .E Sym.bit [] .valV .val0
  | .goS => walkS .S .goS (setS .backS)
  | .backS => moveB .P .M Sym.bit? Sym.bit .backS .pass
  | .pass => decr .N .goT .ld
  | .ld => moveB .E .X Sym.bit? Sym.bit .ld .edge
  | .edge => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .pass)
      (.goto fun _ => .rdU)
  | .rdU => readS .E Sym.bit [⟨.U, one⟩] .rdU .rdV
  | .rdV => readS .E Sym.bit [⟨.V, one⟩] .rdV .go1
  | .go1 => walkS .U .go1 (.peek .M (fun _ o => bitOf Sym.bit? o) <| .goto fun b => .back1 b)
  | .back1 b => moveB .P .M Sym.bit? Sym.bit (.back1 b) (if b then .go2 else .drV)
  | .go2 => walkS .V .go2 (setS .back2)
  | .back2 => moveB .P .M Sym.bit? Sym.bit .back2 .edge
  | .drV => xfer .V [] .drV .edge
  | .goT => walkS .T .goT <| .peek .M (fun _ o => bitOf Sym.bit? o) <| .push .O id <|
      .goto fun _ => .done
  | .bad => .push .O (fun _ => false) <| .goto fun _ => .done
  | .done => .halt

/-- **Start label of the PATH marking machine.** The marking machine for PATH starts at the label
that reads the source vertex $s$, in unary, off the input. -/
def start : Lab := .rdS

/-! ### The algorithm, as the machine runs it -/

/-- **Setting the first mark.** For a list of booleans, the list obtained by setting its first
entry: the empty list is left unchanged, and a list $b :: r$ with first entry $b$ and remaining
entries $r$ becomes $\mathrm{true} :: r$. -/
def setHead : List Bool → List Bool
  | [] => []
  | _ :: r => true :: r

/-- **Setting an entry by splitting the list.** For every list $m$ of booleans and every natural
number $j$, the first $j$ entries of $m$ followed by the remaining entries with their first entry
set to true (the empty list stays empty) equal $m$ with entry $j$ set to true (which is $m$
itself when $j \ge |m|$). -/
theorem take_append_setHead : ∀ (m : List Bool) (j : ℕ),
    m.take j ++ setHead (m.drop j) = m.set j true
  | [], _ => by simp [setHead]
  | _ :: _, 0 => rfl
  | a :: m, j + 1 => by simp [take_append_setHead m j]

/-- **Reading the mark of vertex $j$.** Let $m$ be a list of Boolean marks and $j$ a natural
number. Drop the first $j$ marks of $m$ and write the rest as bit symbols; reading the top symbol
as a bit, with false when there is no top symbol, gives the entry of $m$ at position $j$ (counting
from $0$), or false when $j$ is at least the length of $m$. -/
theorem bitOf_drop (m : List Bool) (j : ℕ) :
    bitOf Sym.bit? ((m.drop j).map Sym.bit).head? = m.getD j false := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases m.drop j <;> rfl

/-- **Out-of-range arcs need no guard.** Let $m$ be a list of $n$ Boolean marks and let $u$, $v$
be natural numbers; write $m_u$ for the entry of $m$ at position $u$ (counting from $0$), taken to
be false when $u \ge n$. If $u < n$, $v < n$ and $m_u$ is true, set position $v$ of $m$ to true,
and otherwise keep $m$; the result is the same as setting position $v$ of $m$ to true when $m_u$ is
true and keeping $m$ otherwise.

Setting a position $v \ge n$ leaves the list unchanged, so the machine, which reads the mark of $u$
and then sets the mark of $v$, ignores an arc with an end past the last vertex, as the marking
algorithm does. -/
theorem arc_eq {n u v : ℕ} {m : List Bool} (h : m.length = n) :
    (if u < n ∧ v < n ∧ m.getD u false = true then m.set v true else m) =
      if m.getD u false = true then m.set v true else m := by
  by_cases hu : m.getD u false = true
  · have hun : u < n := by
      by_contra h'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hu
      simp at hu
    by_cases hv : v < n
    · rw [ite_eq_left ⟨hun, hv, hu⟩, ite_eq_left hu]
    · rw [ite_eq_right fun h' => hv h'.2.1, ite_eq_left hu,
        List.set_eq_of_length_le (show m.length ≤ v by omega)]
  · rw [ite_eq_right fun h' => hu h'.2.2, ite_eq_right hu]

/-- **Initial marks by setting one entry.** For all natural numbers $n$ and $s$, setting entry $s$
of the list of $n$ copies of false to true (which changes nothing when $s \ge n$) gives the
initial marks of $n$ vertices from $s$: the list of length $n$ whose entry $i$ is true exactly
when $i = s$. -/
theorem set_replicate (n s : ℕ) : (List.replicate n false).set s true = initMarks n s := by
  refine List.ext_getElem (by simp [initMarks]) fun i h₁ h₂ => ?_
  simp only [List.getElem_set, List.getElem_replicate, initMarks, List.getElem_map,
    List.getElem_range]
  by_cases h : s = i <;> simp [h, Ne.symm]

/-- **A cleared mark or nothing reads as cleared.** For every decidable proposition $p$, the
optional mark that is a cleared mark (false) when $p$ holds and absent otherwise, read with
default false, is false. -/
theorem getD_ite (p : Prop) [Decidable p] :
    (if p then some false else none).getD false = false := by
  split <;> rfl

/-- **A pass sets no mark when none is set.** For all natural numbers $n$ and $k$ and every list
$es$ of arcs of natural numbers, one pass of the marking algorithm with $n$ vertices over $es$
(Mark Pass) maps the list of $k$ cleared marks to itself. -/
theorem markPass_replicate (n k : ℕ) : ∀ es : List (ℕ × ℕ),
    markPass n es (List.replicate k false) = List.replicate k false
  | [] => rfl
  | (u, v) :: es => by
      simp only [markPass, List.getD_eq_getElem?_getD, List.getElem?_replicate, getD_ite]
      simpa using markPass_replicate n k es

/-- **The marking algorithm reads the mark of the target.** If a bit string $x$ parses as a PATH
instance with source $s$, target $t$, $n$ vertices and edge list $es$, then the marking algorithm
on $x$ returns the mark of $t$ in the reach marks of $s$ (the marks after $n$ marking passes over
$es$, starting from the marks on $0, \dots, n - 1$ with only $s$ marked, and none if $s \ge n$),
where a vertex $t \ge n$ counts as unmarked.

So the checks $s < n$ and $t < n$ of the marking algorithm are implied: a vertex $t \ge n$ has no
mark, and for $s \ge n$ every mark stays cleared. -/
theorem pathCheck_eq {x : List Bool} {s t n : ℕ} {es : List (ℕ × ℕ)}
    (h : decodeP x = some (s, t, n, es)) : pathCheck x = (reachMarks n s es).getD t false := by
  rw [pathCheck, h]
  dsimp only
  by_cases hs : s < n
  · by_cases ht : t < n
    · simp [hs, ht]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [reachMarks, Path.length_iterate_markPass]; simp [initMarks]; omega)]
      simp [ht]
  · have hi : initMarks n s = List.replicate n false := by
      rw [← set_replicate, List.set_eq_of_length_le (by simp; omega)]
    rw [reachMarks, hi, Function.iterate_fixed (markPass_replicate n n es)]
    simp [hs, List.getD_eq_getElem?_getD, List.getElem?_replicate, getD_ite]

/-! ### Frames -/

/-- **Agreement off a set of stacks.** For a list $A$ of stacks of the marking machine and two
contents $S$, $S'$ of its stacks, $S'$ agrees with $S$ off $A$ when every stack not in $A$ holds
the same list in $S'$ as in $S$. -/
def Fr (A : List K) (S S' : ∀ k, List (Γ k)) : Prop := ∀ q, q ∉ A → S' q = S q

/-- **Frames are reflexive.** For every list $A$ of stacks of the marking machine and every
assignment $S$ of contents to its stacks, $S$ agrees with itself off $A$. -/
theorem Fr.refl (A : List K) (S : ∀ k, List (Γ k)) : Fr A S S := fun _ _ => rfl

/-- **Frames compose.** Let $A$, $B$, $C$ be lists of stacks such that every stack in $A$ or in
$B$ is in $C$. If stacks $S_2$ agree with $S_1$ on every stack outside $A$, and $S_3$ agree with
$S_2$ on every stack outside $B$, then $S_3$ agree with $S_1$ on every stack outside $C$. -/
theorem Fr.trans {A B C : List K} {S₁ S₂ S₃ : ∀ k, List (Γ k)} (h₁ : Fr A S₁ S₂)
    (h₂ : Fr B S₂ S₃) (hA : ∀ q ∈ A, q ∈ C) (hB : ∀ q ∈ B, q ∈ C) : Fr C S₁ S₃ := fun q hq => by
  rw [h₂ q fun h => hq (hB q h), h₁ q fun h => hq (hA q h)]

/-- **Updating a framed stack preserves the frame.** Let $A$ be a list of stacks of the PATH
marking machine, and let $S$ and $S'$ be stack contents such that $S'$ agrees with $S$ on every
stack outside $A$. Then for every stack $k \in A$ and every list $l$ over the alphabet of $k$,
the contents obtained from $S'$ by replacing stack $k$ with $l$ still agree with $S$ on every
stack outside $A$. -/
theorem Fr.upd {A : List K} {S S' : ∀ k, List (Γ k)} (h : Fr A S S') {k : K} (hk : k ∈ A)
    (l : List (Γ k)) : Fr A S (update S' k l) := fun q hq => by
  rw [update_of_ne (show q ≠ k from fun e => hq (e ▸ hk)), h q hq]

/-- **The frame of a read.** Let $d$ be a stack of the marking machine, $ps$ a list of pairs of a
stack and a symbol, $i$ a natural number, and $S$, $S'$ two contents of the stacks. Suppose every
stack $q$ other than the input $X$ and $d$ holds in $S'$ the list it holds in $S$ with $i$ further
copies of the symbol of the first entry for $q$ in $ps$ pushed on top (and unchanged if $ps$ has
no entry for $q$). Then $S'$ agrees with $S$ on every stack other than $X$, $d$ and the stacks
that have an entry in $ps$. -/
theorem fr_addU {d : K} {ps : List (Σ k, Γ k)} {i : ℕ} {S S' : ∀ k, List (Γ k)}
    (h : ∀ q, q ≠ .X → q ≠ d → S' q = addU ps i S q) : Fr (.X :: d :: ps.keys) S S' :=
  fun q hq => by
    simp only [List.mem_cons, not_or] at hq
    rw [h q hq.1 hq.2.1, addU_of_not_mem hq.2.2]

/-! ### Runs of the components -/

/-- **Reading a unary number.** Let $d$ be a stack other than $X$, let $g$ encode bits as symbols
of $d$, and let $ps$ be a list of stack–symbol pairs whose stacks are distinct and differ from $X$
and $d$. Suppose the instruction of the marking machine at a label $\ell$ is the unary read off
$X$ onto $d$ through $g$ that pushes $ps$ for each true bit, repeats at $\ell$ and continues at
$\ell'$. If $X$ holds, as bit symbols, $k$ true bits, then a false bit, then a bit list $r$, then
in exactly $k + 1$ steps the machine goes from $\ell$, with any flag, to $\ell'$; afterwards $X$
holds $r$, $d$ has received $k$ copies of $g(\mathrm{true})$ and then $g(\mathrm{false})$ on top,
each stack $q$ with a pair $(q, a)$ in $ps$ has received $k$ copies of $a$ on top, and every
other stack is unchanged. -/
theorem readS_some {d : K} {g : Bool → Γ d} {ps : List (Σ k, Γ k)} {self next : Lab}
    (hp : prog self = readS d g ps self next) (hdX : d ≠ .X) (hps : ps.NodupKeys)
    (hX : K.X ∉ ps.keys) (hd : d ∉ ps.keys) :
    ∀ (k : ℕ) (r : List Bool) (v : Bool) (St : ∀ k, List (Γ k)),
      St .X = (List.replicate k true ++ false :: r).map Sym.bit →
      ∃ v' S', Run prog (k + 1) ⟨some self, v, St⟩ ⟨some next, v', S'⟩ ∧
        S' .X = r.map Sym.bit ∧ S' d = g false :: (cnt (g true) k ++ St d) ∧
        ∀ q, q ≠ .X → q ≠ d → S' q = addU ps k St q := by
  intro k
  induction k with
  | zero =>
      intro r v St hSX
      refine ⟨false, update (update St .X (r.map Sym.bit)) d (g false :: St d), Run.single ?_,
        by simp [update_of_ne hdX.symm], by simp, fun q h1 h2 => by
          simp [update_of_ne h1, update_of_ne h2, addU_zero]⟩
      simp [hp, readS, TM2.stepAux, hSX, bitOf, Sym.bit?, update_of_ne hdX]
  | succ k ih =>
      intro r v St hSX
      set St₁ := addU ps 1 (update (update St .X ((List.replicate k true ++ false :: r).map
        Sym.bit)) d (g true :: St d)) with hSt₁
      have hstep : TM2.step prog ⟨some self, v, St⟩ = some ⟨some self, true, St₁⟩ := by
        simp [TM2.step, hp, readS, TM2.stepAux, hSX, bitOf, Sym.bit?, update_of_ne hdX,
          stepAux_pushAll hps, hSt₁, List.replicate_succ]
      obtain ⟨v', S', h, h1, h2, h3⟩ := ih r true St₁
        (by rw [hSt₁, addU_of_not_mem hX, update_of_ne hdX.symm, update_self])
      refine ⟨v', S', Run.head hstep h, h1, ?_, fun q q1 q2 => ?_⟩
      · rw [h2, hSt₁, addU_of_not_mem hd, update_self]
        simp [cnt, List.replicate_succ']
      · rw [h3 q q1 q2, hSt₁, addU_addU]
        simp only [addU, update_of_ne q1, update_of_ne q2]

/-- **Reading a cut-off unary number.** Let $d$ be a stack other than $X$ and $O$, let $g$ encode
bits as symbols of $d$, and let $ps$ be a list of stack–symbol pairs whose stacks are distinct and
differ from $X$ and $O$. Suppose the instruction of the marking machine at a label $\ell$ is the
unary read off $X$ onto $d$ through $g$ that pushes $ps$ for each true bit, repeats at $\ell$ and
continues at $\ell'$. If a bit list $l$ has no unary length prefix (every bit of $l$ is true) and
$X$ holds $l$ as bit symbols, then from $\ell$, with any flag, the machine reaches the label `bad`
within $|l| + 1$ steps, leaving the output stack $O$ unchanged. -/
theorem readS_none {d : K} {g : Bool → Γ d} {ps : List (Σ k, Γ k)} {self next : Lab}
    (hp : prog self = readS d g ps self next) (hdX : d ≠ .X) (hps : ps.NodupKeys)
    (hX : K.X ∉ ps.keys) (hdO : d ≠ .O) (hO : K.O ∉ ps.keys) :
    ∀ (l : List Bool) (v : Bool) (St : ∀ k, List (Γ k)), readUnaryLength l = none →
      St .X = l.map Sym.bit →
      ∃ v' S', RunLe prog (l.length + 1) ⟨some self, v, St⟩ ⟨some .bad, v', S'⟩ ∧
        S' .O = St .O
  | [], v, St, _, hSX => ⟨true, St, (Run.single (by simp [hp, readS, TM2.stepAux, hSX])).le
      (by simp), rfl⟩
  | false :: l, _, _, h, _ => by simp [readUnaryLength] at h
  | true :: l, v, St, h, hSX => by
      set St₁ := addU ps 1 (update (update St .X (l.map Sym.bit)) d (g true :: St d)) with hSt₁
      have hstep : TM2.step prog ⟨some self, v, St⟩ = some ⟨some self, true, St₁⟩ := by
        simp [TM2.step, hp, readS, TM2.stepAux, hSX, bitOf, Sym.bit?, update_of_ne hdX,
          stepAux_pushAll hps, hSt₁]
      obtain ⟨v', S', h', hO'⟩ := readS_none hp hdX hps hX hdO hO l true St₁
        (by simpa [readUnaryLength] using h)
        (by rw [hSt₁, addU_of_not_mem hX, update_of_ne hdX.symm, update_self])
      obtain ⟨n', hn', h'⟩ := h'
      refine ⟨v', S', ⟨n' + 1, by simp; omega, Run.head hstep h'⟩, ?_⟩
      rw [hO', hSt₁, addU_of_not_mem hO, update_of_ne hdO.symm, update_of_ne (by decide)]

/-- **Restoring the parked marks.** Suppose the instruction of the marking machine at a label
$\ell$ moves the bits on top of $P$ onto $M$ one at a time, repeating at $\ell$ and continuing at
$\ell'$ once $P$ is empty or its top is not a bit. If $P$ holds the reverse of a bit list $p$ and
$M$ holds a bit list $q$, both as bit symbols, then in exactly $|p| + 1$ steps the machine goes
from $\ell$, with any flag, to $\ell'$, leaving $P$ empty, $M$ holding $p$ followed by $q$, and
every other stack unchanged. -/
theorem restore_run {self next : Lab} (hp : prog self = moveB .P .M Sym.bit? Sym.bit self next)
    (pre post : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hP : St .P = pre.reverse.map Sym.bit) (hM : St .M = post.map Sym.bit) :
    ∃ v' S', Run prog (pre.length + 1) ⟨some self, v, St⟩ ⟨some next, v', S'⟩ ∧ S' .P = [] ∧
      S' .M = (pre ++ post).map Sym.bit ∧ Fr [.P, .M] St S' := by
  obtain ⟨v', S', h, hP', hM', hF⟩ := moveB_run (M := prog) hp (show K.P ≠ K.M by decide)
    pre.reverse (pre.reverse.map Sym.bit) [] v St (by simp [hP])
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
  refine ⟨v', S', by simpa using h, hP', by simp [hM', hM, List.map_reverse], fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  exact hF q hq.1 hq.2

/-- **A walk step with an exhausted counter.** Let $c$ be a stack, $\mathit{self}$ a label,
$\mathit{fin}$ a statement and $S$ stacks in which $c$ is empty. For every internal state $v$,
executing from $v$ and $S$ the walk step counted by $c$ that loops at $\mathit{self}$ and
finishes with $\mathit{fin}$ gives the same result as executing $\mathit{fin}$ from internal
state false and the same stacks $S$. -/
theorem stepAux_walkS_nil {c : K} {self : Lab} {fin : Stmt} {S : ∀ k, List (Γ k)}
    (hc : S c = []) (v : Bool) : TM2.stepAux (walkS c self fin) v S = TM2.stepAux fin false S := by
  have : update S c [] = S := by rw [← hc, update_eq_self]
  simp [walkS, TM2.stepAux, hc, this]

/-- **Walking along the marks of the PATH marking machine.** Let $c$ be a stack other than the
marks stack $M$ and the parked stack $P$, let $u$ be a symbol of the alphabet of $c$, and let
$\ell$ be a label at which the program is the walk step counted by $c$ that returns to $\ell$
(with some final statement). Let $j$ be a natural number, $p$ and $q$ lists of bits, $v$ a
Boolean, and $S$ stack contents in which $c$ holds exactly $j$ copies of $u$, $M$ holds $q$ as
bit symbols, and $P$ holds the reverse of $p$ as bit symbols. Then there are a Boolean $v'$ and
stack contents $S'$ such that the machine goes in exactly $j$ steps from label $\ell$ with state
$v$ and stacks $S$ to label $\ell$ with state $v'$ and stacks $S'$, where $c$ is empty in $S'$,
$M$ holds $q$ with its first $j$ entries dropped, $P$ holds the reverse of the concatenation of
$p$ with the first $j$ entries of $q$, all as bit symbols, and $S'$ agrees with $S$ on every
stack other than $c$, $M$ and $P$. -/
theorem walk_run {c : K} {self : Lab} {fin : Stmt} (hp : prog self = walkS c self fin)
    (hcM : c ≠ .M) (hcP : c ≠ .P) (u : Γ c) : ∀ (j : ℕ) (pre post : List Bool) (v : Bool)
    (St : ∀ k, List (Γ k)), St c = cnt u j → St .M = post.map Sym.bit →
    St .P = pre.reverse.map Sym.bit →
    ∃ v' S', Run prog j ⟨some self, v, St⟩ ⟨some self, v', S'⟩ ∧ S' c = [] ∧
      S' .M = (post.drop j).map Sym.bit ∧ S' .P = (pre ++ post.take j).reverse.map Sym.bit ∧
      Fr [c, .M, .P] St S'
  | 0, _, _, v, St, hc, hM, hP => ⟨v, St, Run.zero _, hc, by simpa using hM, by simpa using hP,
      Fr.refl _ _⟩
  | j + 1, pre, [], v, St, hc, hM, hP => by
      rw [cnt_succ] at hc
      have r₁ : Run prog 1 ⟨some self, v, St⟩ ⟨some self, true, update St c (cnt u j)⟩ :=
        Run.single (by simp [hp, walkS, TM2.stepAux, hc, hM, update_of_ne hcM.symm])
      obtain ⟨v', S', h, h1, h2, h3, h4⟩ := walk_run hp hcM hcP u j pre [] true
        (update St c (cnt u j)) (by simp)
        (by rw [update_of_ne hcM.symm, hM]) (by rw [update_of_ne hcP.symm, hP])
      exact ⟨v', S', (r₁.trans h).of_eq (by omega), h1, by simpa using h2, by simpa using h3,
        Fr.trans ((Fr.refl _ _).upd (by simp) _) h4 (fun _ h => h) fun _ h => h⟩
  | j + 1, pre, b :: post, v, St, hc, hM, hP => by
      rw [cnt_succ] at hc
      have r₁ : Run prog 1 ⟨some self, v, St⟩ ⟨some self, b, update (update (update St c
          (cnt u j)) .M (post.map Sym.bit)) .P (.bit b :: St .P)⟩ :=
        Run.single (by
          simp [hp, walkS, TM2.stepAux, hc, hM, update_of_ne hcM.symm, update_of_ne hcP.symm,
            bitOf, Sym.bit?])
      obtain ⟨v', S', h, h1, h2, h3, h4⟩ := walk_run hp hcM hcP u j (pre ++ [b]) post b
        (update (update (update St c (cnt u j)) .M (post.map Sym.bit)) .P (.bit b :: St .P))
        (by simp [update_of_ne hcM, update_of_ne hcP]) (by simp)
        (by simp [hP])
      exact ⟨v', S', (r₁.trans h).of_eq (by omega), h1, by simpa using h2, by simpa using h3,
        Fr.trans ((((Fr.refl _ _).upd (by simp) _).upd (by simp) _).upd (by simp) _) h4
          (fun _ h => h) fun _ h => h⟩

/-- **Effect of the mark-setting step.** Let $\ell$ be a label, $v$ an internal state and $S$
stacks whose mark stack $M$ holds the bits of a list $l$ of booleans. Executing the mark-setting
step to $\ell$ from internal state $v$ and stacks $S$ ends at label $\ell$ with some internal
state and the stacks $S$ with $M$ replaced by the bits of $l$ with its first entry set to true
(the empty list stays empty); every other stack is unchanged. -/
theorem stepAux_setS (next : Lab) (l : List Bool) (v : Bool) (S : ∀ k, List (Γ k))
    (hM : S .M = l.map Sym.bit) : ∃ v', TM2.stepAux (setS next) v S =
      ⟨some next, v', update S .M ((setHead l).map Sym.bit)⟩ := by
  cases l <;> simp [setS, TM2.stepAux, hM, setHead]

/-- **Walking to a vertex and setting its mark.** Let $c$ be a stack other than the mark stack $M$
and the parking stack $P$, and let $\mathit{self}$, $\mathit{back}$, $\mathit{next}$ be labels
such that the marking machine at $\mathit{self}$ is the walk step counted by $c$ that loops at
$\mathit{self}$ and finishes with the mark-setting step to $\mathit{back}$, and at
$\mathit{back}$ it moves the bit block of $P$ onto $M$, looping at $\mathit{back}$ and then
going to $\mathit{next}$. Let $S$ be stacks in which $c$ holds the counter value $j$ (for some
unit symbol), $M$ holds the bits of a list $m$ of booleans, and $P$ is empty. Then from label
$\mathit{self}$ with stacks $S$ and any internal state, the machine reaches label
$\mathit{next}$ in at most $2j + 2$ steps, with some internal state and stacks $S'$ such that
$c$ and $P$ are empty, $M$ holds the bits of $m$ with entry $j$ set to true (unchanged when
$j \ge |m|$), and $S'$ agrees with $S$ on every stack other than $c$, $M$ and $P$. -/
theorem setW_run {c : K} {self back next : Lab} (hp : prog self = walkS c self (setS back))
    (hb : prog back = moveB .P .M Sym.bit? Sym.bit back next) (hcM : c ≠ .M) (hcP : c ≠ .P)
    (u : Γ c) (j : ℕ) (m : List Bool) (v : Bool) (St : ∀ k, List (Γ k)) (hc : St c = cnt u j)
    (hM : St .M = m.map Sym.bit) (hP : St .P = []) :
    ∃ v' S', RunLe prog (2 * j + 2) ⟨some self, v, St⟩ ⟨some next, v', S'⟩ ∧ S' c = [] ∧
      S' .M = (m.set j true).map Sym.bit ∧ S' .P = [] ∧ Fr [c, .M, .P] St S' := by
  obtain ⟨v₁, S₁, r₁, hc₁, hM₁, hP₁, hF₁⟩ := walk_run hp hcM hcP u j [] m v St hc hM
    (by simp [hP])
  obtain ⟨v₂, h₂⟩ := stepAux_setS back (m.drop j) false S₁ hM₁
  have r₂ : Run prog 1 ⟨some self, v₁, S₁⟩
      ⟨some back, v₂, update S₁ .M ((setHead (m.drop j)).map Sym.bit)⟩ :=
    Run.single (by rw [hp, stepAux_walkS_nil hc₁, h₂])
  obtain ⟨v₃, S₃, r₃, hP₃, hM₃, hF₃⟩ := restore_run hb (m.take j) (setHead (m.drop j)) v₂
    (update S₁ .M ((setHead (m.drop j)).map Sym.bit))
    (by rw [update_of_ne (by decide), hP₁]; simp) (by rw [update_self])
  refine ⟨v₃, S₃, ((r₁.trans r₂).trans r₃).le ?_, ?_, by rw [hM₃, take_append_setHead], hP₃,
    Fr.trans (hF₁.upd (by simp) _) hF₃ (fun _ h => h) (by simp)⟩
  · have := List.length_take_le j m
    omega
  · rw [hF₃ c (by simp [hcM, hcP]), update_of_ne hcM, hc₁]

/-- **Reading the mark of a vertex.** Let $u \in \mathbb{N}$ and let $m$ be a list of marks.
Start the marking machine at the label `go1`, with any flag, from stacks on which $U$ holds $u$
counter units, $M$ holds $m$ as bit symbols and $P$ is empty. Then within $2u + 2$ steps it
reaches `go2` if the mark of vertex $u$ in $m$ is set and `drV` otherwise (a vertex past the end
of $m$ counts as unmarked), with $U$ and $P$ empty, $M$ holding $m$ again, and every other
stack unchanged. -/
theorem readW_run (u : ℕ) (m : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hU : St .U = cnt one u) (hM : St .M = m.map Sym.bit) (hP : St .P = []) :
    ∃ v' S', RunLe prog (2 * u + 2) ⟨some .go1, v, St⟩
      ⟨some (if m.getD u false then .go2 else .drV), v', S'⟩ ∧ S' .U = [] ∧
      S' .M = m.map Sym.bit ∧ S' .P = [] ∧ Fr [.U, .M, .P] St S' := by
  obtain ⟨v₁, S₁, r₁, hU₁, hM₁, hP₁, hF₁⟩ := walk_run (self := .go1) rfl (by decide)
    (by decide) one u [] m v St hU hM (by simp [hP])
  have r₂ : Run prog 1 ⟨some .go1, v₁, S₁⟩
      ⟨some (.back1 (m.getD u false)), m.getD u false, S₁⟩ :=
    Run.single (by rw [prog, stepAux_walkS_nil hU₁]; simp only [TM2.stepAux, hM₁, bitOf_drop])
  obtain ⟨v₃, S₃, r₃, hP₃, hM₃, hF₃⟩ := restore_run (self := .back1 (m.getD u false)) rfl
    (m.take u) (m.drop u) _ S₁ (by simp [hP₁]) hM₁
  refine ⟨v₃, S₃, ((r₁.trans r₂).trans r₃).le ?_, by rw [hF₃ .U (by decide), hU₁],
    by rw [hM₃, List.take_append_drop], hP₃, Fr.trans hF₁ hF₃ (fun _ h => h) (by decide)⟩
  have := List.length_take_le u m
  omega

/-- **Validation phase of the PATH marking machine.** Let $w$ be a list of bits, $v$ a Boolean
and $S$ stack contents whose input stack $X$ holds $w$ as bit symbols. Then there are a Boolean
$v'$ and stack contents $S'$ such that, in at most $2|w| + 1$ steps, the machine goes from the
validation label (at a pair) with state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at the
label that walks to the source vertex if $w$ decodes as an edge list, and at the label that
answers false otherwise. The output stack $O$ of $S'$ equals that of $S$. Moreover, if $w$
decodes as an edge list, then $X$ is empty in $S'$, the edge stack $E$ of $S'$ is the reverse
of $w$ as bit symbols followed by the old contents of $E$, and $S'$ agrees with $S$ on every
stack other than $X$ and $E$. -/
theorem val_run : ∀ (w : List Bool) (v : Bool) (St : ∀ k, List (Γ k)),
    St .X = w.map Sym.bit →
    ∃ v' S', RunLe prog (2 * w.length + 1) ⟨some .val0, v, St⟩
      ⟨some (if (decodeEs w).isSome then .goS else .bad), v', S'⟩ ∧ S' .O = St .O ∧
      ((decodeEs w).isSome → S' .X = [] ∧ S' .E = w.reverse.map Sym.bit ++ St .E ∧
        Fr [.X, .E] St S') := by
  intro w
  induction hL : w.length using Nat.strong_induction_on generalizing w with
  | _ L ih =>
  intro v St hX
  subst hL
  by_cases hw : w = []
  · subst hw
    refine ⟨true, St, (Run.single ?_).le (by simp), rfl,
      fun _ => ⟨by simpa using hX, by simp, Fr.refl _ _⟩⟩
    simp [prog, TM2.stepAux, hX, Karp.decodeEs_nil]
  have r₀ : Run prog 1 ⟨some .val0, v, St⟩ ⟨some .valU, false, St⟩ := Run.single (by
    cases w with
    | nil => exact absurd rfl hw
    | cons b w => simp [prog, TM2.stepAux, hX])
  have hlen : 1 ≤ w.length := by
    cases w with
    | nil => exact absurd rfl hw
    | cons => simp
  cases h₁ : readUnaryLength w with
  | none =>
      obtain ⟨v₁, S₁, r₁, hO₁⟩ := readS_none (self := .valU) rfl (by decide) List.nodupKeys_nil
        (by decide) (by decide) (by decide) w false St h₁ hX
      rw [Karp.decodeEs_of_none hw h₁]
      exact ⟨v₁, S₁, ((r₀.le le_rfl).trans r₁).mono (by omega), hO₁, by simp⟩
  | some p =>
      obtain ⟨u, w₁⟩ := p
      have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      obtain ⟨v₁, S₁, r₁, hX₁, hE₁, hF₁⟩ := readS_some (self := .valU) rfl (by decide)
        List.nodupKeys_nil (by decide) (by decide) u w₁ false St (by rw [hX, hx₁])
      have hG₁ := fr_addU hF₁
      have hl₁ : w.length = u + 1 + w₁.length := by rw [hx₁]; simp; omega
      cases h₂ : readUnaryLength w₁ with
      | none =>
          obtain ⟨v₂, S₂, r₂, hO₂⟩ := readS_none (self := .valV) rfl (by decide)
            List.nodupKeys_nil (by decide) (by decide) (by decide) w₁ v₁ S₁ h₂ hX₁
          rw [Karp.decodeEs_of_some_none h₁ h₂]
          refine ⟨v₂, S₂, (((r₀.le le_rfl).trans (r₁.le le_rfl)).trans r₂).mono (by omega),
            by rw [hO₂, hG₁ .O (by decide)], by simp⟩
      | some q =>
          obtain ⟨v', w₂⟩ := q
          have hx₂ := (readUnaryLength_eq_some_iff _ _ _).1 h₂
          obtain ⟨v₂, S₂, r₂, hX₂, hE₂, hF₂⟩ := readS_some (self := .valV) rfl (by decide)
            List.nodupKeys_nil (by decide) (by decide) v' w₂ v₁ S₁ (by rw [hX₁, hx₂])
          have hG₂ := fr_addU hF₂
          have hl₂ : w₁.length = v' + 1 + w₂.length := by rw [hx₂]; simp; omega
          obtain ⟨v₃, S₃, r₃, hO₃, hF₃⟩ := ih w₂.length (by omega) w₂ rfl v₂ S₂ hX₂
          rw [Karp.decodeEs_of_some_some h₁ h₂, Option.isSome_map]
          refine ⟨v₃, S₃, ((((r₀.le le_rfl).trans (r₁.le le_rfl)).trans (r₂.le le_rfl)).trans
            r₃).mono (by omega), by rw [hO₃, hG₂ .O (by decide), hG₁ .O (by decide)],
            fun h => ?_⟩
          obtain ⟨hX₃, hE₃, hG₃⟩ := hF₃ h
          refine ⟨hX₃, ?_, Fr.trans hG₁ (Fr.trans (C := [.X, .E]) hG₂ hG₃ (by decide) (by decide))
            (by decide) (by decide)⟩
          rw [hE₃, hE₂, hE₁, hx₁, hx₂]
          simp [cnt]

/-- **The edge loop of a pass.** Let $n$ be a natural number, $es$ a list of arcs $(u, w)$ of
natural numbers and $m$ a list of $n$ Boolean marks. Encode an arc $(u, w)$ by $u$ ones, a zero,
$w$ ones and a zero, and $es$ by the concatenation of the codes of its arcs; let $\ell$ be the
length of this code. Suppose the marking machine is at the edge-loop label, in any internal state,
with stacks $S$ such that the input stack $X$ holds the code of $es$ and the mark stack $M$ holds
$m$ (vertex $0$ on top), as bit symbols, and the parked-mark stack $P$ and the arc counters $U$
and $V$ are empty. Then within $4\ell + 1$ steps it reaches the pass-loop label with stacks $S'$
in which $X$ is empty, the edge stack $E$ holds the code of $es$ in reverse order on top of its
contents in $S$, $M$ holds the marks that one pass of the marking algorithm with $n$ vertices over
$es$ (Mark Pass) produces from $m$, and $P$, $U$, $V$ are empty; every stack other than $X$, $E$,
$M$, $U$, $V$ and $P$ holds the same list in $S'$ as in $S$. -/
theorem edges_run (n : ℕ) : ∀ (es : List (ℕ × ℕ)) (m : List Bool) (v : Bool)
    (St : ∀ k, List (Γ k)), m.length = n → St .X = (edgeBits es).map Sym.bit →
    St .M = m.map Sym.bit → St .P = [] → St .U = [] → St .V = [] →
    ∃ v' S', RunLe prog (4 * (edgeBits es).length + 1) ⟨some .edge, v, St⟩
      ⟨some .pass, v', S'⟩ ∧ S' .X = [] ∧ S' .E = (edgeBits es).reverse.map Sym.bit ++ St .E ∧
      S' .M = (markPass n es m).map Sym.bit ∧ S' .P = [] ∧ S' .U = [] ∧ S' .V = [] ∧
      Fr [.X, .E, .M, .U, .V, .P] St S'
  | [], m, v, St, _, hX, hM, hP, hU, hV => by
      refine ⟨true, St, (Run.single ?_).le (by simp), by simpa [edgeBits] using hX,
        by simp [edgeBits], by simpa [markPass] using hM, hP, hU, hV, Fr.refl _ _⟩
      simp [prog, TM2.stepAux, hX, edgeBits]
  | (u, w) :: es, m, v, St, hm, hX, hM, hP, hU, hV => by
      have hb : edgeBits ((u, w) :: es) =
          List.replicate u true ++ false :: (List.replicate w true ++ false :: edgeBits es) := by
        simp [edgeBits]
      rw [hb] at hX ⊢
      have r₀ : Run prog 1 ⟨some .edge, v, St⟩ ⟨some .rdU, false, St⟩ :=
        Run.single (by cases u <;> simp [prog, TM2.stepAux, hX])
      obtain ⟨v₁, S₁, r₁, hX₁, hE₁, hF₁⟩ := readS_some (self := .rdU) rfl (by decide)
        (single_nodupKeys _) (by decide) (by decide) u _ false St hX
      have hG₁ := fr_addU hF₁
      obtain ⟨v₂, S₂, r₂, hX₂, hE₂, hF₂⟩ := readS_some (self := .rdV) rfl (by decide)
        (single_nodupKeys _) (by decide) (by decide) w _ v₁ S₁ hX₁
      have hG₂ := fr_addU hF₂
      have hU₂ : S₂ .U = cnt one u := by
        rw [hG₂ .U (by decide), hF₁ .U (by decide) (by decide), addU_single_self, hU,
          List.append_nil]
      obtain ⟨v₃, S₃, r₃, hU₃, hM₃, hP₃, hF₃⟩ := readW_run u m v₂ S₂ hU₂
        (by rw [hG₂ .M (by decide), hG₁ .M (by decide), hM])
        (by rw [hG₂ .P (by decide), hG₁ .P (by decide), hP])
      have hV₃ : S₃ .V = cnt one w := by
        rw [hF₃ .V (by decide), hF₂ .V (by decide) (by decide), addU_single_self,
          hG₁ .V (by decide), hV, List.append_nil]
      obtain ⟨v₄, S₄, r₄, hV₄, hM₄, hP₄, hF₄⟩ : ∃ v₄ S₄, RunLe prog (2 * w + 2)
          ⟨some (if m.getD u false then .go2 else .drV), v₃, S₃⟩ ⟨some .edge, v₄, S₄⟩ ∧
          S₄ .V = [] ∧ S₄ .M = (if m.getD u false then m.set w true else m).map Sym.bit ∧
          S₄ .P = [] ∧ Fr [.V, .M, .P] S₃ S₄ := by
        cases hb : m.getD u false
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨false, update S₃ .V [], (xfer_run (M := prog) (self := .drV) rfl
            List.nodupKeys_nil (by decide) one w v₃ S₃ hV₃).le (by omega), by simp,
            by rw [update_of_ne (by decide), hM₃], by rw [update_of_ne (by decide), hP₃],
            (Fr.refl _ _).upd (by decide) _⟩
        · simp only [↓reduceIte]
          exact setW_run (self := .go2) (back := .back2) rfl rfl (by decide) (by decide) one w m
            v₃ S₃ hV₃ hM₃ hP₃
      obtain ⟨v₅, S₅, r₅, hX₅, hE₅, hM₅, hP₅, hU₅, hV₅, hF₅⟩ := edges_run n es _ v₄ S₄
        (by split <;> simp [hm]) (by rw [hF₄ .X (by decide), hF₃ .X (by decide), hX₂])
        hM₄ hP₄ (by rw [hF₄ .U (by decide), hU₃]) hV₄
      refine ⟨v₅, S₅, ((((((r₀.le le_rfl).trans (r₁.le le_rfl)).trans (r₂.le le_rfl)).trans
        r₃).trans r₄).trans r₅).mono (by simp; omega), hX₅, ?_, ?_, hP₅, hU₅, hV₅,
        Fr.trans hG₁ (Fr.trans (C := [.X, .E, .M, .U, .V, .P]) hG₂ (Fr.trans
          (C := [.X, .E, .M, .U, .V, .P]) hF₃ (Fr.trans (C := [.X, .E, .M, .U, .V, .P]) hF₄ hF₅
            (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide)
          (by decide)⟩
      · rw [hE₅, hF₄ .E (by decide), hF₃ .E (by decide), hE₂, hE₁]
        simp [cnt]
      · rw [hM₅, markPass, arc_eq hm]

/-- **The pass loop of the marking machine.** Let $n, k \in \mathbb{N}$, let $es$ be a list of
pairs of natural numbers with edge bits $b$, and let $m$ be a list of $n$ marks. Start the marking
machine at the label `pass`, with any flag, from stacks on which $N$ holds $k$ counter units, $X$,
$P$, $U$ and $V$ are empty, $E$ holds the reverse of $b$ and $M$ holds $m$, both as bit symbols.
Then within $k(5|b| + 3) + 1$ steps the machine reaches the label `goT`, with $M$ holding
$p^k(m)$ as bit symbols, where $p$ is one marking pass over $es$ on $n$ vertices, with $P$ empty,
and with every stack other than $N$, $X$, $E$, $M$, $U$, $V$ and $P$ unchanged. -/
theorem passes_run (n : ℕ) (es : List (ℕ × ℕ)) : ∀ (k : ℕ) (m : List Bool) (v : Bool)
    (St : ∀ k, List (Γ k)), m.length = n → St .N = cnt one k → St .X = [] →
    St .E = (edgeBits es).reverse.map Sym.bit → St .M = m.map Sym.bit → St .P = [] →
    St .U = [] → St .V = [] →
    ∃ v' S', RunLe prog (k * (5 * (edgeBits es).length + 3) + 1) ⟨some .pass, v, St⟩
      ⟨some .goT, v', S'⟩ ∧ S' .M = ((markPass n es)^[k] m).map Sym.bit ∧ S' .P = [] ∧
      Fr [.N, .X, .E, .M, .U, .V, .P] St S'
  | 0, _, v, St, _, hN, _, _, hM, hP, _, _ =>
      ⟨_, St, (decr_run_zero (M := prog) (self := .pass) rfl v (by simpa using hN)).le
        (by omega), hM, hP,
        Fr.refl _ _⟩
  | k + 1, m, v, St, hm, hN, hX, hE, hM, hP, hU, hV => by
      have r₁ := decr_run_cnt (M := prog) (self := .pass) rfl v hN
      obtain ⟨v₂, S₂, r₂, hE₂, hX₂, hF₂⟩ := moveB_run (M := prog) (self := .ld) (next := .edge)
        rfl (show K.E ≠ K.X by decide) (edgeBits es).reverse ((edgeBits es).reverse.map Sym.bit)
        [] _ (update St .N (cnt one k)) (by simp [hE])
        (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
      have hG₂ : Fr [.N, .E, .X] St S₂ := fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
        rw [hF₂ q hq.2.1 hq.2.2, update_of_ne hq.1]
      obtain ⟨v₃, S₃, r₃, hX₃, hE₃, hM₃, hP₃, hU₃, hV₃, hF₃⟩ := edges_run n es m v₂ S₂ hm
        (by rw [hX₂, update_of_ne (by decide), hX]; simp [List.map_reverse])
        (by rw [hG₂ .M (by decide), hM]) (by rw [hG₂ .P (by decide), hP])
        (by rw [hG₂ .U (by decide), hU]) (by rw [hG₂ .V (by decide), hV])
      obtain ⟨v₄, S₄, r₄, hM₄, hP₄, hF₄⟩ := passes_run n es k (markPass n es m) v₃ S₃
        (by rw [Path.length_markPass, hm])
        (by rw [hF₃ .N (by decide), hF₂ .N (by decide) (by decide), update_self])
        hX₃ (by rw [hE₃, hE₂]; simp) hM₃ hP₃ hU₃ hV₃
      refine ⟨v₄, S₄, ((((r₁.le le_rfl).trans (r₂.le le_rfl)).trans r₃).trans r₄).mono ?_,
        by rw [hM₄, Function.iterate_succ_apply], hP₄,
        Fr.trans hG₂ (Fr.trans (C := [.N, .X, .E, .M, .U, .V, .P]) hF₃ hF₄ (by decide)
          (by decide)) (by decide) (by decide)⟩
      simp only [List.length_reverse, Nat.succ_mul]
      omega

/-- **Running time and output of the marking machine.** For every bit string $x$, the marking
machine started at its start label, with any flag, with $x$ on the input stack $X$ as bit symbols
and every other stack empty, reaches the label `done` within $8(|x| + 1)^4$ steps, with the
output stack $O$ holding exactly one entry: the answer of the marking algorithm on $x$. -/
theorem run (x : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hX : St .X = x.map Sym.bit) (h0 : ∀ k, k ≠ .X → St k = []) :
    ∃ v' S', RunLe prog (8 * (x.length + 1) ^ 4) ⟨some start, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = [pathCheck x] := by
  have hL : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have bad : ∀ (B : ℕ) (v₁ : Bool) (S₁ : ∀ k, List (Γ k)),
      RunLe prog B ⟨some start, v, St⟩ ⟨some .bad, v₁, S₁⟩ → S₁ .O = [] →
      B + 1 ≤ 8 * (x.length + 1) ^ 2 → pathCheck x = false →
      ∃ v' S', RunLe prog (8 * (x.length + 1) ^ 4) ⟨some start, v, St⟩
        ⟨some .done, v', S'⟩ ∧ S' .O = [pathCheck x] := fun B v₁ S₁ r hO hB hc =>
    ⟨v₁, update S₁ .O [false], (r.trans ((Run.single (by
      simp [prog, TM2.stepAux, hO])).le le_rfl)).mono (by omega), by simp [hc]⟩
  rcases h1 : readUnaryLength x with _ | ⟨s, r⟩
  · obtain ⟨v₁, S₁, r₁, hO₁⟩ := readS_none (self := .rdS) rfl (by decide) (single_nodupKeys _)
      (by decide) (by decide) (by decide) x v St h1 hX
    exact bad _ v₁ S₁ r₁ (by rw [hO₁, h0 _ (by decide)]) (by nlinarith)
      (by simp [pathCheck, decodeP, h1])
  have hx₁ := (readUnaryLength_eq_some_iff x s r).1 h1
  obtain ⟨v₁, S₁, r₁, hX₁, -, hF₁⟩ := readS_some (self := .rdS) rfl (by decide)
    (single_nodupKeys _) (by decide) (by decide) s r v St (by rw [hX, hx₁])
  have hG₁ := fr_addU hF₁
  have hS₁ : S₁ .S = cnt one s := by
    rw [hF₁ .S (by decide) (by decide), addU_single_self, h0 _ (by decide), List.append_nil]
  have hl₁ : x.length = s + 1 + r.length := by rw [hx₁]; simp; omega
  rcases h2 : readUnaryLength r with _ | ⟨t, r'⟩
  · obtain ⟨v₂, S₂, r₂, hO₂⟩ := readS_none (self := .rdT) rfl (by decide) (single_nodupKeys _)
      (by decide) (by decide) (by decide) r v₁ S₁ h2 hX₁
    exact bad _ v₂ S₂ ((r₁.le le_rfl).trans r₂)
      (by rw [hO₂, hG₁ .O (by decide), h0 _ (by decide)]) (by nlinarith)
      (by simp [pathCheck, decodeP, hx₁, h2])
  have hx₂ := (readUnaryLength_eq_some_iff r t r').1 h2
  obtain ⟨v₂, S₂, r₂, hX₂, -, hF₂⟩ := readS_some (self := .rdT) rfl (by decide)
    (single_nodupKeys _) (by decide) (by decide) t r' v₁ S₁ (by rw [hX₁, hx₂])
  have hG₂ := fr_addU hF₂
  have hT₂ : S₂ .T = cnt one t := by
    rw [hF₂ .T (by decide) (by decide), addU_single_self, hG₁ .T (by decide), h0 _ (by decide),
      List.append_nil]
  have hl₂ : r.length = t + 1 + r'.length := by rw [hx₂]; simp; omega
  rcases h3 : readUnaryLength r' with _ | ⟨n, r''⟩
  · obtain ⟨v₃, S₃, r₃, hO₃⟩ := readS_none (self := .rdN) rfl (by decide)
      (pair_nodupKeys _ _ (by decide)) (by decide) (by decide) (by decide) r' v₂ S₂ h3 hX₂
    exact bad _ v₃ S₃ (((r₁.le le_rfl).trans (r₂.le le_rfl)).trans r₃)
      (by rw [hO₃, hG₂ .O (by decide), hG₁ .O (by decide), h0 _ (by decide)])
      (by nlinarith) (by simp [pathCheck, decodeP, Karp.decodeE, hx₁, hx₂, h3])
  have hx₃ := (readUnaryLength_eq_some_iff r' n r'').1 h3
  obtain ⟨v₃, S₃, r₃, hX₃, -, hF₃⟩ := readS_some (self := .rdN) rfl (by decide)
    (pair_nodupKeys _ _ (by decide)) (by decide) (by decide) n r'' v₂ S₂ (by rw [hX₂, hx₃])
  have hG₃ := fr_addU hF₃
  have hl₃ : r'.length = n + 1 + r''.length := by rw [hx₃]; simp; omega
  have hN₃ : S₃ .N = cnt one n := by
    rw [hF₃ .N (by decide) (by decide), addU_pair_fst, hG₂ .N (by decide), hG₁ .N (by decide),
      h0 _ (by decide), List.append_nil]
  have hM₃ : S₃ .M = (List.replicate n false).map Sym.bit := by
    rw [hF₃ .M (by decide) (by decide), addU_pair_snd _ _ _ _ (by decide), hG₂ .M (by decide),
      hG₁ .M (by decide), h0 _ (by decide), List.append_nil]
    simp [cnt]
  have hO₃ : S₃ .O = [] := by
    rw [hG₃ .O (by decide), hG₂ .O (by decide), hG₁ .O (by decide), h0 _ (by decide)]
  obtain ⟨v₄, S₄, r₄, hO₄, hF₄⟩ := val_run r'' v₃ S₃ hX₃
  cases h4 : decodeEs r'' with
  | none =>
      rw [h4] at r₄
      exact bad _ v₄ S₄ ((((r₁.le le_rfl).trans (r₂.le le_rfl)).trans (r₃.le le_rfl)).trans r₄)
        (by rw [hO₄, hO₃]) (by nlinarith)
        (by simp [pathCheck, decodeP, Karp.decodeE, hx₁, hx₂, hx₃, h4])
  | some es =>
      rw [h4] at r₄ hF₄
      obtain ⟨hX₄, hE₄, hG₄⟩ := hF₄ rfl
      obtain rfl : edgeBits es = r'' := Karp.edgeBits_of_decodeEs h4
      obtain ⟨v₅, S₅, r₅, -, hM₅, hP₅, hF₅⟩ := setW_run (self := .goS) (back := .backS) rfl rfl
        (by decide) (by decide) one s (List.replicate n false) v₄ S₄
        (by rw [hG₄ .S (by decide), hG₃ .S (by decide), hG₂ .S (by decide), hS₁])
        (by rw [hG₄ .M (by decide), hM₃])
        (by rw [hG₄ .P (by decide), hG₃ .P (by decide), hG₂ .P (by decide), hG₁ .P (by decide),
          h0 _ (by decide)])
      rw [set_replicate] at hM₅
      obtain ⟨v₆, S₆, r₆, hM₆, hP₆, hF₆⟩ := passes_run n es n (initMarks n s) v₅ S₅
        (by simp [initMarks]) (by rw [hF₅ .N (by decide), hG₄ .N (by decide), hN₃])
        (by rw [hF₅ .X (by decide), hX₄])
        (by rw [hF₅ .E (by decide), hE₄, hG₃ .E (by decide), hG₂ .E (by decide),
          hG₁ .E (by decide), h0 _ (by decide), List.append_nil])
        hM₅ hP₅
        (by rw [hF₅ .U (by decide), hG₄ .U (by decide), hG₃ .U (by decide), hG₂ .U (by decide),
          hG₁ .U (by decide), h0 _ (by decide)])
        (by rw [hF₅ .V (by decide), hG₄ .V (by decide), hG₃ .V (by decide), hG₂ .V (by decide),
          hG₁ .V (by decide), h0 _ (by decide)])
      obtain ⟨v₇, S₇, r₇, hT₇, hM₇, -, hF₇⟩ := walk_run (self := .goT) rfl (by decide)
        (by decide) one t [] (reachMarks n s es) v₆ S₆
        (by rw [hF₆ .T (by decide), hF₅ .T (by decide), hG₄ .T (by decide), hG₃ .T (by decide),
          hT₂]) hM₆ (by simp [hP₆])
      have r₈ : Run prog 1 ⟨some .goT, v₇, S₇⟩ ⟨some .done, (reachMarks n s es).getD t false,
          update S₇ .O ((reachMarks n s es).getD t false :: S₇ .O)⟩ :=
        Run.single (by rw [prog, stepAux_walkS_nil hT₇]; simp only [TM2.stepAux, hM₇, bitOf_drop,
          id])
      refine ⟨_, _, ((((((((r₁.le le_rfl).trans (r₂.le le_rfl)).trans (r₃.le le_rfl)).trans
        r₄).trans r₅).trans r₆).trans (r₇.le le_rfl)).trans (r₈.le le_rfl)).mono ?_, ?_⟩
      · have := Nat.mul_le_mul (show n ≤ x.length by omega)
          (show (edgeBits es).length ≤ x.length by omega)
        nlinarith
      · rw [update_self, hF₇ .O (by decide), hF₆ .O (by decide), hF₅ .O (by decide),
          hG₄ .O (by decide), hO₃, pathCheck_eq (s := s) (t := t) (n := n) (es := es)
            (by simp [decodeP, Karp.decodeE, hx₁, hx₂, hx₃, Karp.decodeEs_edgeBits])]

end Cslib.Complexity.Path.Machine
