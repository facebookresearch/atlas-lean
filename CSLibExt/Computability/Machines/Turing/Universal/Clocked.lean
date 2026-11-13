/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.Code
public import MathlibExt.Computability.TuringMachine.BitOps

/-!
# A clocked universal machine on stacks

A multi-stack program in the style of the `FinTM2` components of
`MathlibExt.Computability.TuringMachine` (state `Bool`, every stack holding bits) that runs a
coded single-tape machine (`Cslib.Turing.Universal.Code`) for a bounded number of steps.

## Representation

A number `n` is the cell `cell n`: `n` units (`true`), then a marker (`false`). The stacks hold:

- `C`: the code, as the cells of its entries `(q, a, q', s)` (`entries`, `codeCells`): four
  numbers for every table position that does not halt, row by row;
- `Q`, `H`: the state and the head cell, as counters of units;
- `L`, `R`: the cells left and right of the head, nearest first;
- `Ck`: the clock, a counter;
- `X`, `O`: the input bits and the output bits;
- `N`, `A`, `B`, `T`, `U`, `V`, `P`: scratch space (the transition found, the scan buffer, the
  comparison stacks, a reversal buffer), empty between steps.

`stk c t k q' s` is the content of every stack for the code `c`, the clock `t` and the
configuration `k`, with `q'` on `N` and `s` on `A`.

## The program

The machine reads `encIn c x T` (the clock as a cell, the cells of the input symbols of `x`, a
blank cell, the code stack reversed) from `X` into the stacks (`pc*`, `px*`, `pk0`). One
simulated step runs from `sc0` to `fin` or `hlt`: it scans `C`, moving the entries onto `B` and
comparing each key with `Q` and `H` (`cmpStep`); on a match it copies `q'` and `s` to `N` and
`A`; it moves `B` back onto `C`; then it updates the tape (`act0` to `fin`): it replaces the
state and moves left, moves right or writes. A step costs `O(|codeCells c|)` plus the sizes of the
state, the head cell and its two neighbours (`stepTime`), independently of the length of the
tape. `fin` ticks the clock and loops. At `hlt` (the coded machine halted) the machine writes
`true` and the cells of the output, without trailing blanks, on `O` (`o*`); at `tmo` (the clock
ran out) it writes `false`. Both end at `done`.

## Main results

- `findEntry_entries`: scanning the entries for the key `(q, a)` finds `c.lookup q a`.
- `act_run`: the tape update does `Code.Cfg.act`.
- `step_run_of_step_eq_some`, `step_run_of_step_eq_none`: one simulated step does `Code.step`
  within `stepTime c k` steps.
- `loop_run`, `clocked_run`: started on the code of `c`, the initial configuration on the bits
  `x` and the clock `T`, the machine stops at `hlt` holding the configuration `c.cfgAfter x T`
  exactly when `c.evalSteps x T` is defined, and at `tmo` otherwise, within
  `clockTime c T = (T + 1) * (14 * |codeCells c| + 19)` steps.
- `parse_run`, `out_run`, `univ_run`: from `encIn c x T` the machine reaches `done` with
  `encOut (c.evalSteps x T)` on `O` within `univTime c x T` steps.

`Cslib.Turing.Universal.Clocked.nonempty_univPolyTime` (in `Universal.PolyTime`) runs this machine
in the reduction host and bounds `univTime` by a quadratic polynomial.

## References

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 1.4 (efficient
  universal machines).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.Universal.Clocked

open _root_.Turing Function MetaMathlibExt.TM2Program

/-- **The cell of a number.** The cell of a natural number $n$ is the list of bits consisting of
$n$ copies of the bit true (units) followed by one bit false (a marker). -/
def cell (n : ℕ) : List Bool := cnt true n ++ [false]

/-- **The cells of a list of numbers.** The cells of a list $(n_1, \ldots, n_m)$ of natural numbers
are the concatenation of the cells of $n_1, \ldots, n_m$ in this order, so that the cell of $n_1$
comes first (on top of a stack). -/
def cells (l : List ℕ) : List Bool := l.flatMap cell

/-- **Stacks of the clocked universal machine.** The clocked universal machine has fifteen
stacks: the state $Q$, the next state $N$, the action $A$ and the head cell $H$ (these four hold
counters of units), the cells left ($L$) and right ($R$) of the head, the code $C$, the scan
buffer $B$, the scratch counters $T$, $U$, $V$, the clock $\mathrm{Ck}$, and the parsing stacks:
the encoded input $X$, the parse buffer $P$ and the output $O$. -/
inductive K | Q | N | A | H | L | R | C | B | T | U | V | Ck | X | P | O
  deriving DecidableEq

/-- Finitely many stacks. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.Q, .N, .A, .H, .L, .R, .C, .B, .T, .U, .V, .Ck, .X, .P, .O], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the clocked universal machine.** The labels of the program of the clocked
universal machine: the tape update (`act0`–`act3`, `wr0`, `wr1`, `mvL0`–`mvL3`, `mvR0`–`mvR3`)
and the clock tick `fin`; the scan, which starts at `sc0` and has labels for the state
(`rq0`–`rq2`; `cqA o` and `cqB o` for each comparison outcome `o`; `sq0 m` and `sq1 m` for each
bit `m`), for the head cell (`ra0`–`ra2`; `caA o`, `caB o`; `sa0 m`, `sa1 m`), for skipping the
rest of an entry (`sk3a`, `sk3b`, `sk2a`, `sk2b`, `sk1a`, `sk1b`) and for reading a match
(`rd0`–`rd7`); the restores `rs` and `nf`; the exits `hlt` and `tmo`; the parse of the encoded
input (`pc0`, `pc1`, `px0`–`px6`, `pk0`); and the output phase (`o1`–`o6`, `done`). -/
inductive Lab
  | act0 | act1 | act2 | act3 | wr0 | wr1 | mvL0 | mvL1 | mvL2 | mvL3 | mvR0 | mvR1 | mvR2 | mvR3
  | fin
  | sc0 | rq0 | rq1 | rq2 | cqA (o : Ordering) | cqB (o : Ordering)
  | sq0 (m : Bool) | sq1 (m : Bool)
  | ra0 | ra1 | ra2 | caA (o : Ordering) | caB (o : Ordering) | sa0 (m : Bool) | sa1 (m : Bool)
  | sk3a | sk3b | sk2a | sk2b | sk1a | sk1b
  | rd0 | rd1 | rd2 | rd3 | rd4 | rd5 | rd6 | rd7
  | rs | nf | hlt | tmo
  | pc0 | pc1 | px0 | px1 | px2 | px3 | px4 | px5 | px6 | pk0
  | o1 | o2 | o3 | o4 | o5 | o6 | done
  deriving DecidableEq

/-- Finitely many labels. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.act0, .act1, .act2, .act3, .wr0, .wr1, .mvL0, .mvL1, .mvL2, .mvL3, .mvR0, .mvR1,
    .mvR2, .mvR3, .fin, .sc0, .rq0, .rq1, .rq2, .cqA .lt, .cqA .eq, .cqA .gt, .cqB .lt, .cqB .eq,
    .cqB .gt, .sq0 false, .sq0 true, .sq1 false, .sq1 true, .ra0, .ra1, .ra2, .caA .lt, .caA .eq,
    .caA .gt, .caB .lt, .caB .eq, .caB .gt, .sa0 false, .sa0 true, .sa1 false, .sa1 true, .sk3a,
    .sk3b, .sk2a, .sk2b, .sk1a, .sk1b, .rd0, .rd1, .rd2, .rd3, .rd4, .rd5, .rd6, .rd7, .rs, .nf,
    .hlt, .tmo, .pc0, .pc1, .px0, .px1, .px2, .px3, .px4, .px5, .px6, .pk0, .o1, .o2, .o3, .o4,
    .o5, .o6, .done], by decide⟩
  complete := fun x => by
    cases x
    all_goals (try cases ‹Ordering›)
    all_goals (try cases ‹Bool›)
    all_goals decide

/-- **Stack alphabet of the clocked universal machine.** Every stack $k$ of the clocked universal
machine holds bits: its alphabet is $\Gamma(k) = \mathrm{Bool}$. -/
abbrev Γ : K → Type := fun _ => Bool

/-- **Decoding units.** The unit decoder sends the bit true (a unit) to the bit true, and sends
the bit false (a marker) to no bit, which ends a block. -/
def dU (b : Bool) : Option Bool := if b then some true else none

/-- **Moving a marker onto the scan buffer.** For a label $\ell$, this instruction pops the top
symbol of the code stack $C$ and discards it (doing nothing if $C$ is empty), pushes a marker (the
bit false) onto the scan buffer $B$, and goes to $\ell$; the state bit is unchanged. -/
def mark (next : Lab) : TM2.Stmt Γ Lab Bool :=
  .pop .C (fun v _ ↦ v) (.push .B (fun _ ↦ false) (.goto fun _ ↦ next))

/-- **The clocked universal program.** The program of the clocked universal machine gives an
instruction for every label. Numbers sit on stacks as counters of units (the bit true), and a cell
is a counter followed by a marker (the bit false).

Tape update. $\mathsf{act0}$ empties $Q$ and $\mathsf{act1}$ moves the counter $N$ onto $Q$.
$\mathsf{act2}$ pops $A$ and goes to $\mathsf{mvL0}$ if $A$ was empty, else to $\mathsf{act3}$,
which pops $A$ and goes to $\mathsf{mvR0}$ if $A$ was empty, else to $\mathsf{wr0}$; so the action
$0$ moves left, $1$ moves right and $a + 2$ writes $a$. $\mathsf{wr0}$ empties $H$ and
$\mathsf{wr1}$ moves the counter $A$ onto $H$. A left move ($\mathsf{mvL0}$ to $\mathsf{mvL3}$)
pushes a marker on $R$, moves the units of $H$ onto $R$, moves the units on top of $L$ onto $H$
and pops one more symbol of $L$; a right move ($\mathsf{mvR0}$ to $\mathsf{mvR3}$) does the same
with $L$ and $R$ exchanged. Writes and moves end at $\mathsf{fin}$, which pops the clock $Ck$ and
goes to $\mathsf{tmo}$ if it was empty, else to $\mathsf{sc0}$.

Scan. $\mathsf{sc0}$ goes to $\mathsf{nf}$ if $C$ is empty, else to $\mathsf{rq0}$. Then
$\mathsf{rq0}$, $\mathsf{rq1}$ move the units on top of $C$ onto $T$ and pop the next symbol of
$C$; $\mathsf{rq2}$ compares $T$ with $Q$ unit by unit, parking the popped units on $U$ and $V$;
$\mathsf{cqA}$, $\mathsf{cqB}$ move $U$ back onto $T$ and $V$ back onto $Q$; $\mathsf{sq0}$,
$\mathsf{sq1}$ move $T$ onto $B$, push a marker on $B$, and go to $\mathsf{ra0}$ if the two
counters were equal, else to $\mathsf{sk3a}$. The labels $\mathsf{ra0}$ to $\mathsf{sa1}$ do the
same with $H$ in place of $Q$, and go to $\mathsf{rd0}$ on equality, else to $\mathsf{sk2a}$.
From $\mathsf{sk3a}$, $\mathsf{sk2a}$ or $\mathsf{sk1a}$ the program moves three, two or one
further cells of $C$ onto $B$ (the units, then the next symbol replaced by a marker) and returns
to $\mathsf{sc0}$. The labels $\mathsf{rd0}$ to $\mathsf{rd3}$ move the units on top of $C$ onto
both $N$ and $B$, pop the next symbol of $C$ and push a marker on $B$; $\mathsf{rd4}$ to
$\mathsf{rd7}$ do the same with $A$ in place of $N$ and go to $\mathsf{rs}$. Finally
$\mathsf{rs}$ and $\mathsf{nf}$ move all of $B$ back onto $C$, one symbol at a time, and go to
$\mathsf{act0}$ and $\mathsf{hlt}$ respectively.

Parse. $\mathsf{pc0}$, $\mathsf{pc1}$ move the units on top of $X$ onto $Ck$ and pop the next
symbol of $X$. Then, while the top of $X$ is a unit, $\mathsf{px0}$ to $\mathsf{px2}$ move the
units on top of $X$ onto $P$, pop the next symbol of $X$ and push a marker on $P$; otherwise
$\mathsf{px3}$ pops $X$, $\mathsf{px4}$ moves all of $P$ onto $R$, $\mathsf{px5}$, $\mathsf{px6}$
move the units on top of $R$ onto $H$ and pop the next symbol of $R$, and $\mathsf{pk0}$ moves all
of $X$ onto $C$ and goes to $\mathsf{sc0}$.

Exits. $\mathsf{tmo}$ pushes a marker on $O$ and goes to $\mathsf{done}$. $\mathsf{hlt}$ pushes a
marker on $R$, $\mathsf{o1}$ moves the units of $H$ onto $R$, $\mathsf{o2}$ moves all of $R$ onto
$P$, $\mathsf{o3}$ pops the markers on top of $P$, $\mathsf{o4}$ pushes one marker on $P$ unless
$P$ is empty, $\mathsf{o5}$ moves all of $P$ onto $O$, and $\mathsf{o6}$ pushes a unit on $O$ and
goes to $\mathsf{done}$, where the program halts. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .act0 => xfer .Q [] .act0 .act1
  | .act1 => xfer .N [⟨.Q, true⟩] .act1 .act2
  | .act2 => decr .A .mvL0 .act3
  | .act3 => decr .A .mvR0 .wr0
  | .wr0 => xfer .H [] .wr0 .wr1
  | .wr1 => xfer .A [⟨.H, true⟩] .wr1 .fin
  | .mvL0 => incr .R false .mvL1
  | .mvL1 => xfer .H [⟨.R, true⟩] .mvL1 .mvL2
  | .mvL2 => moveB .L .H dU (fun _ => true) .mvL2 .mvL3
  | .mvL3 => decr .L .fin .fin
  | .mvR0 => incr .L false .mvR1
  | .mvR1 => xfer .H [⟨.L, true⟩] .mvR1 .mvR2
  | .mvR2 => moveB .R .H dU (fun _ => true) .mvR2 .mvR3
  | .mvR3 => decr .R .fin .fin
  | .fin => decr .Ck .tmo .sc0
  | .sc0 => .peek .C (fun _ o ↦ o.isSome) (.branch id (.goto fun _ ↦ .rq0) (.goto fun _ ↦ .nf))
  | .rq0 => moveB .C .T dU (fun _ ↦ true) .rq0 .rq1
  | .rq1 => decr .C .rq2 .rq2
  | .rq2 => cmpStep .T .Q .U .V true true .rq2 (.cqA .lt) (.cqA .eq) (.cqA .gt)
  | .cqA o => xfer .U [⟨.T, true⟩] (.cqA o) (.cqB o)
  | .cqB o => xfer .V [⟨.Q, true⟩] (.cqB o) (.sq0 (decide (o = .eq)))
  | .sq0 m => xfer .T [⟨.B, true⟩] (.sq0 m) (.sq1 m)
  | .sq1 m => incr .B false (if m then .ra0 else .sk3a)
  | .ra0 => moveB .C .T dU (fun _ ↦ true) .ra0 .ra1
  | .ra1 => decr .C .ra2 .ra2
  | .ra2 => cmpStep .T .H .U .V true true .ra2 (.caA .lt) (.caA .eq) (.caA .gt)
  | .caA o => xfer .U [⟨.T, true⟩] (.caA o) (.caB o)
  | .caB o => xfer .V [⟨.H, true⟩] (.caB o) (.sa0 (decide (o = .eq)))
  | .sa0 m => xfer .T [⟨.B, true⟩] (.sa0 m) (.sa1 m)
  | .sa1 m => incr .B false (if m then .rd0 else .sk2a)
  | .sk3a => moveB .C .B dU (fun _ ↦ true) .sk3a .sk3b
  | .sk3b => mark .sk2a
  | .sk2a => moveB .C .B dU (fun _ ↦ true) .sk2a .sk2b
  | .sk2b => mark .sk1a
  | .sk1a => moveB .C .B dU (fun _ ↦ true) .sk1a .sk1b
  | .sk1b => mark .sc0
  | .rd0 => moveB .C .T dU (fun _ ↦ true) .rd0 .rd1
  | .rd1 => decr .C .rd2 .rd2
  | .rd2 => xfer .T [⟨.N, true⟩, ⟨.B, true⟩] .rd2 .rd3
  | .rd3 => incr .B false .rd4
  | .rd4 => moveB .C .T dU (fun _ ↦ true) .rd4 .rd5
  | .rd5 => decr .C .rd6 .rd6
  | .rd6 => xfer .T [⟨.A, true⟩, ⟨.B, true⟩] .rd6 .rd7
  | .rd7 => incr .B false .rs
  | .rs => moveB .B .C some id .rs .act0
  | .nf => moveB .B .C some id .nf .hlt
  | .hlt => incr .R false .o1
  | .tmo => incr .O false .done
  | .pc0 => moveB .X .Ck dU (fun _ ↦ true) .pc0 .pc1
  | .pc1 => decr .X .px0 .px0
  | .px0 => .peek .X (fun _ o ↦ isBit dU o) (.branch id (.goto fun _ ↦ .px1) (.goto fun _ ↦ .px3))
  | .px1 => moveB .X .P dU (fun _ ↦ true) .px1 .px2
  | .px2 => .pop .X (fun v _ ↦ v) (.push .P (fun _ ↦ false) (.goto fun _ ↦ .px0))
  | .px3 => decr .X .px4 .px4
  | .px4 => moveB .P .R some id .px4 .px5
  | .px5 => moveB .R .H dU (fun _ ↦ true) .px5 .px6
  | .px6 => decr .R .pk0 .pk0
  | .pk0 => moveB .X .C some id .pk0 .sc0
  | .o1 => xfer .H [⟨.R, true⟩] .o1 .o2
  | .o2 => moveB .R .P some id .o2 .o3
  | .o3 => .peek .P (fun _ o ↦ o == some false)
      (.branch id (.pop .P (fun v _ ↦ v) (.goto fun _ ↦ .o3)) (.goto fun _ ↦ .o4))
  | .o4 => .peek .P (fun _ o ↦ o.isSome)
      (.branch id (.push .P (fun _ ↦ false) (.goto fun _ ↦ .o5)) (.goto fun _ ↦ .o5))
  | .o5 => moveB .P .O some id .o5 .o6
  | .o6 => incr .O true .done
  | .done => .halt

/-! ### The code as a list of keyed entries -/

/-- **Entries of a code.** For a code $c$, the list of quadruples $(q, a, q', s)$, one for each
state $q$ and symbol $a$ inside the table of $c$ whose table entry is a transition $(q', s)$
(enter the state $q'$ and do the action coded by $s$); halting positions are skipped. The
quadruples are listed row by row, by increasing $q$, and within a row by increasing $a$. -/
def entries (c : Code) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range c.table.length).flatMap fun q ↦
    (List.range (c.table.getD q []).length).filterMap fun a ↦
      (c.lookup q a).map fun e ↦ (q, a, e.1, e.2)

/-- **Looking up a key in a list of entries.** For natural numbers $q$ and $a$ and a list of
quadruples $(q_i, a_i, q'_i, s_i)$ of natural numbers, the result is the pair $(q'_i, s_i)$ of
the first quadruple in the list with $q_i = q$ and $a_i = a$, and no result if no quadruple has
the key $(q, a)$. This is the order in which the machine scans the code stack. -/
def findEntry (q a : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → Option (ℕ × ℕ)
  | [] => none
  | e :: es => if e.1 = q ∧ e.2.1 = a then some (e.2.2.1, e.2.2.2) else findEntry q a es

/-- The entries of a code are its table positions that do not halt. -/
private theorem mem_entries {c : Code} {q a q' s : ℕ} :
    (q, a, q', s) ∈ entries c ↔ c.lookup q a = some (q', s) := by
  simp only [entries, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨q₀, -, a₀, -, ⟨q'', s''⟩, h, rfl, rfl, rfl, rfl⟩
    exact h
  · intro h
    have hq : q < c.table.length := by
      by_contra hq
      simp [Code.lookup, List.getElem?_eq_none (Nat.le_of_not_lt hq)] at h
    have ha : a < (c.table.getD q []).length := by
      by_contra ha
      simp only [Code.lookup, List.getElem?_eq_getElem hq, Option.bind_some,
        List.getD_eq_getElem?_getD, Option.getD_some] at h ha
      simp [List.getElem?_eq_none (Nat.le_of_not_lt ha)] at h
    exact ⟨q, hq, a, ha, (q', s), h, rfl, rfl, rfl, rfl⟩

/-- No two entries of a code share a key. -/
private theorem pairwise_entries (c : Code) :
    (entries c).Pairwise fun e e' ↦ (e.1, e.2.1) ≠ (e'.1, e'.2.1) := by
  unfold entries
  rw [List.pairwise_flatMap]
  refine ⟨fun q _ ↦ ?_, ?_⟩
  · refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
    intro a a' hlt e he e' he'
    simp only [Option.map_eq_some_iff] at he he'
    obtain ⟨_, _, rfl⟩ := he
    obtain ⟨_, _, rfl⟩ := he'
    simp only [ne_eq, Prod.mk.injEq, true_and]
    omega
  · refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro q q' hlt e he e' he'
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at he he'
    obtain ⟨_, -, _, -, rfl⟩ := he
    obtain ⟨_, -, _, -, rfl⟩ := he'
    simp only [ne_eq, Prod.mk.injEq, not_and]
    omega

/-- **Scanning the entries finds the table entry.** For every code $c$ and all natural numbers
$q$ and $a$, looking up the key $(q, a)$ in the entries of $c$ gives the entry of the table of
$c$ at state $q$ and symbol $a$: the pair $(q', s)$ if that position holds the transition
$(q', s)$, and no result if it halts, including every position outside the table. -/
theorem findEntry_entries (c : Code) (q a : ℕ) : findEntry q a (entries c) = c.lookup q a := by
  have key : ∀ es : List (ℕ × ℕ × ℕ × ℕ),
      es.Pairwise (fun e e' ↦ (e.1, e.2.1) ≠ (e'.1, e'.2.1)) →
      (∀ q' s, (q, a, q', s) ∈ es ↔ c.lookup q a = some (q', s)) →
      findEntry q a es = c.lookup q a := by
    intro es
    induction es with
    | nil =>
      intro _ hmem
      cases h : c.lookup q a with
      | none => rfl
      | some r => exact absurd ((hmem r.1 r.2).2 h) (by simp)
    | cons e es ih =>
      intro hp hmem
      obtain ⟨eq, ea, eq', es'⟩ := e
      rw [List.pairwise_cons] at hp
      simp only [findEntry]
      split_ifs with hk
      · obtain ⟨rfl, rfl⟩ := hk
        exact ((hmem eq' es').1 List.mem_cons_self).symm
      · refine ih hp.2 fun q' s ↦ ⟨fun h ↦ (hmem q' s).1 (List.mem_cons_of_mem _ h), fun h ↦ ?_⟩
        rcases List.mem_cons.1 ((hmem q' s).2 h) with h' | h'
        · simp only [Prod.mk.injEq] at h'
          exact absurd ⟨h'.1.symm, h'.2.1.symm⟩ hk
        · exact h'
  exact key _ (pairwise_entries c) fun q' s ↦ mem_entries

/-- **Numbers of a list of entries.** For a list of quadruples of natural numbers, the list of
natural numbers obtained by replacing each quadruple $(q, a, q', s)$ by the four numbers
$q, a, q', s$ in this order, keeping the order of the quadruples. -/
def entryNums (es : List (ℕ × ℕ × ℕ × ℕ)) : List ℕ :=
  es.flatMap fun e ↦ [e.1, e.2.1, e.2.2.1, e.2.2.2]

/-- **The code stack.** The code stack of a code $c$ is the list of bits formed by the cells of the
numbers $q, a, q', s$ of every entry $(q, a, q', s)$ of $c$ (a table position $(q, a)$ holding the
transition $(q', s)$), with the entries ordered by $q$ and then by $a$, and the four numbers of an
entry in the order $q, a, q', s$. -/
def codeCells (c : Code) : List Bool := cells (entryNums (entries c))

/-- **The stacks of a simulated configuration.** For a code $c$, a natural number $t$ (the clock),
a configuration $k$ and natural numbers $q'$ and $s$, the stacks of $c$, $t$ and $k$ with next
state $q'$ and action $s$ hold, as counters of units (the bit true): the state of $k$ on $Q$, $q'$
on $N$, $s$ on $A$, the head symbol of $k$ on $H$ and $t$ on $Ck$. The stacks $L$ and $R$ hold the
cells of the symbols left and right of the head, nearest first, $C$ holds the code stack of $c$,
and every other stack is empty. -/
def stk (c : Code) (t : ℕ) (k : Code.Cfg) (q' s : ℕ) : ∀ j, List (Γ j)
  | .Q => cnt true k.q
  | .N => cnt true q'
  | .A => cnt true s
  | .H => cnt true k.head
  | .L => cells k.left
  | .R => cells k.right
  | .C => codeCells c
  | .Ck => cnt true t
  | _ => []

/-- **Step bound of the tape update.** For a configuration $k$ with state $q$, head cell $h$,
cells $\ell$ left of the head and cells $r$ right of the head (nearest first), a next state $q'$
and an action $s$, the step bound of the tape update is $q + q' + s + h + \ell_0 + r_0 + 8$, where
$\ell_0$ and $r_0$ are the first entries of $\ell$ and $r$, taken to be $0$ for an empty list. -/
def actTime (k : Code.Cfg) (q' s : ℕ) : ℕ :=
  k.q + q' + s + k.head + k.left.headI + k.right.headI + 8

/-- Pushing to no stack changes nothing. -/
private theorem addU_nil (n : ℕ) (S : ∀ j, List (Γ j)) : addU ([] : List (Σ j, Γ j)) n S = S :=
  rfl

/-- The empty list of targets has no duplicate keys. -/
private theorem nodup_nil : ([] : List (Σ j, Γ j)).NodupKeys := List.nodupKeys_nil

/-- The cells of a list: the units of its first cell, then the rest. -/
private theorem cells_eq (l : List ℕ) :
    cells l = cnt true l.headI ++ (if l = [] then [] else false :: cells l.tail) := by
  cases l with
  | nil => rfl
  | cons a l => simp [cells, cell]

/-- Units read as `true` bits. -/
private theorem isBitBlock_cnt (n : ℕ) : IsBitBlock dU (cnt true n) (cnt true n) := by
  simp [IsBitBlock, dU]

/-- The rest of a list of cells after the units of the first cell ends a block. -/
private theorem endsBitBlock_rest (l : List ℕ) :
    EndsBitBlock dU (if l = [] then [] else false :: cells l.tail) := by
  split_ifs <;> simp [EndsBitBlock, dU]

/-- Replacing the state: `q + q' + 2` steps from `act0` to `act2`. -/
private theorem state_run (c : Code) (t : ℕ) (k : Code.Cfg) (q' s : ℕ) (v : Bool) :
    Run prog (k.q + 1 + (q' + 1)) ⟨some .act0, v, stk c t k q' s⟩
      ⟨some .act2, false, stk c t { k with q := q' } 0 s⟩ := by
  have h₁ := xfer_run (M := prog) (self := .act0) (next := .act1) (k := .Q) (ps := []) rfl
    nodup_nil (by simp) true k.q v (stk c t k q' s) rfl
  have h₂ := xfer_run (M := prog) (self := .act1) (next := .act2) (k := .N)
    (ps := [⟨.Q, true⟩]) rfl (single_nodupKeys _) (by simp) true q' (Flag.tag false)
    (addU [] k.q (update (stk c t k q' s) .Q [])) (by rw [addU_nil]; rfl)
  have hS : addU [⟨.Q, true⟩] q' (update (addU [] k.q (update (stk c t k q' s) .Q [])) .N []) =
      stk c t { k with q := q' } 0 s := by
    funext j
    cases j <;> simp [addU, stk, List.dlookup_cons_eq, update]
  rw [hS] at h₂
  exact h₁.trans h₂

/-- Moving left: `head + headI + 4` steps from `mvL0` to `fin`. -/
private theorem mvL_run (c : Code) (t : ℕ) (k : Code.Cfg) (v : Bool) :
    ∃ v', Run prog (1 + (k.head + 1) + (k.left.headI + 1) + 1) ⟨some .mvL0, v, stk c t k 0 0⟩
      ⟨some .fin, v', stk c t ⟨k.q, k.left.tail, k.left.headI, k.head :: k.right⟩ 0 0⟩ := by
  have h₁ := incr_run (M := prog) (self := .mvL0) (next := .mvL1) (k := .R) (u := false) rfl v
    (stk c t k 0 0)
  set S₁ := update (stk c t k 0 0) .R (false :: stk c t k 0 0 .R) with hS₁
  have h₂ := xfer_run (M := prog) (self := .mvL1) (next := .mvL2) (k := .H)
    (ps := [⟨.R, true⟩]) rfl (single_nodupKeys _) (by simp) true k.head v S₁ (by simp [hS₁, stk])
  set S₂ := addU [⟨.R, true⟩] k.head (update S₁ .H []) with hS₂
  have hL : S₂ .L = cnt true k.left.headI ++
      (if k.left = [] then [] else false :: cells k.left.tail) := by
    rw [← cells_eq]; simp [hS₂, hS₁, addU, update, stk]
  obtain ⟨v₃, S₃, h₃, h3L, h3H, h3k⟩ := moveB_run (M := prog) (self := .mvL2) (next := .mvL3)
    (a := .L) (b := .H) (d := dU) (g := fun _ ↦ true) rfl (by decide) (cnt true k.left.headI) _ _
    (Flag.tag false) S₂ hL (isBitBlock_cnt _) (endsBitBlock_rest _)
  have h3H' : S₃ .H = cnt true k.left.headI := by
    rw [h3H]; simp [hS₂, hS₁, addU, update]
  have h3R : S₃ .R = cells (k.head :: k.right) := by
    rw [h3k _ (by decide) (by decide)]
    simp [hS₂, hS₁, addU, update, stk, cells, cell, List.dlookup_cons_eq]
  have h3o : ∀ j, j ≠ .L → j ≠ .H → j ≠ .R → S₃ j = stk c t k 0 0 j := by
    intro j h1 h2 h3
    rw [h3k j h1 h2]
    cases j <;> simp_all [addU, update, stk]
  have hlen : (cnt true k.left.headI).length + 1 = k.left.headI + 1 := by simp
  rw [hlen] at h₃
  by_cases hl : k.left = []
  · have h₄ := decr_run_zero (M := prog) (self := .mvL3) (ifZero := .fin) (ifPos := .fin)
      (k := .L) rfl v₃ (S := S₃) (by rw [h3L]; simp [hl])
    have hfin : S₃ = stk c t ⟨k.q, k.left.tail, k.left.headI, k.head :: k.right⟩ 0 0 := by
      funext j
      cases j
      all_goals first
        | exact h3o _ (by decide) (by decide) (by decide)
        | simp [stk, cells, hl, h3L, h3H', h3R]
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    rw [hfin] at h
    exact ⟨_, h⟩
  · have h₄ := decr_run_pos (M := prog) (self := .mvL3) (ifZero := .fin) (ifPos := .fin)
      (k := .L) rfl v₃ (S := S₃) (x := false) (r := cells k.left.tail) (by rw [h3L]; simp [hl])
    have hfin : update S₃ .L (cells k.left.tail) =
        stk c t ⟨k.q, k.left.tail, k.left.headI, k.head :: k.right⟩ 0 0 := by
      funext j
      cases j
      all_goals first
        | exact (update_of_ne (by decide) _ _).trans (h3o _ (by decide) (by decide) (by decide))
        | simp [stk, update, h3H', h3R]
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    rw [hfin] at h
    exact ⟨_, h⟩

/-- Moving right: `head + headI + 4` steps from `mvR0` to `fin`. -/
private theorem mvR_run (c : Code) (t : ℕ) (k : Code.Cfg) (v : Bool) :
    ∃ v', Run prog (1 + (k.head + 1) + (k.right.headI + 1) + 1) ⟨some .mvR0, v, stk c t k 0 0⟩
      ⟨some .fin, v', stk c t ⟨k.q, k.head :: k.left, k.right.headI, k.right.tail⟩ 0 0⟩ := by
  have h₁ := incr_run (M := prog) (self := .mvR0) (next := .mvR1) (k := .L) (u := false) rfl v
    (stk c t k 0 0)
  set S₁ := update (stk c t k 0 0) .L (false :: stk c t k 0 0 .L) with hS₁
  have h₂ := xfer_run (M := prog) (self := .mvR1) (next := .mvR2) (k := .H)
    (ps := [⟨.L, true⟩]) rfl (single_nodupKeys _) (by simp) true k.head v S₁ (by simp [hS₁, stk])
  set S₂ := addU [⟨.L, true⟩] k.head (update S₁ .H []) with hS₂
  have hL : S₂ .R = cnt true k.right.headI ++
      (if k.right = [] then [] else false :: cells k.right.tail) := by
    rw [← cells_eq]; simp [hS₂, hS₁, addU, update, stk]
  obtain ⟨v₃, S₃, h₃, h3X, h3H, h3k⟩ := moveB_run (M := prog) (self := .mvR2) (next := .mvR3)
    (a := .R) (b := .H) (d := dU) (g := fun _ ↦ true) rfl (by decide) (cnt true k.right.headI) _ _
    (Flag.tag false) S₂ hL (isBitBlock_cnt _) (endsBitBlock_rest _)
  have h3H' : S₃ .H = cnt true k.right.headI := by
    rw [h3H]; simp [hS₂, hS₁, addU, update]
  have h3Y : S₃ .L = cells (k.head :: k.left) := by
    rw [h3k _ (by decide) (by decide)]
    simp [hS₂, hS₁, addU, update, stk, cells, cell, List.dlookup_cons_eq]
  have h3o : ∀ j, j ≠ .R → j ≠ .H → j ≠ .L → S₃ j = stk c t k 0 0 j := by
    intro j h1 h2 h3
    rw [h3k j h1 h2]
    cases j <;> simp_all [addU, update, stk]
  have hlen : (cnt true k.right.headI).length + 1 = k.right.headI + 1 := by simp
  rw [hlen] at h₃
  by_cases hl : k.right = []
  · have h₄ := decr_run_zero (M := prog) (self := .mvR3) (ifZero := .fin) (ifPos := .fin)
      (k := .R) rfl v₃ (S := S₃) (by rw [h3X]; simp [hl])
    have hfin : S₃ = stk c t ⟨k.q, k.head :: k.left, k.right.headI, k.right.tail⟩ 0 0 := by
      funext j
      cases j
      all_goals first
        | exact h3o _ (by decide) (by decide) (by decide)
        | simp [stk, cells, hl, h3X, h3H', h3Y]
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    rw [hfin] at h
    exact ⟨_, h⟩
  · have h₄ := decr_run_pos (M := prog) (self := .mvR3) (ifZero := .fin) (ifPos := .fin)
      (k := .R) rfl v₃ (S := S₃) (x := false) (r := cells k.right.tail) (by rw [h3X]; simp [hl])
    have hfin : update S₃ .R (cells k.right.tail) =
        stk c t ⟨k.q, k.head :: k.left, k.right.headI, k.right.tail⟩ 0 0 := by
      funext j
      cases j
      all_goals first
        | exact (update_of_ne (by decide) _ _).trans (h3o _ (by decide) (by decide) (by decide))
        | simp [stk, update, h3H', h3Y]
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    rw [hfin] at h
    exact ⟨_, h⟩

/-- Writing `a`: `head + a + 2` steps from `wr0` to `fin`. -/
private theorem wr_run (c : Code) (t : ℕ) (k : Code.Cfg) (a : ℕ) (v : Bool) :
    Run prog (k.head + 1 + (a + 1)) ⟨some .wr0, v, stk c t k 0 a⟩
      ⟨some .fin, false, stk c t ⟨k.q, k.left, a, k.right⟩ 0 0⟩ := by
  have h₁ := xfer_run (M := prog) (self := .wr0) (next := .wr1) (k := .H) (ps := []) rfl
    nodup_nil (by simp) true k.head v (stk c t k 0 a) rfl
  have h₂ := xfer_run (M := prog) (self := .wr1) (next := .fin) (k := .A)
    (ps := [⟨.H, true⟩]) rfl (single_nodupKeys _) (by simp) true a (Flag.tag false)
    (addU [] k.head (update (stk c t k 0 a) .H [])) (by rw [addU_nil]; rfl)
  have hS : addU [⟨.H, true⟩] a (update (addU [] k.head (update (stk c t k 0 a) .H [])) .A []) =
      stk c t ⟨k.q, k.left, a, k.right⟩ 0 0 := by
    funext j
    cases j <;> simp [addU, stk, List.dlookup_cons_eq, update]
  rw [hS] at h₂
  exact h₁.trans h₂

/-- Setting the action counter. -/
private theorem update_stk_A (c : Code) (t : ℕ) (k : Code.Cfg) (s n : ℕ) :
    update (stk c t k 0 s) .A (cnt true n) = stk c t k 0 n := by
  funext j
  cases j <;> rfl

/-- **The tape update.** Let $c$ be a code, $k$ a configuration and $t$, $q'$, $s$ natural
numbers. Started at the label $\mathsf{act0}$, with any value of its internal variable, on the
stacks holding the code $c$, the clock $t$ and the configuration $k$, with $q'$ on the next-state
stack, $s$ on the action stack and all other stacks empty, the program of the clocked universal
machine reaches the label $\mathsf{fin}$, with some value of its internal variable, on the stacks
holding $c$, $t$ and the configuration obtained from $k$ by entering the state $q'$ and doing the
action coded by $s$, with the next-state, action and all other stacks empty. It does so in at
most as many steps as the step bound of the tape update for $k$, $q'$ and $s$. -/
theorem act_run (c : Code) (t : ℕ) (k : Code.Cfg) (q' s : ℕ) (v : Bool) :
    ∃ v', RunLe prog (actTime k q' s) ⟨some .act0, v, stk c t k q' s⟩
      ⟨some .fin, v', stk c t (k.act q' s) 0 0⟩ := by
  have h₀ := state_run c t k q' s v
  set k' : Code.Cfg := { k with q := q' }
  match s with
  | 0 =>
    have h₁ := decr_run_zero (M := prog) (self := .act2) (ifZero := .mvL0) (ifPos := .act3)
      (k := .A) rfl false (S := stk c t k' 0 0) rfl
    obtain ⟨v', h₂⟩ := mvL_run c t k' (Flag.tag false)
    exact ⟨v', ((h₀.trans h₁).trans h₂).le (by simp [actTime, k']; omega)⟩
  | 1 =>
    have h₁ := decr_run_cnt (M := prog) (self := .act2) (ifZero := .mvL0) (ifPos := .act3)
      (k := .A) (u := true) rfl false (S := stk c t k' 0 1) (n := 0) rfl
    rw [update_stk_A] at h₁
    have h₂ := decr_run_zero (M := prog) (self := .act3) (ifZero := .mvR0) (ifPos := .wr0)
      (k := .A) rfl (Flag.tag true) (S := stk c t k' 0 0) rfl
    obtain ⟨v', h₃⟩ := mvR_run c t k' (Flag.tag false)
    exact ⟨v', (((h₀.trans h₁).trans h₂).trans h₃).le (by simp [actTime, k']; omega)⟩
  | a + 2 =>
    have h₁ := decr_run_cnt (M := prog) (self := .act2) (ifZero := .mvL0) (ifPos := .act3)
      (k := .A) (u := true) rfl false (S := stk c t k' 0 (a + 2)) (n := a + 1) rfl
    rw [update_stk_A] at h₁
    have h₂ := decr_run_cnt (M := prog) (self := .act3) (ifZero := .mvR0) (ifPos := .wr0)
      (k := .A) (u := true) rfl (Flag.tag true) (S := stk c t k' 0 (a + 1)) (n := a) rfl
    rw [update_stk_A] at h₂
    have h₃ := wr_run c t k' a (Flag.tag true)
    exact ⟨_, (((h₀.trans h₁).trans h₂).trans h₃).le (by simp [actTime, k']; omega)⟩

/-! ### Scanning the code -/

/-- The scan stops on an empty code stack. -/
private theorem sc0_nil (v : Bool) (S : ∀ j, List (Γ j)) (h : S .C = []) :
    Run prog 1 ⟨some .sc0, v, S⟩ ⟨some .nf, false, S⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

/-- The scan reads on from a non-empty code stack. -/
private theorem sc0_cons (v : Bool) (S : ∀ j, List (Γ j)) (x : Bool) (r : List Bool)
    (h : S .C = x :: r) : Run prog 1 ⟨some .sc0, v, S⟩ ⟨some .rq0, true, S⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

/-- Read the number on top of `C` into the empty counter `T`, dropping its marker. -/
private theorem read_run {x y z : Lab} (hx : prog x = moveB .C .T dU (fun _ ↦ true) x y)
    (hy : prog y = decr .C z z) (n : ℕ) (rest : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hC : S .C = cell n ++ rest) (hT : S .T = []) :
    ∃ v', Run prog (n + 2) ⟨some x, v, S⟩
      ⟨some z, v', update (update S .C rest) .T (cnt true n)⟩ := by
  obtain ⟨v₁, S₁, h₁, h1C, h1T, h1k⟩ := moveB_run hx (by decide) (cnt true n) (cnt true n)
    (false :: rest) v S (by simp [hC, cell]) (isBitBlock_cnt n) (by simp [EndsBitBlock, dU])
  have h₂ := decr_run_pos hy v₁ (S := S₁) h1C
  have hlen : (cnt true n).length + 1 = n + 1 := by simp
  rw [hlen] at h₁
  have hS : update S₁ .C rest = update (update S .C rest) .T (cnt true n) := by
    funext j
    by_cases h1 : j = .C
    · subst h1; simp
    by_cases h2 : j = .T
    · subst h2; simp [h1T, hT]
    · simp [update_of_ne h1, update_of_ne h2, h1k j h1 h2]
  rw [hS] at h₂
  exact ⟨_, h₁.trans h₂⟩

/-- Move the number on top of `C`, with its marker, onto `B`. -/
private theorem skip_run {x y z : Lab} (hx : prog x = moveB .C .B dU (fun _ ↦ true) x y)
    (hy : prog y = mark z) (n : ℕ) (rest : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hC : S .C = cell n ++ rest) :
    ∃ v', Run prog (n + 2) ⟨some x, v, S⟩
      ⟨some z, v', update (update S .C rest) .B ((cell n).reverse ++ S .B)⟩ := by
  obtain ⟨v₁, S₁, h₁, h1C, h1B, h1k⟩ := moveB_run hx (by decide) (cnt true n) (cnt true n)
    (false :: rest) v S (by simp [hC, cell]) (isBitBlock_cnt n) (by simp [EndsBitBlock, dU])
  have h₂ : Run prog 1 ⟨some y, v₁, S₁⟩
      ⟨some z, v₁, update (update S₁ .C rest) .B (false :: S₁ .B)⟩ :=
    Run.single (by simp [hy, mark, TM2.stepAux, h1C])
  have hlen : (cnt true n).length + 1 = n + 1 := by simp
  rw [hlen] at h₁
  have hS : update (update S₁ .C rest) .B (false :: S₁ .B) =
      update (update S .C rest) .B ((cell n).reverse ++ S .B) := by
    funext j
    by_cases h1 : j = .B
    · subst h1; simp [h1B, cell]
    by_cases h2 : j = .C
    · subst h2; simp
    · simp [update_of_ne h1, update_of_ne h2, h1k j h2 h1]
  rw [hS] at h₂
  exact ⟨_, h₁.trans h₂⟩

/-- Save the counter `T` onto `B` as a reversed cell. -/
private theorem save_run {x y z : Lab} (hx : prog x = xfer .T [⟨.B, true⟩] x y)
    (hy : prog y = incr .B false z) (n : ℕ) (v : Bool) (S : ∀ j, List (Γ j))
    (hT : S .T = cnt true n) :
    Run prog (n + 2) ⟨some x, v, S⟩
      ⟨some z, false, update (update S .T []) .B ((cell n).reverse ++ S .B)⟩ := by
  have h₁ := xfer_run hx (single_nodupKeys _) (by simp) true n v S hT
  have h₂ := incr_run hy (Flag.tag false) (addU [⟨.B, true⟩] n (update S .T []))
  have hS : update (addU [⟨K.B, true⟩] n (update S .T [])) .B
      (false :: addU [⟨K.B, true⟩] n (update S .T []) .B) =
      update (update S .T []) .B ((cell n).reverse ++ S .B) := by
    funext j
    by_cases h1 : j = .B
    · subst h1
      rw [update_self, addU_single_self, update_self, update_of_ne (by decide)]
      simp [cell]
    · rw [update_of_ne h1, update_of_ne h1, addU_single_ne _ _ _ h1]
  rw [hS] at h₂
  exact h₁.trans h₂

/-- Copy the counter `T` into the empty counter `D` and onto `B` as a reversed cell. -/
private theorem copy_run {x y z : Lab} {D : K} (hDT : D ≠ .T) (hDB : D ≠ .B)
    (hx : prog x = xfer .T [⟨D, true⟩, ⟨.B, true⟩] x y) (hy : prog y = incr .B false z) (n : ℕ)
    (v : Bool) (S : ∀ j, List (Γ j)) (hT : S .T = cnt true n) (hD : S D = []) :
    Run prog (n + 2) ⟨some x, v, S⟩
      ⟨some z, false, update (update (update S .T []) D (cnt true n)) .B
        ((cell n).reverse ++ S .B)⟩ := by
  have h₁ := xfer_run hx (pair_nodupKeys _ _ hDB) (by simp [hDT.symm]) true n v S hT
  have h₂ := incr_run hy (Flag.tag false) (addU [⟨D, true⟩, ⟨.B, true⟩] n (update S .T []))
  have hS : update (addU [⟨D, true⟩, ⟨K.B, true⟩] n (update S .T [])) .B
      (false :: addU [⟨D, true⟩, ⟨K.B, true⟩] n (update S .T []) .B) =
      update (update (update S .T []) D (cnt true n)) .B ((cell n).reverse ++ S .B) := by
    funext j
    by_cases h1 : j = .B
    · subst h1
      rw [update_self, addU_pair_snd _ _ _ _ hDB.symm, update_self, update_of_ne (by decide)]
      simp [cell]
    by_cases h2 : j = D
    · subst h2
      rw [update_of_ne h1, update_of_ne h1, update_self, addU_pair_fst, update_of_ne hDT, hD]
      simp
    · rw [update_of_ne h1, update_of_ne h1, update_of_ne h2, addU_pair_ne _ _ _ _ h2 h1]
  rw [hS] at h₂
  exact h₁.trans h₂

/-- Move all of stack `a` onto stack `b`, reversed. -/
private theorem moveAll_run {x y : Lab} {a b : K} (hab : a ≠ b)
    (hx : prog x = moveB a b some id x y) (v : Bool) (S : ∀ j, List (Γ j)) :
    ∃ v', Run prog ((S a).length + 1) ⟨some x, v, S⟩
      ⟨some y, v', update (update S a []) b ((S a).reverse ++ S b)⟩ := by
  obtain ⟨v₁, S₁, h₁, h1a, h1b, h1k⟩ := moveB_run hx hab (S a) (S a) [] v S
    (by simp) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS : S₁ = update (update S a []) b ((S a).reverse ++ S b) := by
    funext j
    by_cases h1 : j = b
    · subst h1; simp [h1b]
    by_cases h2 : j = a
    · subst h2; simp [update_of_ne hab, h1a]
    · simp [update_of_ne h1, update_of_ne h2, h1k j h2 h1]
  rw [hS] at h₁
  exact ⟨_, h₁⟩

/-- Compare the counter `T` with the state `Q`, leaving both in place. -/
private theorem cmpQ_run (m q : ℕ) (v : Bool) (S : ∀ j, List (Γ j)) (hT : S .T = cnt true m)
    (hQ : S .Q = cnt true q) (hU : S .U = []) (hV : S .V = []) :
    Run prog (3 * min m q + 3 + (if m = q then 0 else 1)) ⟨some .rq2, v, S⟩
      ⟨some (.sq0 (decide (m = q))), false, S⟩ := by
  have h := cmp_run (M := prog) (a := .T) (b := .Q) (ta := .U) (tb := .V) (ua := true)
    (ub := true) (uta := true) (utb := true) (self := .rq2) (r := Lab.cqA) (rB := Lab.cqB)
    (out := fun o ↦ .sq0 (decide (o = .eq))) rfl (fun _ ↦ rfl) (fun _ ↦ rfl) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) m q v S hT hQ hU hV
  simp only [Nat.compare_eq_eq] at h
  exact h

/-- Compare the counter `T` with the head cell `H`, leaving both in place. -/
private theorem cmpA_run (m a : ℕ) (v : Bool) (S : ∀ j, List (Γ j)) (hT : S .T = cnt true m)
    (hH : S .H = cnt true a) (hU : S .U = []) (hV : S .V = []) :
    Run prog (3 * min m a + 3 + (if m = a then 0 else 1)) ⟨some .ra2, v, S⟩
      ⟨some (.sa0 (decide (m = a))), false, S⟩ := by
  have h := cmp_run (M := prog) (a := .T) (b := .H) (ta := .U) (tb := .V) (ua := true)
    (ub := true) (uta := true) (utb := true) (self := .ra2) (r := Lab.caA) (rB := Lab.caB)
    (out := fun o ↦ .sa0 (decide (o = .eq))) rfl (fun _ ↦ rfl) (fun _ ↦ rfl) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) m a v S hT hH hU hV
  simp only [Nat.compare_eq_eq] at h
  exact h

/-- **Cost of scanning past one entry.** The step budget for scanning past an entry
$(q, a, q', s)$ of the code stack is $5q + 5a + 2q' + 2s + 30$. -/
def entryCost (e : ℕ × ℕ × ℕ × ℕ) : ℕ := 5 * e.1 + 5 * e.2.1 + 2 * e.2.2.1 + 2 * e.2.2.2 + 30

/-- The cells of the entries, the first entry first. -/
private theorem cells_entryNums_cons (e : ℕ × ℕ × ℕ × ℕ) (es : List (ℕ × ℕ × ℕ × ℕ)) :
    cells (entryNums (e :: es)) =
      cell e.1 ++ (cell e.2.1 ++ (cell e.2.2.1 ++ (cell e.2.2.2 ++ cells (entryNums es)))) := by
  simp [entryNums, cells, List.flatMap_cons]

/-- **The scan.** From `sc0`, with the cells of the entries `es` on `C`, the state `q` on `Q` and
the head cell `a` on `H`, the machine moves entries from `C` to `B` until it finds the key
`(q, a)`: then it is at `rs` with the answer on `N` and `A`; otherwise it is at `nf` with `C`
empty. `B` and `C` together still spell the original contents, and no other stack changes. -/
private theorem scan_run (q a : ℕ) : ∀ (es : List (ℕ × ℕ × ℕ × ℕ)) (v : Bool)
    (S : ∀ j, List (Γ j)),
    S .C = cells (entryNums es) → S .T = [] → S .U = [] → S .V = [] → S .N = [] → S .A = [] →
    S .Q = cnt true q → S .H = cnt true a →
    ∃ v' S', RunLe prog ((es.map entryCost).sum + 1) ⟨some .sc0, v, S⟩
      ⟨some ((findEntry q a es).elim .nf fun _ ↦ .rs), v', S'⟩ ∧
      (S' .B).reverse ++ S' .C = (S .B).reverse ++ S .C ∧
      S' .N = cnt true (((findEntry q a es).map Prod.fst).getD 0) ∧
      S' .A = cnt true (((findEntry q a es).map Prod.snd).getD 0) ∧
      ∀ j, j ≠ .B → j ≠ .C → j ≠ .N → j ≠ .A → S' j = S j := by
  intro es
  induction es with
  | nil =>
    intro v S hC hT hU hV hN hA hQ hH
    refine ⟨false, S, (sc0_nil v S (by simpa [entryNums, cells] using hC)).le (by simp), rfl,
      by simp [findEntry, hN], by simp [findEntry, hA], fun _ _ _ _ _ ↦ rfl⟩
  | cons e es ih =>
    intro v S hC hT hU hV hN hA hQ hH
    obtain ⟨e₁, e₂, e₃, e₄⟩ := e
    rw [cells_entryNums_cons] at hC
    simp only at hC
    set R4 := cells (entryNums es)
    obtain ⟨x, r, hxr⟩ := List.exists_cons_of_ne_nil (by simp [hC, cell] : S .C ≠ [])
    have h0 := sc0_cons v S x r hxr
    obtain ⟨v₁, h1⟩ := read_run (x := .rq0) (y := .rq1) (z := .rq2) rfl rfl e₁ _ true S hC hT
    set S1 := update (update S .C (cell e₂ ++ (cell e₃ ++ (cell e₄ ++ R4)))) .T (cnt true e₁)
    have h2 := cmpQ_run e₁ q v₁ S1 (by simp [S1]) (by simp [S1, hQ]) (by simp [S1, hU])
      (by simp [S1, hV])
    by_cases hq : e₁ = q
    · subst hq
      simp only [decide_true, ite_true, add_zero] at h2
      have h3 := save_run (x := .sq0 true) (y := .sq1 true) (z := .ra0) rfl rfl e₁ false S1
        (by simp [S1])
      set S3 := update (update S1 .T []) .B ((cell e₁).reverse ++ S1 .B)
      obtain ⟨v₄, h4⟩ := read_run (x := .ra0) (y := .ra1) (z := .ra2) rfl rfl e₂
        (cell e₃ ++ (cell e₄ ++ R4)) false S3
        (by simp [S3, S1]) (by simp [S3])
      set S4 := update (update S3 .C (cell e₃ ++ (cell e₄ ++ R4))) .T (cnt true e₂)
      have h5 := cmpA_run e₂ a v₄ S4 (by simp [S4]) (by simp [S4, S3, S1, hH])
        (by simp [S4, S3, S1, hU]) (by simp [S4, S3, S1, hV])
      by_cases ha : e₂ = a
      · subst ha
        simp only [decide_true, ite_true, add_zero] at h5
        have h6 := save_run (x := .sa0 true) (y := .sa1 true) (z := .rd0) rfl rfl e₂ false S4
          (by simp [S4])
        set S6 := update (update S4 .T []) .B ((cell e₂).reverse ++ S4 .B)
        obtain ⟨v₇, h7⟩ := read_run (x := .rd0) (y := .rd1) (z := .rd2) rfl rfl e₃
          (cell e₄ ++ R4) false S6
          (by simp [S6, S4]) (by simp [S6])
        set S7 := update (update S6 .C (cell e₄ ++ R4)) .T (cnt true e₃)
        have h8 := copy_run (x := .rd2) (y := .rd3) (z := .rd4) (D := .N) (by decide) (by decide)
          rfl rfl e₃ v₇ S7 (by simp [S7]) (by simp [S7, S6, S4, S3, S1, hN])
        set S8 := update (update (update S7 .T []) .N (cnt true e₃)) .B
          ((cell e₃).reverse ++ S7 .B)
        obtain ⟨v₉, h9⟩ := read_run (x := .rd4) (y := .rd5) (z := .rd6) rfl rfl e₄ R4 false S8
          (by simp [S8, S7]) (by simp [S8])
        set S9 := update (update S8 .C R4) .T (cnt true e₄)
        have h10 := copy_run (x := .rd6) (y := .rd7) (z := .rs) (D := .A) (by decide)
          (by decide) rfl rfl e₄ v₉ S9 (by simp [S9])
          (by simp [S9, S8, S7, S6, S4, S3, S1, hA])
        have hr := (((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans
          h6).trans h7).trans h8).trans h9).trans h10
        have hf : findEntry e₁ e₂ ((e₁, e₂, e₃, e₄) :: es) = some (e₃, e₄) := by
          simp [findEntry]
        simp only [hf, Option.elim, Option.map_some, Option.getD_some]
        refine ⟨_, _, hr.le ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, entryCost]
          omega
        · simp [S9, S8, S7, S6, S4, S3, S1, hC, List.reverse_append, cell, List.append_assoc]
        · simp [S9, S8]
        · simp
        · intro j h1 h2 h3 h4
          by_cases h5 : j = .T
          · subst h5; simp [hT]
          · simp [S9, S8, S7, S6, S4, S3, S1, h1, h2, h3, h4, h5]
      · have hne : decide (e₂ = a) = false := by simp [ha]
        rw [hne] at h5
        have h6 := save_run (x := .sa0 false) (y := .sa1 false) (z := .sk2a) rfl rfl e₂ false S4
          (by simp [S4])
        set S6 := update (update S4 .T []) .B ((cell e₂).reverse ++ S4 .B)
        obtain ⟨v₇, h7⟩ := skip_run (x := .sk2a) (y := .sk2b) (z := .sk1a) rfl rfl e₃
          (cell e₄ ++ R4) false S6
          (by simp [S6, S4])
        set S7 := update (update S6 .C (cell e₄ ++ R4)) .B ((cell e₃).reverse ++ S6 .B)
        obtain ⟨v₈, h8⟩ := skip_run (x := .sk1a) (y := .sk1b) (z := .sc0) rfl rfl e₄ R4 v₇ S7
          (by simp [S7])
        set S8 := update (update S7 .C R4) .B ((cell e₄).reverse ++ S7 .B)
        obtain ⟨v', S', ⟨n, hn, hrun⟩, hinv, hN', hA', hfr⟩ := ih v₈ S8 (by simp [S8])
          (by simp [S8, S7, S6]) (by simp [S8, S7, S6, S4, S3, S1, hU])
          (by simp [S8, S7, S6, S4, S3, S1, hV]) (by simp [S8, S7, S6, S4, S3, S1, hN])
          (by simp [S8, S7, S6, S4, S3, S1, hA]) (by simp [S8, S7, S6, S4, S3, S1, hQ])
          (by simp [S8, S7, S6, S4, S3, S1, hH])
        have hf : findEntry e₁ a ((e₁, e₂, e₃, e₄) :: es) = findEntry e₁ a es := by
          simp [findEntry, ha]
        rw [hf]
        have hr := (((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans
          h6).trans h7).trans h8
        refine ⟨v', S', ⟨_, ?_, hr.trans hrun⟩, ?_, hN', hA', ?_⟩
        · simp only [List.map_cons, List.sum_cons, entryCost]
          have := Nat.min_le_left e₂ a
          have : (if e₂ = a then 0 else 1) ≤ 1 := by split <;> omega
          omega
        · rw [hinv]
          simp [S8, S7, S6, S4, S3, S1, hC, List.reverse_append, cell, List.append_assoc]
        · intro j h1 h2 h3 h4
          rw [hfr j h1 h2 h3 h4]
          by_cases h5 : j = .T
          · subst h5; simp [S8, S7, S6, hT]
          · simp [S8, S7, S6, S4, S3, S1, h1, h2, h5]
    · have hne : decide (e₁ = q) = false := by simp [hq]
      rw [hne] at h2
      have h3 := save_run (x := .sq0 false) (y := .sq1 false) (z := .sk3a) rfl rfl e₁ false S1
        (by simp [S1])
      set S3 := update (update S1 .T []) .B ((cell e₁).reverse ++ S1 .B)
      obtain ⟨v₄, h4⟩ := skip_run (x := .sk3a) (y := .sk3b) (z := .sk2a) rfl rfl e₂
        (cell e₃ ++ (cell e₄ ++ R4)) false S3 (by simp [S3, S1])
      set S4 := update (update S3 .C (cell e₃ ++ (cell e₄ ++ R4))) .B ((cell e₂).reverse ++ S3 .B)
      obtain ⟨v₅, h5⟩ := skip_run (x := .sk2a) (y := .sk2b) (z := .sk1a) rfl rfl e₃
        (cell e₄ ++ R4) v₄ S4 (by simp [S4])
      set S5 := update (update S4 .C (cell e₄ ++ R4)) .B ((cell e₃).reverse ++ S4 .B)
      obtain ⟨v₆, h6⟩ := skip_run (x := .sk1a) (y := .sk1b) (z := .sc0) rfl rfl e₄ R4 v₅ S5
        (by simp [S5])
      set S6 := update (update S5 .C R4) .B ((cell e₄).reverse ++ S5 .B)
      obtain ⟨v', S', ⟨n, hn, hrun⟩, hinv, hN', hA', hfr⟩ := ih v₆ S6 (by simp [S6])
        (by simp [S6, S5, S4, S3]) (by simp [S6, S5, S4, S3, S1, hU])
        (by simp [S6, S5, S4, S3, S1, hV]) (by simp [S6, S5, S4, S3, S1, hN])
        (by simp [S6, S5, S4, S3, S1, hA]) (by simp [S6, S5, S4, S3, S1, hQ])
        (by simp [S6, S5, S4, S3, S1, hH])
      have hf : findEntry q a ((e₁, e₂, e₃, e₄) :: es) = findEntry q a es := by
        simp [findEntry, hq]
      rw [hf]
      have hr := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6
      refine ⟨v', S', ⟨_, ?_, hr.trans hrun⟩, ?_, hN', hA', ?_⟩
      · simp only [List.map_cons, List.sum_cons, entryCost]
        have := Nat.min_le_left e₁ q
        have : (if e₁ = q then 0 else 1) ≤ 1 := by split <;> omega
        omega
      · rw [hinv]
        simp [S6, S5, S4, S3, S1, hC, List.reverse_append, cell, List.append_assoc]
      · intro j h1 h2 h3 h4
        rw [hfr j h1 h2 h3 h4]
        by_cases h5 : j = .T
        · subst h5; simp [S6, S5, S4, S3, hT]
        · simp [S6, S5, S4, S3, S1, h1, h2, h5]

/-! ### One simulated step -/

/-- A cell has one symbol more than its number. -/
private theorem length_cell (n : ℕ) : (cell n).length = n + 1 := by simp [cell]

/-- The scan cost is at most eight times the length of the code stack. -/
private theorem sum_entryCost_le : ∀ es : List (ℕ × ℕ × ℕ × ℕ),
    (es.map entryCost).sum ≤ 8 * (cells (entryNums es)).length
  | [] => by simp
  | e :: es => by
    have ih := sum_entryCost_le es
    rw [cells_entryNums_cons]
    simp only [List.map_cons, List.sum_cons, List.length_append, length_cell, entryCost]
    omega

/-- The answer of an entry is bounded by the length of the code stack. -/
private theorem le_length_of_mem {q a q' s : ℕ} : ∀ {es : List (ℕ × ℕ × ℕ × ℕ)},
    (q, a, q', s) ∈ es → q' + s ≤ (cells (entryNums es)).length
  | [], h => by simp at h
  | e :: es, h => by
    rw [cells_entryNums_cons]
    simp only [List.length_append, length_cell]
    rcases List.mem_cons.1 h with rfl | h
    · simp only; omega
    · have := le_length_of_mem h
      omega

/-- **Step bound of one simulated step.** For a code $c$ and a configuration $k$ with state $q$,
head cell $h$, nearest left cell $l$ and nearest right cell $r$ (each read as the blank $0$ when
there is no such cell), let $|C|$ be the length of the code stack of $c$. The step bound of $c$
at $k$ is $10|C| + q + h + l + r + 10$. -/
def stepTime (c : Code) (k : Code.Cfg) : ℕ :=
  10 * (codeCells c).length + k.q + k.head + k.left.headI + k.right.headI + 10

/-- The scan from the stacks of `k`, with the answer of the table. -/
private theorem scan_stk (c : Code) (t : ℕ) (k : Code.Cfg) (v : Bool) :
    ∃ v' S', RunLe prog (8 * (codeCells c).length + 1) ⟨some .sc0, v, stk c t k 0 0⟩
      ⟨some ((c.lookup k.q k.head).elim .nf fun _ ↦ .rs), v', S'⟩ ∧
      (S' .B).reverse ++ S' .C = codeCells c ∧
      S' .N = cnt true (((c.lookup k.q k.head).map Prod.fst).getD 0) ∧
      S' .A = cnt true (((c.lookup k.q k.head).map Prod.snd).getD 0) ∧
      ∀ j, j ≠ .B → j ≠ .C → j ≠ .N → j ≠ .A → S' j = stk c t k 0 0 j := by
  obtain ⟨v', S', hr, hinv, hN, hA, hfr⟩ := scan_run k.q k.head (entries c) v (stk c t k 0 0) rfl
    rfl rfl rfl rfl rfl rfl rfl
  rw [findEntry_entries] at hr hN hA
  exact ⟨v', S', hr.mono (by have := sum_entryCost_le (entries c); simp only [codeCells]; omega),
    by simpa [stk] using hinv, hN, hA, hfr⟩

/-- **One simulated step, running case.** Let $c$ be a code, $k$ and $k'$ configurations such that
one step of $c$ from $k$ gives $k'$, $t$ a natural number, $v$ a bit, and $b$ the step bound of
$c$ at $k$. Started at the label $\mathsf{sc0}$ with state bit $v$ and the stacks of the code $c$,
the clock $t$ and the configuration $k$ with next state and action $0$, the clocked universal
program reaches the label $\mathsf{fin}$ within $b$ steps, with some state bit and the stacks of
$c$, $t$ and $k'$ with next state and action $0$. -/
theorem step_run_of_step_eq_some {c : Code} {k k' : Code.Cfg} (h : c.step k = some k') (t : ℕ)
    (v : Bool) :
    ∃ v', RunLe prog (stepTime c k) ⟨some .sc0, v, stk c t k 0 0⟩
      ⟨some .fin, v', stk c t k' 0 0⟩ := by
  obtain ⟨⟨q', s⟩, hl, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨v₁, S₁, h₁, hinv, hN, hA, hfr⟩ := scan_stk c t k v
  rw [hl] at h₁ hN hA
  obtain ⟨v₂, h₂⟩ := moveAll_run (x := .rs) (y := .act0) (a := .B) (b := .C) (by decide) rfl v₁ S₁
  have hS : update (update S₁ .B []) .C ((S₁ .B).reverse ++ S₁ .C) = stk c t k q' s := by
    funext j
    cases j
    case B => simp [stk]
    case C => simp [hinv, stk]
    case N => simp [hN, stk]
    case A => simp [hA, stk]
    all_goals
      rw [update_of_ne (by decide), update_of_ne (by decide)]
      exact hfr _ (by decide) (by decide) (by decide) (by decide)
  rw [hS] at h₂
  obtain ⟨v₃, h₃⟩ := act_run c t k q' s v₂
  have hB : (S₁ .B).length ≤ (codeCells c).length := by
    rw [← hinv]; simp
  have hqs := le_length_of_mem (mem_entries.2 hl)
  refine ⟨v₃, (h₁.trans ((h₂.le le_rfl).trans h₃)).mono ?_⟩
  simp only [stepTime, actTime, codeCells] at hB hqs ⊢
  omega

/-- **One simulated step, halting case.** Let $c$ be a code, $k$ a configuration at which $c$ halts
(one step of $c$ from $k$ gives nothing), $t$ a natural number, $v$ a bit, and $b$ the step bound
of $c$ at $k$. Started at the label $\mathsf{sc0}$ with state bit $v$ and the stacks of the code
$c$, the clock $t$ and the configuration $k$ with next state and action $0$, the clocked universal
program reaches the label $\mathsf{hlt}$ within $b$ steps, with some state bit and the same
stacks. -/
theorem step_run_of_step_eq_none {c : Code} {k : Code.Cfg} (h : c.step k = none) (t : ℕ)
    (v : Bool) :
    ∃ v', RunLe prog (stepTime c k) ⟨some .sc0, v, stk c t k 0 0⟩
      ⟨some .hlt, v', stk c t k 0 0⟩ := by
  have hl : c.lookup k.q k.head = none := Option.map_eq_none_iff.1 h
  obtain ⟨v₁, S₁, h₁, hinv, hN, hA, hfr⟩ := scan_stk c t k v
  rw [hl] at h₁ hN hA
  obtain ⟨v₂, h₂⟩ := moveAll_run (x := .nf) (y := .hlt) (a := .B) (b := .C) (by decide) rfl v₁ S₁
  have hS : update (update S₁ .B []) .C ((S₁ .B).reverse ++ S₁ .C) = stk c t k 0 0 := by
    funext j
    cases j
    case B => simp [stk]
    case C => simp [hinv, stk]
    case N => simp [hN, stk]
    case A => simp [hA, stk]
    all_goals
      rw [update_of_ne (by decide), update_of_ne (by decide)]
      exact hfr _ (by decide) (by decide) (by decide) (by decide)
  rw [hS] at h₂
  have hB : (S₁ .B).length ≤ (codeCells c).length := by
    rw [← hinv]; simp
  refine ⟨v₂, (h₁.trans (h₂.le le_rfl)).mono ?_⟩
  simp only [stepTime] at hB ⊢
  omega

/-! ### The clocked loop -/

/-- **Configurations bounded by $M$.** A configuration $k$ is bounded by a natural number $M$
when its state, its head cell and every cell left and right of the head are at most $M$. -/
def Bounded (M : ℕ) (k : Code.Cfg) : Prop :=
  k.q ≤ M ∧ k.head ≤ M ∧ (∀ a ∈ k.left, a ≤ M) ∧ ∀ a ∈ k.right, a ≤ M

/-- The first element of a list of numbers at most `M` is at most `M`. -/
private theorem headI_le {M : ℕ} {l : List ℕ} (h : ∀ a ∈ l, a ≤ M) : l.headI ≤ M := by
  cases l with
  | nil => exact Nat.zero_le _
  | cons a l => exact h a List.mem_cons_self

/-- A step keeps the numbers of a configuration at most `M` once `M` bounds the code stack. -/
private theorem bounded_step {c : Code} {M : ℕ} (hM : (codeCells c).length ≤ M)
    {k k' : Code.Cfg} (hk : Bounded M k) (h : c.step k = some k') : Bounded M k' := by
  obtain ⟨⟨q', s⟩, hl, rfl⟩ := Option.map_eq_some_iff.1 h
  have hqs := le_length_of_mem (mem_entries.2 hl)
  obtain ⟨hq, hh, hL, hR⟩ := hk
  simp only [codeCells] at hM
  unfold Bounded
  rcases s with _ | _ | a
  · refine ⟨by dsimp only [Code.Cfg.act]; omega, headI_le hL,
      fun x hx ↦ hL x (List.mem_of_mem_tail hx), fun x hx ↦ ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hh
    · exact hR x hx
  · refine ⟨by dsimp only [Code.Cfg.act]; omega, headI_le hR, fun x hx ↦ ?_,
      fun x hx ↦ hR x (List.mem_of_mem_tail hx)⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hh
    · exact hL x hx
  · exact ⟨by dsimp only [Code.Cfg.act]; omega, by dsimp only [Code.Cfg.act]; omega, hL, hR⟩

/-- The initial configuration holds only the numbers `0`, `1` and `2`. -/
private theorem bounded_init (x : List Bool) {M : ℕ} (hM : 2 ≤ M) : Bounded M (Code.init x) := by
  have hin : ∀ a ∈ input x, a ≤ M := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    cases b <;> simp [bitSym] <;> omega
  exact ⟨Nat.zero_le _, headI_le hin, by simp [Code.init],
    fun a ha ↦ hin a (List.mem_of_mem_tail ha)⟩

/-- **Step bound of the clocked loop.** For a code $c$ and a number $M$, the loop step time is
$10\ell + 4M + 11$, where $\ell$ is the length of the code stack of $c$. It serves as the cost
bound of one round of the loop (a simulated step and a clock tick) on configurations whose numbers
are at most $M$. -/
def loopStepTime (c : Code) (M : ℕ) : ℕ := 10 * (codeCells c).length + 4 * M + 11

/-- The step bound under `Bounded M`. -/
private theorem stepTime_le {c : Code} {M : ℕ} {k : Code.Cfg} (hk : Bounded M k) :
    stepTime c k + 1 ≤ loopStepTime c M := by
  obtain ⟨hq, hh, hL, hR⟩ := hk
  have := headI_le hL
  have := headI_le hR
  simp only [stepTime, loopStepTime]
  omega

/-- A halted configuration is fixed by `stepOrStay`. -/
private theorem iterate_stepOrStay_of_step_eq_none {c : Code} {k : Code.Cfg} (h : c.step k = none)
    (n : ℕ) : c.stepOrStay^[n] k = k :=
  Function.iterate_fixed (by rw [Code.stepOrStay, h, Option.getD_none]) n

/-- **The clocked loop.** Let $c$ be a code, let $M$ be at least the length of the code stack of
$c$, let $k$ be a configuration whose state and cells are all at most $M$, let $t$ be a natural
number and $v$ a bit, and let $k_t$ be the result of $t$ steps of $c$ from $k$, where a halted
configuration stays put. Start the program of the clocked universal machine at label `sc0` with
variable $v$ and the stacks of $c$, the clock $t$ and $k$ (next state and action $0$). If $k_t$
has halted, then within $(t + 1) \cdot L(c, M)$ steps, where $L(c, M)$ is the loop step time,
the program reaches label `hlt` with some variable and the stacks of $c$, some clock $t'$ and
$k_t$ (next state and action $0$). If instead $c$ steps $k_t$ to $k''$, then within the same
number of steps it reaches label `tmo` with some variable and the stacks of $c$, the clock $0$
and $k''$ (next state and action $0$). -/
theorem loop_run {c : Code} {M : ℕ} (hM : (codeCells c).length ≤ M) :
    ∀ (t : ℕ) (k : Code.Cfg), Bounded M k → ∀ v : Bool,
      (c.step (c.stepOrStay^[t] k) = none →
        ∃ v' t', RunLe prog ((t + 1) * loopStepTime c M) ⟨some .sc0, v, stk c t k 0 0⟩
          ⟨some .hlt, v', stk c t' (c.stepOrStay^[t] k) 0 0⟩) ∧
      ∀ k'', c.step (c.stepOrStay^[t] k) = some k'' →
        ∃ v', RunLe prog ((t + 1) * loopStepTime c M) ⟨some .sc0, v, stk c t k 0 0⟩
          ⟨some .tmo, v', stk c 0 k'' 0 0⟩ := by
  intro t
  induction t with
  | zero =>
    intro k hk v
    cases h : c.step k with
    | none =>
      obtain ⟨v', hr⟩ := step_run_of_step_eq_none h 0 v
      refine ⟨fun _ ↦ ⟨v', 0, hr.mono (by have := stepTime_le (c := c) hk; omega)⟩,
        fun k'' h' ↦ ?_⟩
      simp [h] at h'
    | some k₁ =>
      refine ⟨fun h' ↦ by simp [h] at h', fun k'' h' ↦ ?_⟩
      simp only [Function.iterate_zero, id, h, Option.some.injEq] at h'
      subst h'
      obtain ⟨v₁, hr⟩ := step_run_of_step_eq_some h 0 v
      have h₂ := decr_run_zero (M := prog) (self := .fin) (ifZero := .tmo) (ifPos := .sc0)
        (k := .Ck) rfl v₁ (S := stk c 0 k₁ 0 0) rfl
      exact ⟨_, hr.trans (h₂.le le_rfl) |>.mono (by have := stepTime_le (c := c) hk; omega)⟩
  | succ t ih =>
    intro k hk v
    cases h : c.step k with
    | none =>
      rw [iterate_stepOrStay_of_step_eq_none h]
      obtain ⟨v', hr⟩ := step_run_of_step_eq_none h (t + 1) v
      refine ⟨fun _ ↦ ⟨v', t + 1, hr.mono ?_⟩, fun k'' h' ↦ by simp [h] at h'⟩
      have := stepTime_le (c := c) hk
      have : (t + 1 + 1) * loopStepTime c M = (t + 1) * loopStepTime c M + loopStepTime c M :=
        Nat.succ_mul _ _
      omega
    | some k₁ =>
      have hk₁ : c.stepOrStay k = k₁ := by rw [Code.stepOrStay, h, Option.getD_some]
      rw [Function.iterate_succ_apply, hk₁]
      obtain ⟨v₁, hr⟩ := step_run_of_step_eq_some h (t + 1) v
      have h₂ := decr_run_cnt (M := prog) (self := .fin) (ifZero := .tmo) (ifPos := .sc0)
        (k := .Ck) (u := true) rfl v₁ (S := stk c (t + 1) k₁ 0 0) (n := t) rfl
      have hS : update (stk c (t + 1) k₁ 0 0) .Ck (cnt true t) = stk c t k₁ 0 0 := by
        funext j
        cases j <;> rfl
      rw [hS] at h₂
      obtain ⟨ih₁, ih₂⟩ := ih k₁ (bounded_step hM hk h) (Flag.tag true)
      have hb := stepTime_le (c := c) hk
      have hB : stepTime c k + 1 + (t + 1) * loopStepTime c M ≤
          (t + 1 + 1) * loopStepTime c M := by
        have : (t + 1 + 1) * loopStepTime c M = (t + 1) * loopStepTime c M + loopStepTime c M :=
          Nat.succ_mul _ _
        omega
      refine ⟨fun h' ↦ ?_, fun k'' h' ↦ ?_⟩
      · obtain ⟨v', t', hr'⟩ := ih₁ h'
        exact ⟨v', t', ((hr.trans (h₂.le le_rfl)).trans hr').mono hB⟩
      · obtain ⟨v', hr'⟩ := ih₂ k'' h'
        exact ⟨v', ((hr.trans (h₂.le le_rfl)).trans hr').mono hB⟩

/-- **Step bound of the clocked simulation.** For a code $c$ and a clock $T$, let $|C|$ be the
length of the code stack of $c$. The step bound of the clocked simulation on the clock $T$ is
$T + 1$ times the cost of one round of the loop on configurations whose numbers are at most
$|C| + 2$, that is, $(T + 1)(14|C| + 19)$. -/
def clockTime (c : Code) (T : ℕ) : ℕ := (T + 1) * loopStepTime c ((codeCells c).length + 2)

/-- **The clocked universal machine on stacks.** Let $c$ be a code, $x$ a list of bits and $T$ a
natural number, and let $|C|$ be the length of the code stack of $c$. Start the program of the
clocked universal machine at the label $\mathsf{sc0}$, with any value of its internal variable,
on the stacks holding the code $c$, the clock $T$ and the initial configuration on $x$, all other
stacks empty. If the clocked evaluation of $c$ on $x$ for $T$ steps is defined, the machine
reaches the label $\mathsf{hlt}$ on the stacks holding $c$, some clock $t'$ and the configuration
of $c$ after $T$ steps on $x$; otherwise it reaches the label $\mathsf{tmo}$ on the stacks holding
$c$, the clock $0$ and some configuration. In both cases the internal variable ends with some
value, all other stacks are empty, and the run takes at most $(T + 1)(14|C| + 19)$ steps, the
step bound of the clocked machine on the clock $T$.

When the clocked evaluation is defined, its value is the output of the configuration of $c$ after
$T$ steps on $x$. -/
theorem clocked_run (c : Code) (x : List Bool) (T : ℕ) (v : Bool) :
    ((c.evalSteps x T).isSome → ∃ v' t', RunLe prog (clockTime c T)
      ⟨some .sc0, v, stk c T (Code.init x) 0 0⟩ ⟨some .hlt, v', stk c t' (c.cfgAfter x T) 0 0⟩) ∧
    (c.evalSteps x T = none → ∃ v' k'', RunLe prog (clockTime c T)
      ⟨some .sc0, v, stk c T (Code.init x) 0 0⟩ ⟨some .tmo, v', stk c 0 k'' 0 0⟩) := by
  have hM : (codeCells c).length ≤ (codeCells c).length + 2 := by omega
  obtain ⟨h₁, h₂⟩ := loop_run hM T (Code.init x) (bounded_init x (by omega)) v
  refine ⟨fun h ↦ h₁ ((Code.isSome_evalSteps_iff_step_eq_none c x T).1 h), fun h ↦ ?_⟩
  cases hs : c.step (c.cfgAfter x T) with
  | none =>
    have := (Code.isSome_evalSteps_iff_step_eq_none c x T).2 hs
    simp [h] at this
  | some k'' =>
    obtain ⟨v', hr⟩ := h₂ k'' hs
    exact ⟨v', k'', hr⟩

/-! ### Reading the input and writing the output -/

/-- Read the number on top of `a` into the empty counter `b`, dropping its marker. -/
private theorem readTo_run {x y z : Lab} {a b : K} (hab : a ≠ b)
    (hx : prog x = moveB a b dU (fun _ ↦ true) x y) (hy : prog y = decr a z z) (n : ℕ)
    (rest : List Bool) (v : Bool) (S : ∀ j, List (Γ j)) (ha : S a = cell n ++ rest)
    (hb : S b = []) :
    ∃ v', Run prog (n + 2) ⟨some x, v, S⟩
      ⟨some z, v', update (update S a rest) b (cnt true n)⟩ := by
  obtain ⟨v₁, S₁, h₁, h1a, h1b, h1k⟩ := moveB_run hx hab (cnt true n) (cnt true n)
    (false :: rest) v S (by simp [ha, cell]) (isBitBlock_cnt n) (by simp [EndsBitBlock, dU])
  have h₂ := decr_run_pos hy v₁ (S := S₁) h1a
  have hlen : (cnt true n).length + 1 = n + 1 := by simp
  rw [hlen] at h₁
  have hS : update S₁ a rest = update (update S a rest) b (cnt true n) := by
    funext j
    by_cases h1 : j = a
    · subst h1; simp [update_of_ne hab]
    by_cases h2 : j = b
    · subst h2; simp [update_of_ne hab.symm, h1b, hb]
    · simp [update_of_ne h1, update_of_ne h2, h1k j h1 h2]
  rw [hS] at h₂
  exact ⟨_, h₁.trans h₂⟩

/-- Pop the first cell of the cells on `a` into the empty counter `b`; an empty stack gives a
blank cell. -/
private theorem popCell_run {x y z : Lab} {a b : K} (hab : a ≠ b)
    (hx : prog x = moveB a b dU (fun _ ↦ true) x y) (hy : prog y = decr a z z) (l : List ℕ)
    (v : Bool) (S : ∀ j, List (Γ j)) (ha : S a = cells l) (hb : S b = []) :
    ∃ v', Run prog (l.headI + 2) ⟨some x, v, S⟩
      ⟨some z, v', update (update S a (cells l.tail)) b (cnt true l.headI)⟩ := by
  cases l with
  | nil =>
    obtain ⟨v₁, S₁, h₁, h1a, h1b, h1k⟩ := moveB_run hx hab [] [] [] v S (by simp [ha, cells])
      (by simp [IsBitBlock]) (by simp [EndsBitBlock])
    have h₂ := decr_run_zero hy v₁ (S := S₁) h1a
    have hS : S₁ = update (update S a (cells [].tail)) b (cnt true ([] : List ℕ).headI) := by
      funext j
      by_cases h1 : j = a
      · subst h1; simp [update_of_ne hab, h1a, cells]
      by_cases h2 : j = b
      · subst h2; simp [h1b, hb]
      · simp [update_of_ne h1, update_of_ne h2, h1k j h1 h2]
    have h := h₁.trans h₂
    rw [hS] at h
    exact ⟨_, h.of_eq (by simp)⟩
  | cons n l =>
    exact readTo_run hab hx hy n (cells l) v S (by simp [ha, cells]) hb

/-- Reading the input symbols: their cells move to `P`, reversed, up to the blank cell. -/
private theorem xloop_run : ∀ (l : List ℕ), (∀ n ∈ l, 1 ≤ n) → ∀ (rest : List Bool) (v : Bool)
    (S : ∀ j, List (Γ j)), S .X = cells l ++ false :: rest →
    ∃ v', Run prog ((l.map (· + 3)).sum + 2) ⟨some .px0, v, S⟩
      ⟨some .px4, v', update (update S .X rest) .P ((cells l).reverse ++ S .P)⟩ := by
  intro l
  induction l with
  | nil =>
    intro _ rest v S hX
    have h₁ : Run prog 1 ⟨some .px0, v, S⟩ ⟨some .px3, false, S⟩ :=
      Run.single (by simp [prog, TM2.stepAux, hX, isBit, dU, cells])
    have h₂ := decr_run_pos (M := prog) (self := .px3) (ifZero := .px4) (ifPos := .px4)
      (k := .X) rfl false (S := S) (x := false) (r := rest) (by simpa [cells] using hX)
    have hS : update S .X rest = update (update S .X rest) .P ((cells []).reverse ++ S .P) := by
      funext j
      by_cases h1 : j = .P
      · subst h1; simp [cells]
      · simp [update_of_ne h1]
    rw [hS] at h₂
    exact ⟨_, h₁.trans h₂⟩
  | cons n l ih =>
    intro hl rest v S hX
    have hn : 1 ≤ n := hl n List.mem_cons_self
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hX' : S .X = cnt true (n' + 1) ++ false :: (cells l ++ false :: rest) := by
      simp [hX, cells, cell]
    have h₁ : Run prog 1 ⟨some .px0, v, S⟩ ⟨some .px1, true, S⟩ :=
      Run.single (by simp [prog, TM2.stepAux, hX', isBit, dU, cnt_succ])
    obtain ⟨v₂, S₂, h₂, h2X, h2P, h2k⟩ := moveB_run (M := prog) (self := .px1) (next := .px2)
      (a := .X) (b := .P) (d := dU) (g := fun _ ↦ true) rfl (by decide) (cnt true (n' + 1))
      (cnt true (n' + 1)) _ true S hX' (isBitBlock_cnt _) (by simp [EndsBitBlock, dU])
    have h₃ : Run prog 1 ⟨some .px2, v₂, S₂⟩
        ⟨some .px0, v₂, update (update S₂ .X (cells l ++ false :: rest)) .P (false :: S₂ .P)⟩ :=
      Run.single (by simp [prog, TM2.stepAux, h2X])
    obtain ⟨v₄, h₄⟩ := ih (fun m hm ↦ hl m (List.mem_cons_of_mem _ hm)) rest v₂
      (update (update S₂ .X (cells l ++ false :: rest)) .P (false :: S₂ .P)) (by simp)
    have hS : update (update (update (update S₂ .X (cells l ++ false :: rest)) .P
        (false :: S₂ .P)) .X rest) .P ((cells l).reverse ++
        update (update S₂ .X (cells l ++ false :: rest)) .P (false :: S₂ .P) .P) =
        update (update S .X rest) .P ((cells ((n' + 1) :: l)).reverse ++ S .P) := by
      funext j
      by_cases h1 : j = .P
      · subst h1; simp [h2P, cells, cell]
      by_cases h2 : j = .X
      · subst h2; simp
      · simp [update_of_ne h1, update_of_ne h2, h2k j h2 h1]
    rw [hS] at h₄
    have hlen : (cnt true (n' + 1)).length + 1 = n' + 2 := by simp
    rw [hlen] at h₂
    refine ⟨_, (((h₁.trans h₂).trans h₃).trans h₄).of_eq ?_⟩
    simp only [List.map_cons, List.sum_cons]
    omega

/-- **Input encoding of the clocked universal machine.** For a code $c$, a list of bits $x$ and a
clock $T$, the input of the clocked universal machine is the list of bits formed by the cell of
$T$, then the cells of the input word of $x$, then the cell of $0$ (a blank cell, the single bit
false), then the code stack of $c$ in reverse order. -/
def encIn (c : Code) (x : List Bool) (T : ℕ) : List Bool :=
  cell T ++ (cells (input x) ++ (false :: (codeCells c).reverse))

/-- **Cost of reading the input.** For a code $c$, a list of bits $x$ and a natural number $T$, let
$w_1, \dots, w_n$ be the input word of $x$ (false as the symbol $1$, true as $2$), with $w_1$ read
as $0$ when $x$ is empty, let $S_j = \sum_{i=1}^{n} (w_i + j)$, and let $m$ be the length of the
code stack of $c$. The cost of reading the input is
$T + 2 + (S_3 + 2) + (S_1 + 1) + (w_1 + 2) + (m + 1)$. -/
def parseTime (c : Code) (x : List Bool) (T : ℕ) : ℕ :=
  T + 2 + (((input x).map (· + 3)).sum + 2) + ((cells (input x)).length + 1) +
    ((input x).headI + 2) + ((codeCells c).length + 1)

/-- **Reading the input.** Let $c$ be a code, $x$ a list of bits and $T$ a natural number, and let
$p$ be the cost of reading the input of $c$, $x$ and $T$. Started at the label $\mathsf{pc0}$ with
state bit false, the input encoding of $c$, $x$ and $T$ on the stack $X$ and every other stack
empty, the clocked universal program reaches the label $\mathsf{sc0}$ in exactly $p$ steps, with
some state bit and the stacks of the code $c$, the clock $T$ and the initial configuration on $x$,
with next state and action $0$. -/
theorem parse_run (c : Code) (x : List Bool) (T : ℕ) :
    ∃ v', Run prog (parseTime c x T) ⟨some .pc0, false, update (fun _ ↦ []) .X (encIn c x T)⟩
      ⟨some .sc0, v', stk c T (Code.init x) 0 0⟩ := by
  set S0 : ∀ j, List (Γ j) := update (fun _ ↦ []) .X (encIn c x T)
  set R1 := cells (input x) ++ (false :: (codeCells c).reverse)
  obtain ⟨v₁, h₁⟩ := readTo_run (x := .pc0) (y := .pc1) (z := .px0) (a := .X) (b := .Ck)
    (by decide) rfl rfl T R1 false S0 (by simp [S0, encIn, R1]) (by simp [S0])
  set S1 := update (update S0 .X R1) .Ck (cnt true T)
  have hin : ∀ n ∈ input x, 1 ≤ n := by
    intro n hn
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hn
    cases b <;> simp [bitSym]
  obtain ⟨v₂, h₂⟩ := xloop_run (input x) hin ((codeCells c).reverse) v₁ S1 (by simp [S1, R1])
  set S2 := update (update S1 .X (codeCells c).reverse) .P ((cells (input x)).reverse ++ S1 .P)
  obtain ⟨v₃, h₃⟩ := moveAll_run (x := .px4) (y := .px5) (a := .P) (b := .R) (by decide) rfl v₂ S2
  set S3 := update (update S2 .P []) .R ((S2 .P).reverse ++ S2 .R)
  obtain ⟨v₄, h₄⟩ := popCell_run (x := .px5) (y := .px6) (z := .pk0) (a := .R) (b := .H)
    (by decide) rfl rfl (input x) v₃ S3 (by simp [S3, S2, S1, S0]) (by simp [S3, S2, S1, S0])
  set S4 := update (update S3 .R (cells (input x).tail)) .H (cnt true (input x).headI)
  obtain ⟨v₅, h₅⟩ := moveAll_run (x := .pk0) (y := .sc0) (a := .X) (b := .C) (by decide) rfl v₄ S4
  have hr := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  have hS : update (update S4 .X []) .C ((S4 .X).reverse ++ S4 .C) = stk c T (Code.init x) 0 0 := by
    funext j
    cases j <;> simp [S4, S3, S2, S1, S0, stk, Code.init, cells]
  rw [hS] at hr
  refine ⟨_, hr.of_eq ?_⟩
  simp [parseTime, S4, S3, S2, S1, S0]

/-- Drop the markers on top of `P`. -/
private theorem dropF_run : ∀ (l : List Bool) (v : Bool) (S : ∀ j, List (Γ j)), S .P = l →
    ∃ v', Run prog ((l.takeWhile (· == false)).length + 1) ⟨some .o3, v, S⟩
      ⟨some .o4, v', update S .P (l.dropWhile (· == false))⟩
  | [], v, S, h => by
    refine ⟨false, Run.single ?_⟩
    have hu : update S .P [] = S := by rw [← h, update_eq_self]
    simp [prog, TM2.stepAux, h, hu]
  | true :: l, v, S, h => by
    refine ⟨false, Run.single ?_⟩
    have hu : update S .P (true :: l) = S := by rw [← h, update_eq_self]
    simp [prog, TM2.stepAux, h, hu]
  | false :: l, v, S, h => by
    have h₁ : Run prog 1 ⟨some .o3, v, S⟩ ⟨some .o3, true, update S .P l⟩ :=
      Run.single (by simp [prog, TM2.stepAux, h])
    obtain ⟨v', h₂⟩ := dropF_run l true (update S .P l) (by simp)
    rw [update_idem] at h₂
    exact ⟨v', (h₁.trans h₂).of_eq (by simp; omega)⟩

/-- Put one marker back on `P` unless it is empty. -/
private theorem o4_run (v : Bool) (S : ∀ j, List (Γ j)) :
    ∃ v', Run prog 1 ⟨some .o4, v, S⟩
      ⟨some .o5, v', update S .P (if S .P = [] then [] else false :: S .P)⟩ := by
  cases h : S .P with
  | nil =>
    refine ⟨false, Run.single ?_⟩
    have hu : update S .P [] = S := by rw [← h, update_eq_self]
    simp [prog, TM2.stepAux, h, hu]
  | cons b l =>
    exact ⟨true, Run.single (by simp [prog, TM2.stepAux, h])⟩

/-- Reversing the cells of a list, dropping the leading markers and putting one back unless
nothing is left, gives the reversed cells of the list without its trailing blanks. -/
private theorem trim_cells (l : List ℕ) :
    (if (cells l).reverse.dropWhile (· == false) = [] then []
      else false :: (cells l).reverse.dropWhile (· == false)) =
      (cells (l.rdropWhile (· == 0))).reverse := by
  induction l using List.reverseRecOn with
  | nil => simp [cells]
  | append_singleton l a ih =>
    have hc : (cells (l ++ [a])).reverse = false :: (cnt true a ++ (cells l).reverse) := by
      simp [cells, cell, List.flatMap_append]
    rw [hc]
    rcases a with _ | a
    · simpa [List.rdropWhile_concat_pos] using ih
    · rw [List.rdropWhile_concat_neg _ _ (a + 1) (by simp), hc]
      simp [cnt_succ]

/-- **Output encoding of the clocked universal machine.** The output bits of an optional list of
numbers: no result (a timeout) is encoded as the single bit false, and a result $l$ is encoded as
the bit true followed by the cells of $l$, where a number $n$ is written as $n$ bits true followed
by one bit false. -/
def encOut : Option (List ℕ) → List Bool
  | none => [false]
  | some l => true :: cells l

/-- **Writing the output.** Let $c$ be a code, $t$ a natural number, $k$ a configuration and $v$ a
bit, and let $N$ be the length of the cells of the head symbol of $k$ followed by the symbols to
its right (a symbol $a$ takes $a + 1$ bits). Started at the label $\mathsf{hlt}$ with state bit $v$
and the stacks of the code $c$, the clock $t$ and the configuration $k$ with next state and action
$0$, the clocked universal program reaches the label $\mathsf{done}$ within $4N + 8$ steps, with
some state bit and stacks in which the output stack $O$ holds the encoding of the output of $k$:
the bit true followed by the cells of the output of $k$. -/
theorem out_run (c : Code) (t : ℕ) (k : Code.Cfg) (v : Bool) :
    ∃ v' S', RunLe prog (4 * (cells (k.head :: k.right)).length + 8) ⟨some .hlt, v, stk c t k 0 0⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = encOut (some k.output) := by
  set S0 := stk c t k 0 0
  have h₁ := incr_run (M := prog) (self := .hlt) (next := .o1) (k := .R) (u := false) rfl v S0
  set S1 := update S0 .R (false :: S0 .R)
  have h₂ := xfer_run (M := prog) (self := .o1) (next := .o2) (k := .H) (ps := [⟨.R, true⟩]) rfl
    (single_nodupKeys _) (by simp) true k.head v S1 (by simp [S1, S0, stk])
  set S2 := addU [⟨K.R, true⟩] k.head (update S1 .H [])
  have h2R : S2 .R = cells (k.head :: k.right) := by
    simp [S2, S1, S0, addU_single_self, stk, cells, cell]
  obtain ⟨v₃, h₃⟩ := moveAll_run (x := .o2) (y := .o3) (a := .R) (b := .P) (by decide) rfl
    (Flag.tag false) S2
  set S3 := update (update S2 .R []) .P ((S2 .R).reverse ++ S2 .P)
  have h3P : S3 .P = (cells (k.head :: k.right)).reverse := by
    simp [S3, S2, S1, S0, addU, stk, cells, cell]
  obtain ⟨v₄, h₄⟩ := dropF_run _ v₃ S3 h3P
  set S4 := update S3 .P ((cells (k.head :: k.right)).reverse.dropWhile (· == false))
  obtain ⟨v₅, h₅⟩ := o4_run v₄ S4
  set S5 := update S4 .P (if S4 .P = [] then [] else false :: S4 .P)
  have h5P : S5 .P = (cells k.output).reverse := by
    simp only [S5, S4, update_self, Code.Cfg.output]
    exact trim_cells _
  obtain ⟨v₆, h₆⟩ := moveAll_run (x := .o5) (y := .o6) (a := .P) (b := .O) (by decide) rfl v₅ S5
  set S6 := update (update S5 .P []) .O ((S5 .P).reverse ++ S5 .O)
  have h₇ := incr_run (M := prog) (self := .o6) (next := .done) (k := .O) (u := true) rfl v₆ S6
  have hr := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇
  refine ⟨_, _, hr.le ?_, ?_⟩
  · have ht := (List.takeWhile_prefix (l := (cells (k.head :: k.right)).reverse)
      (· == false)).length_le
    have hd := List.length_dropWhile_le (p := (· == false)) (cells (k.head :: k.right)).reverse
    simp only [List.length_reverse] at ht hd
    have hlen : (S5 .P).length ≤ (cells (k.head :: k.right)).length + 1 := by
      simp only [S5, S4, update_self]
      split_ifs
      · exact Nat.zero_le _
      · rw [List.length_cons]
        exact Nat.succ_le_succ ((List.dropWhile_suffix _).length_le.trans
          (List.length_reverse ..).le)
    have hH : k.head + 1 ≤ (cells (k.head :: k.right)).length := by simp [cells, cell]
    rw [h2R]
    omega
  · have hO : S5 .O = [] := by simp [S5, S4, S3, S2, S1, S0, addU, stk]
    simp only [S6, update_self, h5P, hO, List.reverse_reverse, List.append_nil, encOut]

/-- **Writing a timeout.** Let $c$ be a code, $t$ a natural number, $k$ a configuration and $v$ a
bit. Started at the label $\mathsf{tmo}$ with state bit $v$ and the stacks of the code $c$, the
clock $t$ and the configuration $k$ with next state and action $0$, the clocked universal program
reaches the label $\mathsf{done}$ in exactly one step, with the same state bit and the same stacks
except that the output stack $O$ holds the timeout encoding, the single bit false. -/
theorem tmo_run (c : Code) (t : ℕ) (k : Code.Cfg) (v : Bool) :
    Run prog 1 ⟨some .tmo, v, stk c t k 0 0⟩
      ⟨some .done, v, update (stk c t k 0 0) .O (encOut none)⟩ :=
  incr_run (M := prog) (self := .tmo) (next := .done) (k := .O) (u := false) rfl v _

/-! ### The whole machine -/

/-- A step adds at most one cell to the tape. -/
private theorem tapeLen_stepOrStay (c : Code) (k : Code.Cfg) :
    (c.stepOrStay k).left.length + (c.stepOrStay k).right.length ≤
      k.left.length + k.right.length + 1 := by
  unfold Code.stepOrStay
  cases h : c.step k with
  | none => simp
  | some k' =>
    obtain ⟨⟨q', s⟩, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases s with _ | _ | a <;> simp [Code.Cfg.act] <;> omega

/-- After `n` clocked steps on `x`, the numbers are at most `|codeCells c| + 2` and the tape has
at most `|x| + n` cells besides the head. -/
private theorem iterate_bounds (c : Code) (x : List Bool) :
    ∀ n, Bounded ((codeCells c).length + 2) (c.stepOrStay^[n] (Code.init x)) ∧
      (c.stepOrStay^[n] (Code.init x)).left.length +
        (c.stepOrStay^[n] (Code.init x)).right.length ≤ x.length + n
  | 0 => ⟨bounded_init x (by omega), by simp [Code.init, input]⟩
  | n + 1 => by
    obtain ⟨hb, hl⟩ := iterate_bounds c x n
    rw [Function.iterate_succ_apply']
    refine ⟨?_, (tapeLen_stepOrStay c _).trans (by omega)⟩
    set k := c.stepOrStay^[n] (Code.init x)
    rw [Code.stepOrStay]
    cases h : c.step k with
    | none => exact hb
    | some k' => exact bounded_step (c := c) (by omega) hb h

/-- Cells of numbers at most `M` take at most `M + 1` symbols each. -/
private theorem length_cells_le {M : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a ≤ M) →
    (cells l).length ≤ l.length * (M + 1)
  | [], _ => by simp [cells]
  | a :: l, h => by
    have ih := length_cells_le (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [cells, List.flatMap_cons, List.length_append, length_cell, List.length_cons] at ih ⊢
    rw [Nat.succ_mul]
    omega

/-- **Step bound of the clocked universal machine.** For a code $c$, a list of bits $x$ and a
natural number $T$, the step bound of the whole machine on $(c, x, T)$ is the sum of three terms:
the cost of reading the input on $(c, x, T)$, the step bound of the clocked simulation on the
clock $T$, and the output bound $4\,(|x| + T + 1)\,(|C| + 3) + 8$, where $|x|$ is the length of
$x$ and $|C|$ is the length of the code stack of $c$. -/
def univTime (c : Code) (x : List Bool) (T : ℕ) : ℕ :=
  parseTime c x T + clockTime c T + (4 * ((x.length + T + 1) * ((codeCells c).length + 3)) + 8)

/-- **Correctness and running time of the clocked universal machine.** Let $c$ be a code, $x$ a
list of bits and $T$ a natural number. Start the clocked universal stack program at the label
$\mathrm{pc0}$ with internal bit $\mathrm{false}$, with every stack empty except $X$, which holds
the input encoding of $(c, x, T)$: the cell of $T$, the cells of the input symbols of $x$ (the
symbol $1$ for $\mathrm{false}$ and $2$ for $\mathrm{true}$), the bit $\mathrm{false}$, and the
code stack of $c$ reversed, where the cell of a number $n$ is $n$ bits $\mathrm{true}$ followed
by the bit $\mathrm{false}$. Then within at most $N(c, x, T)$ steps, where $N$ is the step bound
of the whole machine, the program reaches the label $\mathrm{done}$ (with some internal bit and
some stack contents) with the output encoding of the clocked evaluation of $c$ on $x$ with clock
$T$ on the stack $O$: the single bit $\mathrm{false}$ if the coded machine does not halt within
$T$ steps, and otherwise the bit $\mathrm{true}$ followed by the cells of its output, the tape
from the head rightwards without trailing blanks. -/
theorem univ_run (c : Code) (x : List Bool) (T : ℕ) :
    ∃ v' S', RunLe prog (univTime c x T) ⟨some .pc0, false, update (fun _ ↦ []) .X (encIn c x T)⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = encOut (c.evalSteps x T) := by
  obtain ⟨v₁, h₁⟩ := parse_run c x T
  obtain ⟨hh, ht⟩ := clocked_run c x T v₁
  cases he : c.evalSteps x T with
  | none =>
    obtain ⟨v₂, k'', h₂⟩ := ht he
    have h₃ := tmo_run c 0 k'' v₂
    refine ⟨_, _, ((h₁.le le_rfl).trans (h₂.trans (h₃.le le_rfl))).mono ?_, by simp⟩
    simp only [univTime]
    omega
  | some l =>
    obtain ⟨v₂, t', h₂⟩ := hh (by simp [he])
    obtain ⟨v₃, S', h₃, hO⟩ := out_run c t' (c.cfgAfter x T) v₂
    have hl : (c.cfgAfter x T).output = l :=
      ((Code.evalSteps_eq_some_iff_output c x T l).1 he).2
    rw [hl] at hO
    obtain ⟨⟨_, hh', -, hR⟩, hlen⟩ := iterate_bounds c x T
    have hcells : (cells ((c.cfgAfter x T).head :: (c.cfgAfter x T).right)).length ≤
        (x.length + T + 1) * ((codeCells c).length + 3) := by
      refine (length_cells_le (M := (codeCells c).length + 2) ?_).trans ?_
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hh'
        · exact hR a ha
      · refine Nat.mul_le_mul ?_ le_rfl
        simp only [List.length_cons, Code.cfgAfter] at hlen ⊢
        omega
    refine ⟨_, _, ((h₁.le le_rfl).trans (h₂.trans h₃)).mono ?_, hO⟩
    simp only [univTime]
    omega

end Cslib.Turing.Universal.Clocked
