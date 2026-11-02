/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.Diagonalization

/-!
# A polynomial-time decider for the diagonal language

The diagonal language of `Cslib.Turing.Universal.Diagonalization` for `f n = n ^ 2 + 1` is in `P`,
although no code decides it within `n ^ 2 + 1` steps: `P ⊄ CodeTime (n ↦ n ^ 2 + 1)`
(`not_P_subset_codeTime_sq_add_one`). This separates two models, the multi-stack machines of `P`
and the single-tape codes with exact step counts; it is the diagonal half of the argument of
Sipser's Theorem 9.10, not that theorem.

The decider is the composition of four machines (`TM2Composition.compComputable`):

1. the checking machine `Diag.Check.comp` decides whether the input `x` is a code stack, reading
   its entries cell by cell with `Cslib.CookLevin.readUnaryLength` and comparing consecutive keys
   as unary counters (`Diag.chkFrom`, which agrees with `decodeCodeCells`: `Diag.chkFrom_zero`);
   it writes `true :: x` or `[false]` (`Diag.Check.answer`);
2. the layout machine `Diag.Layout.comp` writes
   `cell (|x| ^ 2 + 1) ++ cells (input x) ++ false :: x.reverse` from `true :: x` (squaring with
   `TM2Program.mul_run`), and a fixed list otherwise (`Diag.Layout.layout`), which is the
   universal machine's input `encIn` of `diagArg (fun n ↦ n ^ 2 + 1) x` (`Diag.layout_answer`);
3. the clocked universal machine (`Clocked.nonempty_univPolyTime`);
4. the readout machine `Diag.Readout.comp`.

Each of the first two runs in the reduction host of `Cslib.Complexity.Host` within a quadratic
number of steps (`Diag.Check.run`: `33 (n + 1) ^ 2`; `Diag.Layout.run`: `18 (n + 1) ^ 2`).

## Main definitions

- `Cslib.Turing.Universal.Diag.chkFrom`: the cell-by-cell check of code stacks.
- `Cslib.Turing.Universal.Diag.Check.comp`, `Cslib.Turing.Universal.Diag.Layout.comp`: the
  checking and layout machines.
- `Cslib.Turing.Universal.Diag.reformat`: the reformatting machine of `nonempty_diag_polyTime`
  for `n ↦ n ^ 2 + 1`.

## Main results

- `Diag.chkFrom_iff`, `Diag.chkFrom_zero`: the check recognizes code stacks.
- `Diag.Check.run`, `Diag.Layout.run`: the runs of the two machines, with their step bounds.
- `nonempty_diag_sq_add_one_polyTime`: a `FinTM2` decides `diag (fun n ↦ n ^ 2 + 1)` on raw bits
  in polynomial time.
- `diag_sq_add_one_mem_P`: `diag (fun n ↦ n ^ 2 + 1) ∈ P`.
- `exists_mem_P_not_mem_codeTime_sq_add_one`, `not_P_subset_codeTime_sq_add_one`:
  `P ⊄ CodeTime (n ↦ n ^ 2 + 1)`.

## References

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, proof of
  Theorem 9.10 (the decider `D` for the diagonal language).
-/

@[expose] public section

set_option autoImplicit false

open _root_.Turing MetaMathlibExt.ComplexityTheory

namespace Cslib.Turing.Universal

open Clocked

namespace Diag

open Cslib.CookLevin

/-! ### Checking code stacks cell by cell -/

/-- `readUnaryLength` fails exactly on lists of units. -/
private theorem readUnaryLength_eq_none {x : List Bool} :
    readUnaryLength x = none ↔ x = List.replicate x.length true := by
  induction x with
  | nil => simp [readUnaryLength]
  | cons b x ih =>
    cases b with
    | false => simp [readUnaryLength, List.replicate_succ]
    | true =>
      simp only [readUnaryLength, Option.map_eq_none_iff, ih, List.length_cons, List.replicate_succ,
        List.cons.injEq, true_and]

/-- A cell read off a list shortens it by the cell's length. -/
private theorem length_of_readUnaryLength_eq_some {x : List Bool} {n : ℕ} {r : List Bool}
    (h : readUnaryLength x = some (n, r)) : x.length = n + 1 + r.length := by
  rw [readUnaryLength_eq_some_iff_cell.1 h]
  simp [cell]
  omega

/-- **Cell-by-cell check of a code stack.** The check of a bit list $x$ from a key $(p_q, p_a)$
of natural numbers is defined as follows. The empty list passes. Otherwise, calling the cell of a
number $n$ the $n$ bits $\mathrm{true}$ followed by one bit $\mathrm{false}$, read four cells off
the front of $x$, those of $q$, $a$, $q'$ and $s$ in this order, leaving the rest $r$. The check
fails if one of these cells cannot be read because what remains contains no bit
$\mathrm{false}$, or if the key $(q, a)$ is lexicographically below $(p_q, p_a)$, that is,
unless $p_q < q$, or $p_q = q$ and $p_a \le a$. Otherwise its result is the check of $r$ from
the key $(q, a + 1)$.

The reformatting machine checks its input this way. -/
def chkFrom (pq pa : ℕ) (x : List Bool) : Bool :=
  match x with
  | [] => true
  | b :: x' =>
    match _h1 : readUnaryLength (b :: x') with
    | none => false
    | some (q, x1) =>
      match _h2 : readUnaryLength x1 with
      | none => false
      | some (a, x2) =>
        if pq < q ∨ pq = q ∧ pa ≤ a then
          match _h3 : readUnaryLength x2 with
          | none => false
          | some (_, x3) =>
            match h4 : readUnaryLength x3 with
            | none => false
            | some (_, x4) => chkFrom q (a + 1) x4
        else false
termination_by x.length
decreasing_by
  have e1 := congrArg List.length (readUnaryLength_eq_some_iff_cell.1 _h1)
  have e2 := congrArg List.length (readUnaryLength_eq_some_iff_cell.1 _h2)
  have e3 := congrArg List.length (readUnaryLength_eq_some_iff_cell.1 _h3)
  have e4 := congrArg List.length (readUnaryLength_eq_some_iff_cell.1 h4)
  simp only [cell, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at e1 e2 e3 e4
  simp only [List.length_cons]
  omega

/-- The cells of an entry list, entry by entry. -/
private theorem cells_entryNums_cons (e : ℕ × ℕ × ℕ × ℕ) (es : List (ℕ × ℕ × ℕ × ℕ)) :
    cells (entryNums (e :: es)) =
      cell e.1 ++ (cell e.2.1 ++ (cell e.2.2.1 ++ (cell e.2.2.2 ++ cells (entryNums es)))) := by
  simp [cells, entryNums]

/-- Reading the first cell. -/
private theorem readUnaryLength_cell_append (n : ℕ) (r : List Bool) :
    readUnaryLength (cell n ++ r) = some (n, r) :=
  readUnaryLength_eq_some_iff_cell.2 rfl

/-- **The cell-by-cell check recognizes code stacks.** For all natural numbers $p_q, p_a$ and
every bit list $x$, the cell-by-cell check of $x$ from the key $(p_q, p_a)$ succeeds if and only
if there is a list of $m \ge 0$ entries $(q_1, a_1, q'_1, s_1), \dots, (q_m, a_m, q'_m, s_m)$ of
natural numbers such that $x$ is the concatenation of the cells of
$q_1, a_1, q'_1, s_1, \dots, q_m, a_m, q'_m, s_m$, in this order, and the keys $(q_i, a_i)$
strictly increase in lexicographic order, starting at $(p_q, p_a)$ or above. Here the cell of a
number $n$ is $n$ bits $\mathrm{true}$ followed by one bit $\mathrm{false}$. -/
theorem chkFrom_iff (pq pa : ℕ) (x : List Bool) :
    chkFrom pq pa x = true ↔ ∃ es, x = cells (entryNums es) ∧ keysAscendFrom pq pa es = true := by
  induction h : x.length using Nat.strong_induction_on generalizing x pq pa with
  | _ n ih =>
  subst h
  match x with
  | [] =>
    rw [chkFrom]
    exact ⟨fun _ ↦ ⟨[], rfl, rfl⟩, fun _ ↦ rfl⟩
  | b :: x' =>
    rw [chkFrom]
    split
    · next h1 =>
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro es hx _
      cases es with
      | nil => simp [cells, entryNums] at hx
      | cons e es' =>
        rw [hx, cells_entryNums_cons, readUnaryLength_cell_append] at h1
        cases h1
    · next q x1 h1 =>
      have hx1 := readUnaryLength_eq_some_iff_cell.1 h1
      split
      · next h2 =>
        simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro es hx _
        cases es with
        | nil => simp [cells, entryNums] at hx
        | cons e es' =>
          rw [hx, cells_entryNums_cons, readUnaryLength_cell_append] at h1
          cases h1
          rw [readUnaryLength_cell_append] at h2
          cases h2
      · next a x2 h2 =>
        have hx2 := readUnaryLength_eq_some_iff_cell.1 h2
        split
        · next hkey =>
          split
          · next h3 =>
            simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
            intro es hx _
            cases es with
            | nil => simp [cells, entryNums] at hx
            | cons e es' =>
              rw [hx, cells_entryNums_cons, readUnaryLength_cell_append] at h1
              cases h1
              rw [readUnaryLength_cell_append] at h2
              cases h2
              rw [readUnaryLength_cell_append] at h3
              cases h3
          · next q' x3 h3 =>
            have hx3 := readUnaryLength_eq_some_iff_cell.1 h3
            split
            · next h4 =>
              simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
              intro es hx _
              cases es with
              | nil => simp [cells, entryNums] at hx
              | cons e es' =>
                rw [hx, cells_entryNums_cons, readUnaryLength_cell_append] at h1
                cases h1
                rw [readUnaryLength_cell_append] at h2
                cases h2
                rw [readUnaryLength_cell_append] at h3
                cases h3
                rw [readUnaryLength_cell_append] at h4
                cases h4
            · next s x4 h4 =>
              have hx4 := readUnaryLength_eq_some_iff_cell.1 h4
              have hlen : x4.length < (b :: x').length := by
                rw [hx1, hx2, hx3, hx4]
                simp [cell]
                omega
              rw [ih _ hlen q (a + 1) x4 rfl]
              constructor
              · rintro ⟨es', rfl, hk⟩
                refine ⟨(q, a, q', s) :: es', ?_, ?_⟩
                · rw [cells_entryNums_cons, hx1, hx2, hx3, hx4]
                · simp only [keysAscendFrom, Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨hkey, hk⟩
              · rintro ⟨es, hx, hk⟩
                cases es with
                | nil => simp [cells, entryNums] at hx
                | cons e es' =>
                  obtain ⟨e1, e2, e3, e4⟩ := e
                  rw [hx, cells_entryNums_cons, readUnaryLength_cell_append] at h1
                  cases h1
                  rw [readUnaryLength_cell_append] at h2
                  cases h2
                  rw [readUnaryLength_cell_append] at h3
                  cases h3
                  rw [readUnaryLength_cell_append] at h4
                  cases h4
                  simp only [keysAscendFrom, Bool.and_eq_true, decide_eq_true_eq] at hk
                  exact ⟨es', rfl, hk.2⟩
        · next hkey =>
          simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
          intro es hx hk
          cases es with
          | nil => simp [cells, entryNums] at hx
          | cons e es' =>
            obtain ⟨e1, e2, e3, e4⟩ := e
            rw [hx, cells_entryNums_cons, readUnaryLength_cell_append] at h1
            cases h1
            rw [readUnaryLength_cell_append] at h2
            cases h2
            simp only [keysAscendFrom, Bool.and_eq_true, decide_eq_true_eq] at hk
            exact hkey hk.1

/-! #### Unfolding the check -/

/-- The check accepts the empty list. -/
private theorem chkFrom_nil (pq pa : ℕ) : chkFrom pq pa [] = true := by rw [chkFrom]

/-- The check rejects a list without a first cell. -/
private theorem chkFrom_of_none₁ {pq pa : ℕ} {x : List Bool} (hx : x ≠ [])
    (h : readUnaryLength x = none) :
    chkFrom pq pa x = false := by
  match x, hx with
  | b :: x', _ =>
    rw [chkFrom]
    split
    · rfl
    · next h1 => rw [h] at h1; cases h1

/-- The check rejects a list without a second cell. -/
private theorem chkFrom_of_none₂ {pq pa q : ℕ} {x x1 : List Bool}
    (h1 : readUnaryLength x = some (q, x1))
    (h : readUnaryLength x1 = none) : chkFrom pq pa x = false := by
  match x, h1 with
  | b :: x', h1 =>
    rw [chkFrom]
    split
    · rfl
    · next q₀ x₀ h1' =>
      rw [h1] at h1'
      cases h1'
      split
      · rfl
      · next h2' => rw [h] at h2'; cases h2'

/-- The check rejects a key below the bound. -/
private theorem chkFrom_of_key {pq pa q a : ℕ} {x x1 x2 : List Bool}
    (h1 : readUnaryLength x = some (q, x1)) (h2 : readUnaryLength x1 = some (a, x2))
    (hk : ¬(pq < q ∨ pq = q ∧ pa ≤ a)) :
    chkFrom pq pa x = false := by
  match x, h1 with
  | b :: x', h1 =>
    rw [chkFrom]
    split
    · rfl
    · next q₀ x₀ h1' =>
      rw [h1] at h1'
      cases h1'
      split
      · rfl
      · next a₀ x₀' h2' =>
        rw [h2] at h2'
        cases h2'
        simp only [hk, ↓reduceIte]

/-- The check rejects a list without a third cell. -/
private theorem chkFrom_of_none₃ {pq pa q a : ℕ} {x x1 x2 : List Bool}
    (h1 : readUnaryLength x = some (q, x1)) (h2 : readUnaryLength x1 = some (a, x2))
    (hk : pq < q ∨ pq = q ∧ pa ≤ a) (h : readUnaryLength x2 = none) : chkFrom pq pa x = false := by
  match x, h1 with
  | b :: x', h1 =>
    rw [chkFrom]
    split
    · rfl
    · next q₀ x₀ h1' =>
      rw [h1] at h1'
      cases h1'
      split
      · rfl
      · next a₀ x₀' h2' =>
        rw [h2] at h2'
        cases h2'
        simp only [hk, ↓reduceIte]
        split
        · rfl
        · next h3' => rw [h] at h3'; cases h3'

/-- The check rejects a list without a fourth cell. -/
private theorem chkFrom_of_none₄ {pq pa q a q' : ℕ} {x x1 x2 x3 : List Bool}
    (h1 : readUnaryLength x = some (q, x1)) (h2 : readUnaryLength x1 = some (a, x2))
    (hk : pq < q ∨ pq = q ∧ pa ≤ a) (h3 : readUnaryLength x2 = some (q', x3))
    (h : readUnaryLength x3 = none) : chkFrom pq pa x = false := by
  match x, h1 with
  | b :: x', h1 =>
    rw [chkFrom]
    split
    · rfl
    · next q₀ x₀ h1' =>
      rw [h1] at h1'
      cases h1'
      split
      · rfl
      · next a₀ x₀' h2' =>
        rw [h2] at h2'
        cases h2'
        simp only [hk, ↓reduceIte]
        split
        · rfl
        · next h3' =>
          rw [h3] at h3'
          cases h3'
          split
          · rfl
          · next h4' => rw [h] at h4'; cases h4'

/-- After a whole entry, the check goes on from the next key. -/
private theorem chkFrom_of_entry {pq pa q a q' s : ℕ} {x x1 x2 x3 x4 : List Bool}
    (h1 : readUnaryLength x = some (q, x1)) (h2 : readUnaryLength x1 = some (a, x2))
    (hk : pq < q ∨ pq = q ∧ pa ≤ a) (h3 : readUnaryLength x2 = some (q', x3))
    (h4 : readUnaryLength x3 = some (s, x4)) : chkFrom pq pa x = chkFrom q (a + 1) x4 := by
  match x, h1 with
  | b :: x', h1 =>
    rw [chkFrom]
    split
    · next h1' => rw [h1] at h1'; cases h1'
    · next q₀ x₀ h1' =>
      rw [h1] at h1'
      cases h1'
      split
      · next h2' => rw [h2] at h2'; cases h2'
      · next a₀ x₀' h2' =>
        rw [h2] at h2'
        cases h2'
        simp only [hk, ↓reduceIte]
        split
        · next h3' => rw [h3] at h3'; cases h3'
        · next h3' =>
          rw [h3] at h3'
          cases h3'
          split
          · next h4' => rw [h4] at h4'; cases h4'
          · next h4' =>
            rw [h4] at h4'
            cases h4'
            rfl

/-! ### The checking machine -/

namespace Check

open Function MetaMathlibExt.TM2Program

/-- **Stacks of the checking machine.** The checking machine has twelve stacks, named
$X, Y, W, V, Q, A, P_Q, P_A, T_1, T_2, J, O$. -/
inductive K | X | Y | W | V | Q | A | PQ | PA | T1 | T2 | J | O
  deriving DecidableEq

/-- Finitely many stacks. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .Y, .W, .V, .Q, .A, .PQ, .PA, .T1, .T2, .J, .O], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the checking machine.** The labels of the checking machine: 23 labels without
arguments and four families of labels indexed by the outcome of a comparison ($<$, $=$ or $>$),
35 distinct labels in all. -/
inductive Lab
  | dupP | dupQ | cpy | lp | rq0 | rq1 | ra0 | ra1
  | cq | cqR (o : Ordering) | cqRB (o : Ordering) | ca | caR (o : Ordering) | caRB (o : Ordering)
  | sk0 | sk1 | sk2 | sk3 | dr0 | dr1 | mv0 | mv1 | inc | okO | okT | bad | done
  deriving DecidableEq

/-- Finitely many labels. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.dupP, .dupQ, .cpy, .lp, .rq0, .rq1, .ra0, .ra1, .cq, .cqR .lt, .cqR .eq,
    .cqR .gt, .cqRB .lt, .cqRB .eq, .cqRB .gt, .ca, .caR .lt, .caR .eq, .caR .gt, .caRB .lt,
    .caRB .eq, .caRB .gt, .sk0, .sk1, .sk2, .sk3, .dr0, .dr1, .mv0, .mv1, .inc, .okO, .okT, .bad,
    .done], by decide⟩
  complete := fun x => by
    cases x
    all_goals (try cases ‹Ordering›)
    all_goals decide

/-- **Stack alphabet of the layout machine.** Every stack of the layout machine holds bits: the
alphabet of each stack is the type of Booleans. -/
abbrev Γ : K → Type := fun _ => Bool

/-- **Branch after comparing states.** The label the checking machine goes to after comparing the
bound $p$ for the state (the state of the previous key, or $0$ at the first entry) with the
state $q$ of the current key: if $p < q$, the label $\mathsf{sk0}$, where it starts skipping the
rest of the entry; if $p = q$, the label $\mathsf{ca}$, where it compares the symbols; if
$p > q$, the label $\mathsf{bad}$, where it rejects. -/
def outQ : Ordering → Lab
  | .lt => .sk0
  | .eq => .ca
  | .gt => .bad

/-- **Branch after comparing symbols.** The label the checking machine goes to after comparing
the bound $p$ for the symbol with the symbol $a$ of the current key: if $p > a$, the label
$\mathsf{bad}$, where it rejects; if $p < a$ or $p = a$, the label $\mathsf{sk0}$, where it starts
skipping the rest of the entry. -/
def outA : Ordering → Lab
  | .gt => .bad
  | _ => .sk0

/-- **Program of the checking machine.** Writing $1$ for true and $0$ for false, this is the
program of a multi-stack machine whose stacks $X, Y, W, V, Q, A, P_Q, P_A, T_1, T_2, J, O$ all
hold bits. To read a cell from $V$ onto a stack $S$ means to pop the leading $1$s of $V$, pushing
a $1$ on $S$ for each, and then to pop the $0$ that follows; if $V$ is empty at that point, the
machine rejects. From its first label the program pops the bits of $X$ one at a time, pushing
each onto both $Y$ and $W$, and then pops the bits of $W$ one at a time onto $V$. Then it loops.
If $V$ is empty, it pops the bits of $Y$ one at a time onto $O$, pushes a $1$ on $O$ and halts.
Otherwise it reads a cell from $V$ onto $Q$ and then one onto $A$. With $p_Q$, $q$, $p_A$, $a$
the numbers of bits on $P_Q$, $Q$, $P_A$, $A$, it compares $p_Q$ with $q$ and, if they are
equal, $p_A$ with $a$, afterwards pushing back as many $1$s as it popped from each. If
$p_Q > q$, or $p_Q = q$ and $p_A > a$, it rejects; otherwise it reads two more cells from $V$
onto $J$, empties $P_Q$ and $P_A$, moves $Q$ onto $P_Q$ and $A$ onto $P_A$ (pushing a $1$ for
each bit popped), pushes one more $1$ on $P_A$ and loops again. Rejecting pushes a single $0$ on
$O$ and halts. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .dupP => .peek .X (fun _ o ↦ o.isSome) (.branch id (.goto fun _ ↦ .dupQ) (.goto fun _ ↦ .cpy))
  | .dupQ => .pop .X (fun _ o ↦ o.getD false) (.branch id
      (.push .Y (fun _ ↦ true) (.push .W (fun _ ↦ true) (.goto fun _ ↦ .dupP)))
      (.push .Y (fun _ ↦ false) (.push .W (fun _ ↦ false) (.goto fun _ ↦ .dupP))))
  | .cpy => moveB .W .V some id .cpy .lp
  | .lp => .peek .V (fun _ o ↦ o.isSome) (.branch id (.goto fun _ ↦ .rq0) (.goto fun _ ↦ .okO))
  | .rq0 => moveB .V .Q dU (fun _ ↦ true) .rq0 .rq1
  | .rq1 => decr .V .bad .ra0
  | .ra0 => moveB .V .A dU (fun _ ↦ true) .ra0 .ra1
  | .ra1 => decr .V .bad .cq
  | .cq => cmpStep .PQ .Q .T1 .T2 true true .cq (.cqR .lt) (.cqR .eq) (.cqR .gt)
  | .cqR o => xfer .T1 [⟨.PQ, true⟩] (.cqR o) (.cqRB o)
  | .cqRB o => xfer .T2 [⟨.Q, true⟩] (.cqRB o) (outQ o)
  | .ca => cmpStep .PA .A .T1 .T2 true true .ca (.caR .lt) (.caR .eq) (.caR .gt)
  | .caR o => xfer .T1 [⟨.PA, true⟩] (.caR o) (.caRB o)
  | .caRB o => xfer .T2 [⟨.A, true⟩] (.caRB o) (outA o)
  | .sk0 => moveB .V .J dU (fun _ ↦ true) .sk0 .sk1
  | .sk1 => decr .V .bad .sk2
  | .sk2 => moveB .V .J dU (fun _ ↦ true) .sk2 .sk3
  | .sk3 => decr .V .bad .dr0
  | .dr0 => xfer .PQ [] .dr0 .dr1
  | .dr1 => xfer .PA [] .dr1 .mv0
  | .mv0 => xfer .Q [⟨.PQ, true⟩] .mv0 .mv1
  | .mv1 => xfer .A [⟨.PA, true⟩] .mv1 .inc
  | .inc => incr .PA true .lp
  | .okO => moveB .Y .O some id .okO .okT
  | .okT => incr .O true .done
  | .bad => emit .O [false] .done
  | .done => .halt

/-- Reading a cell from `V` onto `b`. -/
private theorem read_run_some {r0 r1 next : Lab} {b : K} (hb : K.V ≠ b)
    (h0 : prog r0 = moveB .V b dU (fun _ ↦ true) r0 r1) (h1 : prog r1 = decr .V .bad next)
    {x r : List Bool} {n : ℕ} (hx : readUnaryLength x = some (n, r)) (v : Bool)
    (S : ∀ k, List (Γ k)) (hV : S .V = x) :
    ∃ v' S', Run prog (n + 2) ⟨some r0, v, S⟩ ⟨some next, v', S'⟩ ∧ S' .V = r ∧
      S' b = List.replicate n true ++ S b ∧ ∀ k, k ≠ .V → k ≠ b → S' k = S k := by
  have hx' := readUnaryLength_eq_some_iff_cell.1 hx
  obtain ⟨v₁, S₁, h₁, h1V, h1b, h1k⟩ := moveB_run h0 hb (List.replicate n true)
    (List.replicate n true) (false :: r) v S (by rw [hV, hx']; simp [cell])
    (by simp [IsBitBlock, dU]) (by simp [EndsBitBlock, dU])
  have h₂ := decr_run_pos h1 v₁ (S := S₁) h1V
  refine ⟨_, _, (h₁.trans h₂).of_eq (by simp), by simp, ?_, fun k hk1 hk2 ↦ ?_⟩
  · rw [update_of_ne (Ne.symm hb), h1b]
    simp [List.reverse_replicate]
  · rw [update_of_ne hk1, h1k k hk1 hk2]

/-- Reading a cell from `V` fails when `V` holds only units. -/
private theorem read_run_none {r0 r1 next : Lab} {b : K} (hb : K.V ≠ b)
    (h0 : prog r0 = moveB .V b dU (fun _ ↦ true) r0 r1) (h1 : prog r1 = decr .V .bad next)
    {x : List Bool} (hx : readUnaryLength x = none) (v : Bool)
    (S : ∀ k, List (Γ k)) (hV : S .V = x) :
    ∃ v' S', Run prog (x.length + 2) ⟨some r0, v, S⟩ ⟨some .bad, v', S'⟩ ∧
      ∀ k, k ≠ .V → k ≠ b → S' k = S k := by
  have hx' := readUnaryLength_eq_none.1 hx
  obtain ⟨v₁, S₁, h₁, h1V, -, h1k⟩ := moveB_run h0 hb x x [] v S (by rw [hV]; simp)
    (by rw [hx']; simp [IsBitBlock, dU]) (by simp [EndsBitBlock])
  have h₂ := decr_run_zero h1 v₁ (S := S₁) h1V
  exact ⟨_, _, (h₁.trans h₂).of_eq rfl, h1k⟩

/-- **The checking loop.** From `lp` with the rest `x` of the input on `V` and the key bound
`(pq, pa)` on `PQ` and `PA`, the machine reaches `okO` if `chkFrom pq pa x` holds and `bad`
otherwise, within `(2 N + 27) (|x| + 1)` steps, leaving `Y` and `O` unchanged. -/
private theorem loop_run (N : ℕ) : ∀ (x : List Bool) (pq pa : ℕ) (v : Bool) (S : ∀ k, List (Γ k)),
    S .V = x → S .PQ = List.replicate pq true → S .PA = List.replicate pa true → S .Q = [] →
    S .A = [] → S .T1 = [] → S .T2 = [] → x.length ≤ N → pq ≤ N → pa ≤ N + 1 →
    ∃ v' S', RunLe prog ((2 * N + 27) * (x.length + 1)) ⟨some .lp, v, S⟩
      ⟨some (if chkFrom pq pa x then .okO else .bad), v', S'⟩ ∧ S' .Y = S .Y ∧
        S' .O = S .O := by
  intro x
  induction hlen : x.length using Nat.strong_induction_on generalizing x with
  | _ len ih =>
  intro pq pa v S hV hPQ hPA hQ hA hT1 hT2 hN hpq hpa
  subst hlen
  rcases x with _ | ⟨b, x'⟩
  · refine ⟨false, S, (Run.single ?_).le ?_, rfl, rfl⟩
    · simp [prog, TM2.stepAux, hV, chkFrom_nil]
    · simp
  · have hne : b :: x' ≠ [] := List.cons_ne_nil _ _
    have r0 : Run prog 1 ⟨some .lp, v, S⟩ ⟨some .rq0, true, S⟩ :=
      Run.single (by simp [prog, TM2.stepAux, hV])
    rcases h1 : readUnaryLength (b :: x') with _ | ⟨q, x1⟩
    · obtain ⟨v₁, S₁, r₁, h1k⟩ := read_run_none (r0 := .rq0) (r1 := .rq1) (next := .ra0)
        (b := .Q) (by decide) rfl rfl h1 true S hV
      rw [chkFrom_of_none₁ hne h1]
      refine ⟨_, _, (r0.trans r₁).le ?_, h1k _ (by decide) (by decide),
        h1k _ (by decide) (by decide)⟩
      nlinarith
    have l1 := length_of_readUnaryLength_eq_some h1
    obtain ⟨v₁, S₁, r₁, h1V, h1Q, h1k⟩ := read_run_some (r0 := .rq0) (r1 := .rq1) (next := .ra0)
      (b := .Q) (by decide) rfl rfl h1 true S hV
    rcases h2 : readUnaryLength x1 with _ | ⟨a, x2⟩
    · obtain ⟨v₂, S₂, r₂, h2k⟩ := read_run_none (r0 := .ra0) (r1 := .ra1) (next := .cq)
        (b := .A) (by decide) rfl rfl h2 v₁ S₁ h1V
      rw [chkFrom_of_none₂ h1 h2]
      refine ⟨_, _, ((r0.trans r₁).trans r₂).le ?_, ?_, ?_⟩
      · nlinarith
      · rw [h2k _ (by decide) (by decide), h1k _ (by decide) (by decide)]
      · rw [h2k _ (by decide) (by decide), h1k _ (by decide) (by decide)]
    have l2 := length_of_readUnaryLength_eq_some h2
    obtain ⟨v₂, S₂, r₂, h2V, h2A, h2k⟩ := read_run_some (r0 := .ra0) (r1 := .ra1) (next := .cq)
      (b := .A) (by decide) rfl rfl h2 v₁ S₁ h1V
    have f2 : ∀ k, k ≠ K.V → k ≠ K.Q → k ≠ K.A → S₂ k = S k := fun k h1' h2' h3' ↦ by
      rw [h2k k h1' h3', h1k k h1' h2']
    have s2PQ : S₂ .PQ = List.replicate pq true := by
      rw [f2 _ (by decide) (by decide) (by decide), hPQ]
    have s2PA : S₂ .PA = List.replicate pa true := by
      rw [f2 _ (by decide) (by decide) (by decide), hPA]
    have s2Q : S₂ .Q = List.replicate q true := by
      rw [h2k _ (by decide) (by decide), h1Q, hQ, List.append_nil]
    have s2A : S₂ .A = List.replicate a true := by
      rw [h2A, h1k _ (by decide) (by decide), hA, List.append_nil]
    have s2T1 : S₂ .T1 = [] := by rw [f2 _ (by decide) (by decide) (by decide), hT1]
    have s2T2 : S₂ .T2 = [] := by rw [f2 _ (by decide) (by decide) (by decide), hT2]
    -- from `sk0` on, once the key is checked
    have cont : (pq < q ∨ pq = q ∧ pa ≤ a) → ∀ (c : ℕ) (vv : Bool),
        Run prog c ⟨some .lp, v, S⟩ ⟨some .sk0, vv, S₂⟩ → c ≤ 4 * q + 4 * a + 13 →
        ∃ v' S', RunLe prog ((2 * N + 27) * ((b :: x').length + 1)) ⟨some .lp, v, S⟩
          ⟨some (if chkFrom pq pa (b :: x') then .okO else .bad), v', S'⟩ ∧ S' .Y = S .Y ∧
            S' .O = S .O := by
      intro hk c vv rpre hc
      rcases h3 : readUnaryLength x2 with _ | ⟨q', x3⟩
      · obtain ⟨v₃, S₃, r₃, h3k⟩ := read_run_none (r0 := .sk0) (r1 := .sk1) (next := .sk2)
          (b := .J) (by decide) rfl rfl h3 vv S₂ h2V
        rw [chkFrom_of_none₃ h1 h2 hk h3]
        refine ⟨_, _, (rpre.trans r₃).le ?_, ?_, ?_⟩
        · nlinarith
        · rw [h3k _ (by decide) (by decide), f2 _ (by decide) (by decide) (by decide)]
        · rw [h3k _ (by decide) (by decide), f2 _ (by decide) (by decide) (by decide)]
      have l3 := length_of_readUnaryLength_eq_some h3
      obtain ⟨v₃, S₃, r₃, h3V, -, h3k⟩ := read_run_some (r0 := .sk0) (r1 := .sk1) (next := .sk2)
        (b := .J) (by decide) rfl rfl h3 vv S₂ h2V
      rcases h4 : readUnaryLength x3 with _ | ⟨s, x4⟩
      · obtain ⟨v₄, S₄, r₄, h4k⟩ := read_run_none (r0 := .sk2) (r1 := .sk3) (next := .dr0)
          (b := .J) (by decide) rfl rfl h4 v₃ S₃ h3V
        rw [chkFrom_of_none₄ h1 h2 hk h3 h4]
        refine ⟨_, _, ((rpre.trans r₃).trans r₄).le ?_, ?_, ?_⟩
        · nlinarith
        · rw [h4k _ (by decide) (by decide), h3k _ (by decide) (by decide),
            f2 _ (by decide) (by decide) (by decide)]
        · rw [h4k _ (by decide) (by decide), h3k _ (by decide) (by decide),
            f2 _ (by decide) (by decide) (by decide)]
      have l4 := length_of_readUnaryLength_eq_some h4
      obtain ⟨v₄, S₄, r₄, h4V, -, h4k⟩ := read_run_some (r0 := .sk2) (r1 := .sk3) (next := .dr0)
        (b := .J) (by decide) rfl rfl h4 v₃ S₃ h3V
      have f4 : ∀ k, k ≠ K.V → k ≠ K.J → S₄ k = S₂ k := fun k h1' h2' ↦ by
        rw [h4k k h1' h2', h3k k h1' h2']
      have r5 := xfer_run (M := prog) (self := .dr0) (next := .dr1) (k := .PQ) (ps := []) rfl
        List.nodupKeys_nil (by simp) true pq v₄ S₄ (by rw [f4 _ (by decide) (by decide), s2PQ])
      have r6 := xfer_run (M := prog) (self := .dr1) (next := .mv0) (k := .PA) (ps := []) rfl
        List.nodupKeys_nil (by simp) true pa (Flag.tag false) (addU [] pq (update S₄ .PQ []))
        (by simp [addU, f4 .PA (by decide) (by decide), s2PA])
      have r7 := xfer_run (M := prog) (self := .mv0) (next := .mv1) (k := .Q)
        (ps := [⟨.PQ, true⟩]) rfl (single_nodupKeys _) (by simp) true q (Flag.tag false)
        (addU [] pa (update (addU [] pq (update S₄ .PQ [])) .PA []))
        (by simp [addU, f4 .Q (by decide) (by decide), s2Q])
      have r8 := xfer_run (M := prog) (self := .mv1) (next := .inc) (k := .A)
        (ps := [⟨.PA, true⟩]) rfl (single_nodupKeys _) (by simp) true a (Flag.tag false)
        (addU [⟨K.PQ, true⟩] q
          (update (addU [] pa (update (addU [] pq (update S₄ .PQ [])) .PA [])) .Q []))
        (by simp [addU, f4 .A (by decide) (by decide), s2A])
      set S₈ := addU [⟨K.PA, true⟩] a (update (addU [⟨K.PQ, true⟩] q
          (update (addU [] pa (update (addU [] pq (update S₄ .PQ [])) .PA [])) .Q [])) .A [])
        with hS₈
      have r9 := incr_run (M := prog) (self := .inc) (next := .lp) (k := .PA) (u := true) rfl
        (Flag.tag false) S₈
      set S₉ := update S₈ .PA (true :: S₈ .PA) with hS₉
      have hnil : ∀ n (T : ∀ k, List (Γ k)), addU ([] : List (Σ k, Γ k)) n T = T :=
        fun _ _ ↦ rfl
      have g : ∀ k, k ≠ K.PQ → k ≠ K.PA → k ≠ K.Q → k ≠ K.A → S₉ k = S₄ k := by
        intro k h1' h2' h3' h4'
        simp only [hS₉, hS₈, hnil, update_of_ne h1', update_of_ne h2', update_of_ne h3',
          update_of_ne h4', addU_single_ne _ _ _ h1', addU_single_ne _ _ _ h2']
      have hlt : x4.length < (b :: x').length := by omega
      obtain ⟨v', S', rL, hY, hO⟩ := ih x4.length hlt x4 rfl q (a + 1) (Flag.tag false) S₉
        (by rw [g _ (by decide) (by decide) (by decide) (by decide), h4V])
        (by simp [hS₉, hS₈, hnil, addU_single_self, addU_single_ne])
        (by simp [hS₉, hS₈, hnil, addU_single_self, addU_single_ne,
          List.replicate_succ])
        (by simp [hS₉, hS₈, hnil, addU_single_self, addU_single_ne])
        (by simp [hS₉, hS₈, hnil, addU_single_self, addU_single_ne])
        (by rw [g _ (by decide) (by decide) (by decide) (by decide),
          f4 _ (by decide) (by decide), s2T1])
        (by rw [g _ (by decide) (by decide) (by decide) (by decide),
          f4 _ (by decide) (by decide), s2T2])
        (by omega) (by omega) (by omega)
      rw [chkFrom_of_entry h1 h2 hk h3 h4]
      refine ⟨v', S', (((rpre.trans (r₃.trans (r₄.trans (r5.trans (r6.trans (r7.trans
        (r8.trans r9))))))).le le_rfl).trans rL).mono ?_, ?_, ?_⟩
      · have e : (b :: x').length = x4.length + (q + a + q' + s + 4) := by omega
        rw [e]
        nlinarith
      · rw [hY, g _ (by decide) (by decide) (by decide) (by decide),
          f4 _ (by decide) (by decide), f2 _ (by decide) (by decide) (by decide)]
      · rw [hO, g _ (by decide) (by decide) (by decide) (by decide),
          f4 _ (by decide) (by decide), f2 _ (by decide) (by decide) (by decide)]
    -- compare the states
    have rq := cmp_run (M := prog) (self := .cq) (r := .cqR) (rB := .cqRB) (out := outQ) rfl
      (fun _ ↦ rfl) (fun _ ↦ rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pq q v₂ S₂ s2PQ s2Q s2T1 s2T2
    have hcq : 3 * min pq q + 3 + (if pq = q then 0 else 1) ≤ 3 * q + 4 := by
      split <;> omega
    rcases lt_trichotomy pq q with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.2 hlt] at rq
      exact cont (Or.inl hlt) _ _ (((r0.trans r₁).trans r₂).trans rq) (by omega)
    · rw [Nat.compare_eq_eq.2 heq] at rq
      have ra := cmp_run (M := prog) (self := .ca) (r := .caR) (rB := .caRB) (out := outA) rfl
        (fun _ ↦ rfl) (fun _ ↦ rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) pa a (Flag.tag false) S₂ s2PA s2A s2T1 s2T2
      have hca : 3 * min pa a + 3 + (if pa = a then 0 else 1) ≤ 3 * a + 4 := by
        split <;> omega
      rcases le_or_gt pa a with hle | hgt'
      · have ho : outA (compare pa a) = .sk0 := by
          rcases hle.lt_or_eq with h | h
          · rw [Nat.compare_eq_lt.2 h]; rfl
          · rw [Nat.compare_eq_eq.2 h]; rfl
        rw [ho] at ra
        exact cont (Or.inr ⟨heq, hle⟩) _ _ ((((r0.trans r₁).trans r₂).trans rq).trans ra)
          (by omega)
      · rw [Nat.compare_eq_gt.2 hgt'] at ra
        rw [chkFrom_of_key h1 h2 (by omega)]
        refine ⟨_, _, ((((r0.trans r₁).trans r₂).trans rq).trans ra).le ?_, ?_, ?_⟩
        · nlinarith
        · rw [f2 _ (by decide) (by decide) (by decide)]
        · rw [f2 _ (by decide) (by decide) (by decide)]
    · rw [Nat.compare_eq_gt.2 hgt] at rq
      rw [chkFrom_of_key h1 h2 (by omega)]
      refine ⟨_, _, (((r0.trans r₁).trans r₂).trans rq).le ?_, ?_, ?_⟩
      · nlinarith
      · rw [f2 _ (by decide) (by decide) (by decide)]
      · rw [f2 _ (by decide) (by decide) (by decide)]

/-- Duplicating the input onto `Y` and `W`, reversed. -/
private theorem dup_run : ∀ (x : List Bool) (v : Bool) (S : ∀ k, List (Γ k)), S .X = x →
    ∃ v' S', Run prog (2 * x.length + 1) ⟨some .dupP, v, S⟩ ⟨some .cpy, v', S'⟩ ∧
      S' .Y = x.reverse ++ S .Y ∧ S' .W = x.reverse ++ S .W ∧
      ∀ k, k ≠ K.X → k ≠ K.Y → k ≠ K.W → S' k = S k
  | [], v, S, hX => ⟨false, S, Run.single (by simp [prog, TM2.stepAux, hX]), by simp, by simp,
      fun _ _ _ _ ↦ rfl⟩
  | b :: x, v, S, hX => by
    have r₁ : Run prog 1 ⟨some .dupP, v, S⟩ ⟨some .dupQ, true, S⟩ :=
      Run.single (by simp [prog, TM2.stepAux, hX])
    set S₁ := update (update (update S .X x) .Y (b :: S .Y)) .W (b :: S .W) with hS₁
    have r₂ : Run prog 1 ⟨some .dupQ, true, S⟩ ⟨some .dupP, b, S₁⟩ :=
      Run.single (by cases b <;> simp [prog, TM2.stepAux, hX, hS₁])
    obtain ⟨v', S', r₃, hY, hW, hk⟩ := dup_run x b S₁ (by simp [hS₁])
    refine ⟨v', S', ((r₁.trans r₂).trans r₃).of_eq (by simp; omega), ?_, ?_, fun k h1 h2 h3 ↦ ?_⟩
    · rw [hY]; simp [hS₁]
    · rw [hW]; simp [hS₁]
    · rw [hk k h1 h2 h3]; simp [hS₁, update_of_ne h1, update_of_ne h2, update_of_ne h3]

/-- **Answer of the checking machine.** For a bit list $x$, the answer is the list $x$ with
the bit $\mathrm{true}$ put in front if the cell-by-cell check of $x$ from the key $(0, 0)$
succeeds, and the one-bit list $[\mathrm{false}]$ otherwise. -/
def answer (x : List Bool) : List Bool := if chkFrom 0 0 x then true :: x else [false]

/-- **The checking run.** For every bit list $x$, the checking machine, started at the label
$\mathsf{dupP}$ with internal state false, with $x$ on its input stack $X$ and every other stack
empty, reaches the label $\mathsf{done}$ within $33(|x| + 1)^2$ steps, with some internal state
and stacks in which the output stack $O$ holds the answer of the checking machine on $x$. -/
theorem run (x : List Bool) :
    ∃ v S', RunLe prog (33 * (x.length + 1) ^ 2)
      ⟨some .dupP, false, update (fun _ ↦ []) .X x⟩ ⟨some .done, v, S'⟩ ∧ S' .O = answer x := by
  set S0 : ∀ k, List (Γ k) := update (fun _ ↦ []) .X x with hS0
  obtain ⟨v₁, S₁, r₁, h1Y, h1W, h1k⟩ := dup_run x false S0 (by simp [hS0])
  have h0 : ∀ k, k ≠ K.X → S0 k = [] := fun k hk ↦ by simp [hS0, update_of_ne hk]
  obtain ⟨v₂, S₂, r₂, -, h2V, h2k⟩ := moveB_run (M := prog) (self := .cpy) (next := .lp)
    (a := .W) (b := .V) (d := some) (g := id) rfl (by decide) x.reverse x.reverse [] v₁ S₁
    (by rw [h1W, h0 _ (by decide)]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have f2 : ∀ k, k ≠ K.X → k ≠ K.Y → k ≠ K.W → k ≠ K.V → S₂ k = [] := fun k a b c d ↦ by
    rw [h2k k c d, h1k k a b c, h0 k a]
  obtain ⟨v₃, S₃, r₃, hY3, hO3⟩ := loop_run x.length x 0 0 v₂ S₂
    (by rw [h2V, h1k _ (by decide) (by decide) (by decide), h0 _ (by decide)]; simp)
    (by rw [f2 _ (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [f2 _ (by decide) (by decide) (by decide) (by decide)]; rfl)
    (f2 _ (by decide) (by decide) (by decide) (by decide))
    (f2 _ (by decide) (by decide) (by decide) (by decide))
    (f2 _ (by decide) (by decide) (by decide) (by decide))
    (f2 _ (by decide) (by decide) (by decide) (by decide)) le_rfl (Nat.zero_le _) (by omega)
  have hY : S₃ .Y = x.reverse := by
    rw [hY3, h2k _ (by decide) (by decide), h1Y, h0 _ (by decide), List.append_nil]
  have hO : S₃ .O = [] := by rw [hO3, f2 _ (by decide) (by decide) (by decide) (by decide)]
  have hpre := ((r₁.trans r₂).le le_rfl).trans r₃
  by_cases hc : chkFrom 0 0 x = true
  · simp only [hc, ↓reduceIte] at hpre
    obtain ⟨v₄, S₄, r₄, -, h4O, -⟩ := moveB_run (M := prog) (self := .okO) (next := .okT)
      (a := .Y) (b := .O) (d := some) (g := id) rfl (by decide) x.reverse x.reverse [] v₃ S₃
      (by rw [hY]; simp) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
    have r₅ := incr_run (M := prog) (self := .okT) (next := .done) (k := .O) (u := true) rfl v₄ S₄
    refine ⟨_, _, (hpre.trans ((r₄.trans r₅).le le_rfl)).mono ?_, ?_⟩
    · simp only [List.length_reverse]
      nlinarith
    · simp [answer, hc, h4O, hO]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpre
    have r₄ := emit_run (M := prog) (self := .bad) (next := .done) (k := .O) (xs := [false]) rfl
      v₃ S₃
    refine ⟨_, _, (hpre.trans (r₄.le le_rfl)).mono ?_, ?_⟩
    · simp only [List.length_reverse]
      nlinarith
    · simp [answer, hc, hO]

/-- **The checking machine as a host component.** The component machine with the twelve stacks
$X, Y, W, V, Q, A, P_Q, P_A, T_1, T_2, J, O$ of the checking machine, each holding bits, with
the labels and the program of the checking machine, and with its stacks listed in the order
$X, Y, W, V, Q, A, P_Q, P_A, T_1, T_2, J, O$. -/
abbrev comp : Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ := fun _ ↦ inferInstanceAs (Fintype Bool)
  L := Lab
  prog := prog
  ks := [.X, .Y, .W, .V, .Q, .A, .PQ, .PA, .T1, .T2, .J, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The checking machine in polynomial time.** A finite multi-stack Turing machine with a
polynomial time bound that computes the checking answer: given a bit list $x$ as its input, it
halts within the bound, evaluated at $|x|$, with the checking answer on $x$ as its output. -/
noncomputable def polyTime :
    TM2ComputableInPolyTime (fun l : List Bool ↦ l) (fun l : List Bool ↦ l) answer :=
  Complexity.Host.reduction (c := comp) (cX := .X) (cO := .O) (gX := id) (start := .dupP)
    (done := .done) (Equiv.refl Bool) _ (Polynomial.C 33 * (Polynomial.X + 1) ^ 2) rfl
    fun x ↦ by
      obtain ⟨v, S', hr, hO⟩ := run x
      exact ⟨v, S', by simpa [Polynomial.eval_mul, Polynomial.eval_pow] using hr,
        by simpa using hO⟩

end Check

/-! ### The layout machine -/

namespace Layout

open Function MetaMathlibExt.TM2Program

/-- **Stacks of the layout machine.** The layout machine has twelve stacks, named
$X, Z, P, P_2, U, N, A_2, B_2, D, C, T, O$. -/
inductive K | X | Z | P | P2 | U | N | A2 | B2 | D | C | T | O
  deriving DecidableEq

/-- Finitely many stacks. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .Z, .P, .P2, .U, .N, .A2, .B2, .D, .C, .T, .O], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the layout machine.** The layout machine has 17 labels, named $\mathsf{s0}$,
$\mathsf{mvZ}$, $\mathsf{cp0}$, $\mathsf{cp1}$, $\mathsf{lo0}$, $\mathsf{lo1}$, $\mathsf{lo2}$,
$\mathsf{lo3}$, $\mathsf{lo4}$, $\mathsf{mh}$, $\mathsf{mb}$, $\mathsf{mk}$, $\mathsf{mr}$,
$\mathsf{lo5}$, $\mathsf{lo6}$, $\mathsf{bad}$ and $\mathsf{done}$. -/
inductive Lab
  | s0 | mvZ | cp0 | cp1 | lo0 | lo1 | lo2 | lo3 | lo4 | mh | mb | mk | mr | lo5 | lo6 | bad | done
  deriving DecidableEq

/-- Finitely many labels. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.s0, .mvZ, .cp0, .cp1, .lo0, .lo1, .lo2, .lo3, .lo4, .mh, .mb, .mk, .mr, .lo5,
    .lo6, .bad, .done], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack symbols of the layout machine.** Every stack of the layout machine holds bits: the
alphabet of each of its stacks is the type of Booleans. -/
abbrev Γ : K → Type := fun _ => Bool

/-- **Program of the layout machine.** Writing $1$ for true and $0$ for false, this is the
program of a multi-stack machine whose stacks $X, Z, P, P_2, U, N, A_2, B_2, D, C, T, O$ all hold
bits. To move a stack $S$ onto a stack $S'$ means to pop the bits of $S$ one at a time, pushing
each onto $S'$, until $S$ is empty; to transfer $S$ to some stacks means to pop $S$ until it is
empty, pushing a $1$ on each of these stacks for every bit popped. From the label $\mathsf{s0}$
the program pops $X$. If $X$ was empty or the popped bit is $0$, it pushes $0, 0, 1, 1, 0$ on $O$
in this order and halts. Otherwise it moves $X$ onto $Z$, and then, as long as $Z$ is nonempty,
it pops a bit $b$ from $Z$, pushes $b$ on $U$ and a $1$ on $N$, and pushes $0, 1, 1$ on $P$ in
this order if $b = 1$ and $0, 1$ if $b = 0$. Then it moves $U$ onto $O$, pushes a $0$ on $O$,
moves $P$ onto $P_2$ and then $P_2$ onto $O$, and transfers $N$ to $A_2$ and $B_2$. Then it
loops: it pops $A_2$; if a bit was popped, it pushes a $1$ on $D$, transfers $B_2$ to $C$ and
$T$, transfers $T$ to $B_2$ and loops again; if $A_2$ was empty, it transfers $D$ to $A_2$.
Finally it pushes $0, 1$ on $O$ in this order, transfers $C$ to $O$ and halts. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .s0 => .pop .X (fun _ o ↦ o == some true)
      (.branch id (.goto fun _ ↦ .mvZ) (.goto fun _ ↦ .bad))
  | .mvZ => moveB .X .Z some id .mvZ .cp0
  | .cp0 => .peek .Z (fun _ o ↦ o.isSome) (.branch id (.goto fun _ ↦ .cp1) (.goto fun _ ↦ .lo0))
  | .cp1 => .pop .Z (fun _ o ↦ o.getD false) (.branch id
      (.push .U (fun _ ↦ true) (.push .N (fun _ ↦ true) (.push .P (fun _ ↦ false)
        (.push .P (fun _ ↦ true) (.push .P (fun _ ↦ true) (.goto fun _ ↦ .cp0))))))
      (.push .U (fun _ ↦ false) (.push .N (fun _ ↦ true) (.push .P (fun _ ↦ false)
        (.push .P (fun _ ↦ true) (.goto fun _ ↦ .cp0))))))
  | .lo0 => moveB .U .O some id .lo0 .lo1
  | .lo1 => incr .O false .lo2
  | .lo2 => moveB .P .P2 some id .lo2 .lo3
  | .lo3 => moveB .P2 .O some id .lo3 .lo4
  | .lo4 => xfer .N [⟨.A2, true⟩, ⟨.B2, true⟩] .lo4 .mh
  | .mh => forHead .A2 .D true .mb .mr
  | .mb => xfer .B2 [⟨.C, true⟩, ⟨.T, true⟩] .mb .mk
  | .mk => xfer .T [⟨.B2, true⟩] .mk .mh
  | .mr => xfer .D [⟨.A2, true⟩] .mr .lo5
  | .lo5 => emitR .O [true, false] .lo6
  | .lo6 => xfer .C [⟨.O, true⟩] .lo6 .done
  | .bad => emitR .O [false, true, true, false, false] .done
  | .done => .halt

/-- The cells pass: popping `z` from `Z` pushes `z.reverse` on `U`, `|z|` units on `N` and the
cells of the input symbols of `z.reverse` on `P`. -/
private theorem cp_run : ∀ (z : List Bool) (v : Bool) (S : ∀ k, List (Γ k)), S .Z = z →
    ∃ v' S', Run prog (2 * z.length + 1) ⟨some .cp0, v, S⟩ ⟨some .lo0, v', S'⟩ ∧
      S' .U = z.reverse ++ S .U ∧ S' .N = List.replicate z.length true ++ S .N ∧
      S' .P = cells (input z.reverse) ++ S .P ∧
      ∀ k, k ≠ K.Z → k ≠ K.U → k ≠ K.N → k ≠ K.P → S' k = S k
  | [], v, S, hZ => ⟨false, S, Run.single (by simp [prog, TM2.stepAux, hZ]), by simp, by simp,
      by simp [input, cells], fun _ _ _ _ _ ↦ rfl⟩
  | b :: z, v, S, hZ => by
    have r₁ : Run prog 1 ⟨some .cp0, v, S⟩ ⟨some .cp1, true, S⟩ :=
      Run.single (by simp [prog, TM2.stepAux, hZ])
    set S₁ := update (update (update (update S .Z z) .U (b :: S .U)) .N (true :: S .N)) .P
      (cell (bitSym b) ++ S .P) with hS₁
    have r₂ : Run prog 1 ⟨some .cp1, true, S⟩ ⟨some .cp0, b, S₁⟩ := by
      refine Run.single ?_
      cases b <;>
      · simp only [prog, TM2.stepAux, hZ, List.head?_cons, List.tail_cons,
          Option.getD_some, id, Bool.cond_true, Bool.cond_false, TM2.Cfg.mk.injEq, true_and]
        funext k
        cases k <;> simp [hS₁, update_self, update_of_ne, cell, bitSym, List.replicate_succ]
    obtain ⟨v', S', r₃, hU, hN, hP, hk⟩ := cp_run z b S₁ (by simp [hS₁])
    refine ⟨v', S', ((r₁.trans r₂).trans r₃).of_eq (by simp; omega), ?_, ?_, ?_,
      fun k h1 h2 h3 h4 ↦ ?_⟩
    · rw [hU]; simp [hS₁]
    · rw [hN]; simp [hS₁, List.replicate_succ']
    · rw [hP]; simp [hS₁, input, cells]
    · rw [hk k h1 h2 h3 h4]
      simp [hS₁, update_of_ne h1, update_of_ne h2, update_of_ne h3, update_of_ne h4]

/-- The cells of the input symbols take at most three bits per input bit. -/
private theorem length_cells_input_le (x : List Bool) :
    (cells (input x)).length ≤ 3 * x.length := by
  induction x with
  | nil => simp [cells, input]
  | cons b x ih =>
    have : (cell (bitSym b)).length ≤ 3 := by cases b <;> simp [cell, bitSym]
    simp only [input, List.map_cons, cells, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    omega

/-- **The layout function.** Write $\mathrm{cell}(n)$ for the bit list of $n$ bits
$\mathrm{true}$ followed by one bit $\mathrm{false}$. On a bit list $\mathrm{true} :: x$, the
layout function returns $\mathrm{cell}(|x|^2 + 1)$, then the cells $\mathrm{cell}(s)$ of the
symbols $s$ of the input word of $x$ (the symbol $2$ for each bit $\mathrm{true}$ and $1$ for
each bit $\mathrm{false}$), then the bit $\mathrm{false}$, then the reverse of $x$. On every other
bit list, that is, the empty list or a list starting with $\mathrm{false}$, it returns the list
$[\mathrm{false}, \mathrm{true}, \mathrm{true}, \mathrm{false}, \mathrm{false}]$. -/
def layout : List Bool → List Bool
  | true :: x => cell (x.length ^ 2 + 1) ++ (cells (input x) ++ (false :: x.reverse))
  | _ => [false, true, true, false, false]

/-- **The layout run.** For every bit list $y$, the layout machine, started at the label
$\mathsf{s0}$ with internal state false, with $y$ on its input stack $X$ and every other stack
empty, reaches the label $\mathsf{done}$ within $18(|y| + 1)^2$ steps, with some internal state
and stacks in which the output stack $O$ holds the layout of $y$. -/
theorem run (y : List Bool) :
    ∃ v S', RunLe prog (18 * (y.length + 1) ^ 2)
      ⟨some .s0, false, update (fun _ ↦ []) .X y⟩ ⟨some .done, v, S'⟩ ∧ S' .O = layout y := by
  rcases y with _ | ⟨_ | _, x⟩
  · have r₁ : Run prog 1 ⟨some .s0, false, update (fun _ ↦ []) .X []⟩
        ⟨some .bad, false, update (update (fun _ ↦ []) .X []) .X ([] : List Bool).tail⟩ :=
      Run.single rfl
    have r₂ := emitR_run (M := prog) (self := .bad) (next := .done) (k := .O)
      (ys := [false, true, true, false, false]) rfl false
      (update (update (fun _ ↦ []) .X []) .X ([] : List Bool).tail)
    exact ⟨_, _, (r₁.trans r₂).le (by norm_num), by simp [layout]⟩
  · have r₁ : Run prog 1 ⟨some .s0, false, update (fun _ ↦ []) .X (false :: x)⟩
        ⟨some .bad, false, update (update (fun _ ↦ []) .X (false :: x)) .X x⟩ :=
      Run.single rfl
    have r₂ := emitR_run (M := prog) (self := .bad) (next := .done) (k := .O)
      (ys := [false, true, true, false, false]) rfl false
      (update (update (fun _ ↦ []) .X (false :: x)) .X x)
    refine ⟨_, _, (r₁.trans r₂).le ?_, by simp [layout]⟩
    have h := Nat.one_le_pow 2 ((false :: x).length + 1) (by omega)
    nlinarith [h]
  · set n := x.length with hn
    set S1 : ∀ k, List (Γ k) := update (update (fun _ ↦ []) .X (true :: x)) .X x with hS1
    have h1 : ∀ k, k ≠ K.X → S1 k = [] := fun k hk ↦ by simp [hS1, update_of_ne hk]
    have r₁ : Run prog 1 ⟨some .s0, false, update (fun _ ↦ []) .X (true :: x)⟩
        ⟨some .mvZ, true, S1⟩ := Run.single rfl
    obtain ⟨v₂, S2, r₂, -, h2Z, h2k⟩ := moveB_run (M := prog) (self := .mvZ) (next := .cp0)
      (a := .X) (b := .Z) (d := some) (g := id) rfl (by decide) x x [] true S1
      (by simp [hS1]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
    obtain ⟨v₃, S3, r₃, h3U, h3N, h3P, h3k⟩ := cp_run x.reverse v₂ S2
      (by rw [h2Z, h1 _ (by decide)]; simp)
    have f3 : ∀ k, k ≠ K.X → k ≠ K.Z → k ≠ K.U → k ≠ K.N → k ≠ K.P → S3 k = [] :=
      fun k a b c d e ↦ by rw [h3k k b c d e, h2k k a b, h1 k a]
    obtain ⟨v₄, S4, r₄, -, h4O, h4k⟩ := moveB_run (M := prog) (self := .lo0) (next := .lo1)
      (a := .U) (b := .O) (d := some) (g := id) rfl (by decide) x x [] v₃ S3
      (by rw [h3U, h2k _ (by decide) (by decide), h1 _ (by decide)]; simp)
      (by simp [IsBitBlock]) (by simp [EndsBitBlock])
    have r₅ := incr_run (M := prog) (self := .lo1) (next := .lo2) (k := .O) (u := false) rfl v₄ S4
    set S5 := update S4 .O (false :: S4 .O) with hS5
    set c := cells (input x) with hc
    obtain ⟨v₆, S6, r₆, -, h6P2, h6k⟩ := moveB_run (M := prog) (self := .lo2) (next := .lo3)
      (a := .P) (b := .P2) (d := some) (g := id) rfl (by decide) c c [] v₄ S5
      (by
        rw [hS5, update_of_ne (by decide), h4k _ (by decide) (by decide), h3P,
          h2k _ (by decide) (by decide), h1 _ (by decide)]
        simp [hc])
      (by simp [IsBitBlock]) (by simp [EndsBitBlock])
    obtain ⟨v₇, S7, r₇, -, h7O, h7k⟩ := moveB_run (M := prog) (self := .lo3) (next := .lo4)
      (a := .P2) (b := .O) (d := some) (g := id) rfl (by decide) c.reverse c.reverse [] v₆ S6
      (by
        rw [h6P2, hS5, update_of_ne (by decide),
          h4k _ (by decide) (by decide), f3 _ (by decide) (by decide) (by decide) (by decide)
            (by decide)]
        simp)
      (by simp [IsBitBlock]) (by simp [EndsBitBlock])
    have hO7 : S7 .O = c ++ false :: x.reverse := by
      rw [h7O, h6k _ (by decide) (by decide), hS5, update_self, h4O,
        f3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp
    have g7 : ∀ k, k ≠ K.X → k ≠ K.Z → k ≠ K.U → k ≠ K.N → k ≠ K.P → k ≠ K.P2 → k ≠ K.O →
        S7 k = [] := fun k a b c' d e f g' ↦ by
      rw [h7k k f g', h6k k e f, hS5, update_of_ne g', h4k k c' g', f3 k a b c' d e]
    have hN7 : S7 .N = List.replicate n true := by
      rw [h7k _ (by decide) (by decide), h6k _ (by decide) (by decide), hS5,
        update_of_ne (by decide), h4k _ (by decide) (by decide), h3N,
        h2k _ (by decide) (by decide), h1 _ (by decide)]
      simp [hn]
    have r₈ := xfer_run (M := prog) (self := .lo4) (next := .mh) (k := .N)
      (ps := [⟨.A2, true⟩, ⟨.B2, true⟩]) rfl (pair_nodupKeys _ _ (by decide)) (by simp) true n
      v₇ S7 hN7
    set S8 := addU [⟨K.A2, true⟩, ⟨K.B2, true⟩] n (update S7 .N []) with hS8
    have r₉ := mul_run (M := prog) (a := .A2) (ad := .D) (b := .B2) (c := .C) (t := .T)
      (ua := true) (uad := true) (ub := true) (uc := true) (ut := true) (head := .mh) (body := .mb)
      (l₂ := .mk) (rest := .mr) (next := .lo5) rfl rfl rfl rfl (by decide) n n 0
      (Flag.tag false) S8
      (by simp [hS8, addU_pair_fst, g7 .A2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)])
      (by simp [hS8, addU_pair_ne, g7 .D (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)])
      (by simp [hS8, addU_pair_snd, g7 .B2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)])
      (by simp [hS8, addU_pair_ne, g7 .C (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)])
      (by simp [hS8, addU_pair_ne, g7 .T (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)])
    set S9 := update S8 .C (cnt true (n * n + 0)) with hS9
    have r₁₀ := emitR_run (M := prog) (self := .lo5) (next := .lo6) (k := .O) (ys := [true, false])
      rfl (Flag.tag false) S9
    set S10 := update S9 .O ([true, false] ++ S9 .O) with hS10
    have r₁₁ := xfer_run (M := prog) (self := .lo6) (next := .done) (k := .C) (ps := [⟨.O, true⟩])
      rfl (single_nodupKeys _) (by simp) true (n * n + 0) (Flag.tag false) S10
      (by simp [hS10, hS9])
    refine ⟨_, _, (((((((((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).trans
      r₇).trans r₈).trans r₉).trans r₁₀).trans r₁₁).le ?_), ?_⟩
    · have hcl := length_cells_input_le x
      simp only [List.length_reverse, List.length_cons, ← hn, ← hc] at hcl ⊢
      nlinarith
    · simp only [addU_single_self, update_self, hS10, hS9, update_of_ne (show K.O ≠ K.C by decide),
        hS8, addU_pair_ne _ _ _ _ (show K.O ≠ K.A2 by decide) (show K.O ≠ K.B2 by decide),
        update_of_ne (show K.O ≠ K.N by decide), hO7, layout, cell, ← hn, ← hc]
      simp [sq, List.replicate_succ']

end Layout

/-! ### The upper bound for `n ↦ n ^ 2 + 1` -/

/-- **The cell-by-cell check agrees with code-stack decoding.** For every bit list $x$, the
cell-by-cell check of $x$ from the key $(0, 0)$ succeeds if and only if the decoding of $x$ as a
code stack returns a code. -/
theorem chkFrom_zero (x : List Bool) : chkFrom 0 0 x = (decodeCodeCells x).isSome := by
  rw [Bool.eq_iff_iff, chkFrom_iff, isSome_decodeCodeCells_iff_entries]

namespace Layout

/-- **The layout machine as a host component.** The component machine with the twelve stacks
$X, Z, P, P_2, U, N, A_2, B_2, D, C, T, O$ of the layout machine, each holding bits, with the
labels and the program of the layout machine, and with its stacks listed in the order
$X, Z, P, P_2, U, N, A_2, B_2, D, C, T, O$. -/
abbrev comp : Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ := fun _ ↦ inferInstanceAs (Fintype Bool)
  L := Lab
  prog := prog
  ks := [.X, .Z, .P, .P2, .U, .N, .A2, .B2, .D, .C, .T, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The layout in polynomial time.** A finite multi-stack Turing machine, whose input and
output alphabets are identified with the bits, together with a polynomial time bound, that
computes the layout function: given a bit list $y$ as its input, it halts within the bound,
evaluated at $|y|$, with the layout of $y$ as its output. -/
noncomputable def polyTime :
    TM2ComputableInPolyTime (fun l : List Bool ↦ l) (fun l : List Bool ↦ l) layout :=
  Complexity.Host.reduction (c := comp) (cX := .X) (cO := .O) (gX := id) (start := .s0)
    (done := .done) (Equiv.refl Bool) _ (Polynomial.C 18 * (Polynomial.X + 1) ^ 2) rfl
    fun y ↦ by
      obtain ⟨v, S', hr, hO⟩ := run y
      exact ⟨v, S', by simpa [Polynomial.eval_mul, Polynomial.eval_pow] using hr,
        by simpa using hO⟩

end Layout

/-- **Layout after checking gives the universal machine's input.** For every bit list $x$, let
$(c, y, T)$ be the universal machine's argument for the diagonal language of $f(n) = n^2 + 1$ on
$x$. Then the layout function applied to the checking machine's answer on $x$ equals the input
bit list of the clocked universal machine for the code $c$, the input $y$ and the clock $T$. -/
theorem layout_answer (x : List Bool) :
    Layout.layout (Check.answer x) =
      encIn (diagArg (fun n ↦ n ^ 2 + 1) x).1 (diagArg (fun n ↦ n ^ 2 + 1) x).2.1
        (diagArg (fun n ↦ n ^ 2 + 1) x).2.2 := by
  rw [encIn_diagArg, ← chkFrom_zero]
  by_cases h : chkFrom 0 0 x = true <;> simp [Check.answer, Layout.layout, h]

/-- **The reformatting machine for $n \mapsto n^2 + 1$.** Let $f(n) = n^2 + 1$. This is a
finite multi-stack Turing machine whose input and output alphabets are identified with the bits,
together with a polynomial $p$, such that for every bit list $x$, started with $x$ on its input
stack it halts within $p(|x|)$ steps with output the clocked universal machine's input bits for
the universal machine's argument $(c, w, T)$ for the diagonal language of $f$ at $x$: the clock
$T$ as a cell, the cells of the input symbols of $w$, a blank cell and the code stack of $c$
reversed. It runs the checking machine and then the layout machine. -/
noncomputable def reformat :
    TM2ComputableInPolyTime (fun x : List Bool ↦ x)
      (fun a : Code × List Bool × ℕ ↦ encIn a.1 a.2.1 a.2.2) (diagArg (fun n ↦ n ^ 2 + 1)) :=
  let H := MetaMathlibExt.TM2Composition.compComputable Check.polyTime Layout.polyTime
  { toTM2ComputableAux := H.toTM2ComputableAux
    time := H.time
    outputsFun := fun x ↦ by
      have h := H.outputsFun x
      simp only [Function.comp_apply, layout_answer] at h
      exact h }

end Diag

/-- **Deciding the diagonal language on raw bits in polynomial time.** Let $D$ be the diagonal
language for the time bound $f(n) = n^2 + 1$. There is a finite multi-stack Turing machine that,
given a bit list $x$ as its input, halts within a number of steps polynomial in $|x|$ with the
single bit $D(x)$ as its output. -/
theorem nonempty_diag_sq_add_one_polyTime :
    Nonempty (TM2ComputableInPolyTime (fun x : List Bool ↦ x) (fun b : Bool ↦ [b])
      (diag (fun n ↦ n ^ 2 + 1))) :=
  nonempty_diag_polyTime Diag.reformat

/-- **The quadratic diagonal language is in P.** The diagonal language for the time bound
$f(n) = n^2 + 1$, the set of bit lists $x$ that encode a code which does not halt on $x$ within
$|x|^2 + 1$ steps with the answer $\mathrm{true}$, is in the class P of decision problems
decidable in polynomial time.

The decider decodes the canonical encoding of bit lists and then runs a polynomial-time decider
on the raw bits. -/
theorem diag_sq_add_one_mem_P : diag (fun n ↦ n ^ 2 + 1) ∈ P := by
  obtain ⟨D⟩ := nonempty_diag_sq_add_one_polyTime
  obtain ⟨h⟩ := MetaMathlibExt.tm2ComputableInPolyTime_comp
    Cslib.Complexity.DenseSAT.DecodeBits.computable D
  exact ⟨⟨h.toTM2ComputableAux, h.time, h.outputsFun⟩⟩

/-- **Diagonalization across models.** There is a decision problem in the class P that no code
decides within $n^2 + 1$ steps: no code halts on every input $x$ within $|x|^2 + 1$ steps with
the answer for $x$ as its output.

The diagonal language for the time bound $n \mapsto n^2 + 1$ is such a problem. The class of
problems that codes decide within $n^2 + 1$ steps is not empty: it contains the problem whose
answer is always $\mathrm{false}$. -/
theorem exists_mem_P_not_mem_codeTime_sq_add_one :
    ∃ L ∈ P, L ∉ CodeTime (fun n ↦ n ^ 2 + 1) :=
  ⟨diag (fun n ↦ n ^ 2 + 1), diag_sq_add_one_mem_P, diag_not_mem_codeTime _⟩

/-- **Polynomial time is not contained in code time $n^2 + 1$.** Some decision problem in
$\mathsf{P}$ is decided by no code within $n^2 + 1$ steps on every input of length $n$; that is,
$\mathsf{P}$ is not a subset of the class $\mathrm{CodeTime}(n \mapsto n^2 + 1)$. -/
theorem not_P_subset_codeTime_sq_add_one : ¬ P ⊆ CodeTime (fun n ↦ n ^ 2 + 1) := fun h ↦
  diag_not_mem_codeTime _ (h diag_sq_add_one_mem_P)

end Cslib.Turing.Universal
