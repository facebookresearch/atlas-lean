/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic


/-!
# The π-calculus: syntax, substitution, structural congruence, reduction

The π-calculus (Milner, Parrow, and Walker, *A calculus of mobile
processes*, Information and Computation 1992) extends CCS with name
passing: the input prefix `a(x).P` binds `x`, and the output prefix
`ā⟨b⟩.P` sends the channel name `b` along `a`, so channels themselves
travel as values and the communication topology changes at run time.

Names are de Bruijn indexed: `Name.var i` is the `i`-th enclosing
binder (an input binder or a `ν`-binder), and `Name.const n` is a free
channel. `liftProc` shifts free variables under a binder;
`subst p n` substitutes the name `n` for the innermost bound
variable of `p`, lifting `n` as it passes under binders, so a bound
(`var`) name can be transmitted exactly like a free one. `Cong` is
structural congruence (commutativity and associativity of `|`,
`ν`-scope extrusion, replication unfolding), and `Step` is reduction:
communication (with substitution), reduction under `|` and `ν`, and
reduction up to structural congruence.

Main results, all concrete calculations:

* `subst_out_var`: substitution delivers a sent channel to the input
  variable.
* `comm_example`: `ā⟨b⟩.0 | a(x).x̄.0 → 0 | b̄.0`.
* `bound_name_transmission`: a restricted name is transmitted,
  `νa.(b̄⟨a⟩.0 | b(x).x̄.0) → νa.(0 | ā.0)`, so the receiver gains the
  restricted channel.
* `scope_comm_example`: communication on a restricted channel,
  `νa.(ā⟨b⟩.0 | a(x).0) → νa.(0 | 0)`.
* `comm_after_swap`: communication after swapping the parallel
  components by structural congruence.
* `extrusion_example`: scope extrusion,
  `(νa.P) | 0 ≡ νa.(P | 0)`.
* `out_cong_example`: congruence transports under an output prefix,
  `ā⟨b⟩.(P | 0) ≡ ā⟨b⟩.P`.
* `sum_choice_example`, `input_choice_example`, `sum_sum_example`,
  `nested_sum_example`: guarded choice selects on the output side, on
  the input side, on both sides, and transitively through nested
  sums.
-/

@[expose] public section

namespace Cslib
namespace PiCalculus

/-- A channel name: a free channel `const n`, or the `i`-th enclosing
binder `var i`. -/
inductive Name where
  | const (n : ℕ) : Name
  | var (i : ℕ) : Name
  deriving DecidableEq, Repr

/-- Processes of the π-calculus. `inp a p` binds variable `0` in `p`;
`nu p` binds variable `0` in `p` as a fresh channel. -/
inductive Proc where
  | nil : Proc
  | out (a b : Name) (p : Proc) : Proc
  | inp (a : Name) (p : Proc) : Proc
  | par (p q : Proc) : Proc
  | nu (p : Proc) : Proc
  | repl (p : Proc) : Proc
  | sum (p q : Proc) : Proc
  deriving DecidableEq, Repr

/-- Shift free variables at or above `cutoff` up by one, e.g. when
pushing a process under a binder. -/
def liftName (cutoff : ℕ) : Name → Name
  | .const n => .const n
  | .var i => if cutoff ≤ i then .var (i + 1) else .var i

/-- Shift free variables of a process, entering binders with an
increased cutoff. -/
def liftProc (cutoff : ℕ) : Proc → Proc
  | .nil => .nil
  | .out a b p => .out (liftName cutoff a) (liftName cutoff b) (liftProc cutoff p)
  | .inp a p => .inp (liftName cutoff a) (liftProc (cutoff + 1) p)
  | .par p q => .par (liftProc cutoff p) (liftProc cutoff q)
  | .nu p => .nu (liftProc (cutoff + 1) p)
  | .repl p => .repl (liftProc cutoff p)
  | .sum p q => .sum (liftProc cutoff p) (liftProc cutoff q)

/-- Substitute the name `n` for the variable at `cutoff`: variables
below the cutoff are bound by inner binders and untouched, the variable
at the cutoff is replaced by `n`, and variables above shift down by
one. -/
def substName (n : Name) : ℕ → Name → Name
  | _, .const m => .const m
  | cutoff, .var i =>
      if i < cutoff then .var i
      else if i = cutoff then n
      else .var (i - 1)

/-- Substitute the name `n` for the variable at `cutoff` in a
process. Under a binder, `n` is lifted by one at cutoff `0` so it
keeps referring to the same outer names: every free index of `n`
refers to a binder above the substitution point, so all of them shift.
Lifting at the current cutoff would leave indices below the cutoff
captured by the new binder. -/
def substProc (n : Name) : ℕ → Proc → Proc
  | _, .nil => .nil
  | cutoff, .out a b p =>
      .out (substName n cutoff a) (substName n cutoff b) (substProc n cutoff p)
  | cutoff, .inp a p =>
      .inp (substName n cutoff a) (substProc (liftName 0 n) (cutoff + 1) p)
  | cutoff, .par p q => .par (substProc n cutoff p) (substProc n cutoff q)
  | cutoff, .nu p => .nu (substProc (liftName 0 n) (cutoff + 1) p)
  | cutoff, .repl p => .repl (substProc n cutoff p)
  | cutoff, .sum p q => .sum (substProc n cutoff p) (substProc n cutoff q)

/-- Substitute the name `n` for the innermost bound variable of `p`. -/
def subst (p : Proc) (n : Name) : Proc := substProc n 0 p

/-- Swap the two de Bruijn indices `cutoff` and `cutoff + 1` in a name:
the two binders at that depth exchange places. -/
def swapNameAt (cutoff : ℕ) : Name → Name
  | .var i => if i = cutoff then .var (cutoff + 1)
      else if i = cutoff + 1 then .var cutoff else .var i
  | .const n => .const n

/-- Swap the two binders at depth `cutoff` throughout a process,
incrementing the cutoff under binders. -/
def swapProc (cutoff : ℕ) : Proc → Proc
  | .nil => .nil
  | .out a b p => .out (swapNameAt cutoff a) (swapNameAt cutoff b) (swapProc cutoff p)
  | .inp a p => .inp (swapNameAt cutoff a) (swapProc (cutoff + 1) p)
  | .par p q => .par (swapProc cutoff p) (swapProc cutoff q)
  | .nu p => .nu (swapProc (cutoff + 1) p)
  | .repl p => .repl (swapProc cutoff p)
  | .sum p q => .sum (swapProc cutoff p) (swapProc cutoff q)

/-- Substitution delivers a sent channel to the input variable:
`(x̄⟨0⟩.0)[c / x] = c̄⟨0⟩.0`. -/
theorem subst_out_var (c : ℕ) :
    subst (.out (.var 0) (.const 0) .nil) (.const c) =
      .out (.const c) (.const 0) .nil := rfl

/-- Substitution leaves a process with no `var 0` untouched: a
constant channel stays constant, and the empty process stays empty. -/
theorem subst_nil (n : Name) : subst .nil n = .nil := rfl

/-- Nested-binder regression: substituting for variable `1` under a
`ν` lifts the replacement `var 0` to `var 1`, so it is not captured by
the `ν`. -/
theorem substProc_nested :
    substProc (.var 0) 1 (.nu (.out (.var 2) (.const 0) .nil)) =
      .nu (.out (.var 1) (.const 0) .nil) := rfl

/-- Structural congruence: `|` is commutative and associative with
unit `nil`, `ν` extrudes over `|` (lifting the other side, which cannot
mention the fresh name), restriction of `nil` is `nil`, nested
restrictions commute (swapping the two bound indices), and replication
unfolds. -/
inductive Cong : Proc → Proc → Prop
  | refl (p : Proc) : Cong p p
  | symm {p q : Proc} : Cong p q → Cong q p
  | trans {p q r : Proc} : Cong p q → Cong q r → Cong p r
  | par_comm (p q : Proc) : Cong (.par p q) (.par q p)
  | par_assoc (p q r : Proc) : Cong (.par (.par p q) r) (.par p (.par q r))
  | par_nil (p : Proc) : Cong (.par p .nil) p
  | par_cong {p p' q q' : Proc} : Cong p p' → Cong q q' →
      Cong (.par p q) (.par p' q')
  | nu_cong {p p' : Proc} : Cong p p' → Cong (.nu p) (.nu p')
  | scope (p q : Proc) :
      Cong (.par (.nu p) q) (.nu (.par p (liftProc 0 q)))
  | sum_cong {p p' q q' : Proc} : Cong p p' → Cong q q' →
      Cong (.sum p q) (.sum p' q')
  | out_cong {p p' : Proc} (a b : Name) : Cong p p' →
      Cong (.out a b p) (.out a b p')
  | inp_cong {q q' : Proc} (a : Name) : Cong q q' →
      Cong (.inp a q) (.inp a q')
  | repl_cong {p p' : Proc} : Cong p p' → Cong (.repl p) (.repl p')
  | nu_nil : Cong (.nu .nil) .nil
  | nu_swap (p : Proc) : Cong (.nu (.nu p)) (.nu (.nu (swapProc 0 p)))
  | repl_unfold (p : Proc) : Cong (.repl p) (.par p (.repl p))

/-- Guarded-choice resolution: discard sum branches to reach a
guarded process. Transitivity handles nested sums. -/
inductive Select : Proc → Proc → Prop
  | refl (p : Proc) : Select p p
  | left (p q : Proc) : Select (.sum p q) p
  | right (p q : Proc) : Select (.sum p q) q
  | trans {p q r : Proc} : Select p q → Select q r → Select p r

/-- Reduction: communication (substituting the sent channel for the
input variable) between any selected output and input guards,
reduction under `|` and `ν`, and reduction up to structural
congruence. -/
inductive Step : Proc → Proc → Prop
  | commSelect {a : Name} {b : Name} {p' q' p q : Proc} :
      Select p (.out a b p') → Select q (.inp a q') →
      Step (.par p q) (.par p' (subst q' b))
  | parL {p p' q : Proc} : Step p p' → Step (.par p q) (.par p' q)
  | parR {p p' q : Proc} : Step p p' → Step (.par q p) (.par q p')
  | nu {p p' : Proc} : Step p p' → Step (.nu p) (.nu p')
  | cong {p p' q q' : Proc} : Cong p p' → Step p' q' → Cong q' q →
      Step p q

/-- Communication: `ā⟨b⟩.0 | a(x).x̄.0 → 0 | b̄.0`. The sent channel `b`
is substituted for the input variable. -/
theorem comm_example (a b : ℕ) :
    Step (.par (.out (.const a) (.const b) .nil)
        (.inp (.const a) (.out (.var 0) (.const 0) .nil)))
      (.par .nil (.out (.const b) (.const 0) .nil)) :=
  Step.commSelect (Select.refl _) (Select.refl _)

/-- Communication on a restricted channel:
`νa.(ā⟨b⟩.0 | a(x).0) → νa.(0 | 0)`. -/
theorem scope_comm_example (b : ℕ) :
    Step (.nu (.par (.out (.var 0) (.const b) .nil) (.inp (.var 0) .nil)))
      (.nu (.par .nil .nil)) :=
  Step.nu (Step.commSelect (Select.refl _) (Select.refl _))

/-- A restricted name is transmitted: `νa.(b̄⟨a⟩.0 | b(x).x̄.0)` reduces
to `νa.(0 | ā.0)`, where the receiver's `var 0` now denotes the
restricted channel `a` (the `ν`-binder). -/
theorem bound_name_transmission (b : ℕ) :
    Step (.nu (.par (.out (.const b) (.var 0) .nil)
        (.inp (.const b) (.out (.var 0) (.const 0) .nil))))
      (.nu (.par .nil (.out (.var 0) (.const 0) .nil))) :=
  Step.nu (Step.commSelect (Select.refl _) (Select.refl _))

/-- Communication after swapping the parallel components by structural
congruence: `a(x).0 | ā⟨b⟩.0 → 0 | 0`. -/
theorem comm_after_swap (a b : ℕ) :
    Step (.par (.inp (.const a) .nil) (.out (.const a) (.const b) .nil))
      (.par .nil .nil) :=
  Step.cong (.par_comm _ _) (Step.commSelect (Select.refl _) (Select.refl _)) (.refl _)

/-- Scope extrusion: `(νa.P) | 0 ≡ νa.(P | 0)` when the other side is
closed (here it is `nil`). -/
theorem extrusion_example (p : Proc) :
    Cong (.par (.nu p) .nil) (.nu (.par p (liftProc 0 .nil))) :=
  Cong.scope _ _

/-- Scope extrusion under an outer restriction: the outside process
`out (var 0) nil` mentions the outer `ν`'s channel, and extrusion
lifts it to `var 1` so it still denotes that channel past the fresh
inner `ν`. -/
theorem extrusion_nested :
    Cong (.nu (.par (.nu (.out (.var 1) (.const 0) .nil))
        (.out (.var 0) (.const 0) .nil)))
      (.nu (.nu (.par (.out (.var 1) (.const 0) .nil)
        (.out (.var 1) (.const 0) .nil)))) :=
  Cong.nu_cong (Cong.scope _ _)

/-- Congruence is contextual: `par_nil` transported under an output
prefix. -/
theorem out_cong_example (a b : ℕ) (p : Proc) :
    Cong (.out (.const a) (.const b) (.par p .nil))
      (.out (.const a) (.const b) p) :=
  Cong.out_cong _ _ (Cong.par_nil p)

/-- Nested restrictions commute: swapping the two `ν` binders turns the
channel `var 1` (the outer binder) into `var 0` (now the inner one). -/
theorem nu_swap_example :
    Cong (.nu (.nu (.out (.var 1) (.const 0) .nil)))
      (.nu (.nu (.out (.var 0) (.const 0) .nil))) :=
  Cong.nu_swap _

/-- Guarded choice: the left branch communicates and the right branch
is discarded. -/
theorem sum_choice_example (a b : ℕ) :
    Step (.par (.sum (.out (.const a) (.const b) .nil) .nil)
        (.inp (.const a) .nil))
      (.par .nil .nil) :=
  Step.commSelect (Select.left _ _) (Select.refl _)

/-- Guarded input choice: the receiving sum selects its `a`-branch and
the `c`-branch is discarded. -/
theorem input_choice_example (a b c : ℕ) :
    Step (.par (.out (.const a) (.const b) .nil)
        (.sum (.inp (.const a) .nil) (.inp (.const c) .nil)))
      (.par .nil .nil) :=
  Step.commSelect (Select.refl _) (Select.left _ _)

/-- Two guarded sums communicate: each selects its matching branch. -/
theorem sum_sum_example (a b : ℕ) :
    Step (.par (.sum (.out (.const a) (.const b) .nil) .nil)
        (.sum (.inp (.const a) .nil) .nil))
      (.par .nil .nil) :=
  Step.commSelect (Select.left _ _) (Select.left _ _)

/-- Nested sums: selection is transitive through the outer sum. -/
theorem nested_sum_example (a b : ℕ) :
    Step (.par (.sum (.sum (.out (.const a) (.const b) .nil) .nil) .nil)
        (.inp (.const a) .nil))
      (.par .nil .nil) :=
  Step.commSelect (Select.trans (Select.left _ _) (Select.left _ _)) (Select.refl _)

/-- Parallel composition is commutative on a concrete pair. -/
theorem par_comm_example (a b : ℕ) :
    Cong (.par (.out (.const a) (.const b) .nil) .nil)
      (.par .nil (.out (.const a) (.const b) .nil)) :=
  Cong.par_comm _ _

end PiCalculus
end Cslib
