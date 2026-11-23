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

Concrete substitution, communication, scope, and guarded-choice calculations
are checked in `CSLibExtTest.Languages.PiCalculus.BasicTests`.
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

/-- Substitution leaves a process with no `var 0` untouched: a
constant channel stays constant, and the empty process stays empty. -/
theorem subst_nil (n : Name) : subst .nil n = .nil := rfl

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

end PiCalculus
end Cslib
