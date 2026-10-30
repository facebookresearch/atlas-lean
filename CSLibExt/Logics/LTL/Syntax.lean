/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear temporal logic: syntax
-/
module

public import Cslib.Init

/-!
# Syntax of linear temporal logic

Formulas of linear temporal logic (LTL) over a type of atoms, with primitive connectives truth,
negation, conjunction, `next`, and `until`, and the derived connectives falsity, disjunction,
implication, bi-implication, `eventually`, `always`, and `release`.

The syntax is independent of any semantics.  It is interpreted over upstream ω-words
(`Cslib.ωSequence`) in `CSLibExt.Logics.LTL.OmegaWord`.  An interpretation over state runs
`ℕ → State` of the local LTS core is future work.
-/

@[expose] public section

namespace Cslib
namespace LTL

universe u

/-- Formulas of linear temporal logic over a type of atoms.  The primitive
connectives are truth, negation, conjunction, `next`, and `until`. -/
inductive Formula (Atom : Type u) : Type u where
  | atom (a : Atom) : Formula Atom
  | top : Formula Atom
  | not (φ : Formula Atom) : Formula Atom
  | and (φ ψ : Formula Atom) : Formula Atom
  | next (φ : Formula Atom) : Formula Atom
  | until (φ ψ : Formula Atom) : Formula Atom
  deriving DecidableEq, Repr

namespace Formula

variable {Atom : Type u}

/-- Falsity as the negation of truth. -/
def bot : Formula Atom := .not .top

/-- Disjunction encoded using conjunction and negation. -/
def or (φ ψ : Formula Atom) : Formula Atom := .not (.and (.not φ) (.not ψ))

/-- Implication encoded using disjunction and negation. -/
def imp (φ ψ : Formula Atom) : Formula Atom := or (.not φ) ψ

/-- Bi-implication encoded using conjunction and implication. -/
def iff (φ ψ : Formula Atom) : Formula Atom := .and (imp φ ψ) (imp ψ φ)

/-- Eventuality: `φ` holds at some position. -/
def eventually (φ : Formula Atom) : Formula Atom := .until .top φ

/-- Invariance: `φ` holds at every position. -/
def always (φ : Formula Atom) : Formula Atom := .not (eventually (.not φ))

/-- Release, the dual of `until`: `ψ` holds up to and including the first position where `φ`
holds, or forever if there is no such position. -/
def release (φ ψ : Formula Atom) : Formula Atom := .not (.until (.not φ) (.not ψ))

end Formula

end LTL
end Cslib
