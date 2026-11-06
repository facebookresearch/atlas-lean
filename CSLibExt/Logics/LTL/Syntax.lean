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

/-- **Formulas of linear temporal logic.** For a type $A$ of atoms, the formulas of linear
temporal logic (LTL) over $A$ are generated inductively: every atom $a \in A$ is a formula, the
truth constant $\top$ is a formula, and if $\varphi$ and $\psi$ are formulas then so are the
negation $\neg\varphi$, the conjunction $\varphi \wedge \psi$, the next formula
$\mathbf{X}\,\varphi$ and the until formula $\varphi \mathbin{\mathbf{U}} \psi$. -/
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

/-- **Falsity in LTL.** The LTL formula $\bot$ (falsity) is defined as $\neg\top$, the negation
of the truth constant $\top$. -/
def bot : Formula Atom := .not .top

/-- **Disjunction in LTL.** For LTL formulas $\varphi$ and $\psi$, the disjunction
$\varphi \vee \psi$ is defined as $\neg(\neg\varphi \wedge \neg\psi)$. -/
def or (φ ψ : Formula Atom) : Formula Atom := .not (.and (.not φ) (.not ψ))

/-- **Implication in LTL.** For LTL formulas $\varphi$ and $\psi$, the implication
$\varphi \to \psi$ is defined as the disjunction $\neg\varphi \vee \psi$. -/
def imp (φ ψ : Formula Atom) : Formula Atom := or (.not φ) ψ

/-- **Bi-implication in LTL.** For LTL formulas $\varphi$ and $\psi$, the bi-implication
$\varphi \leftrightarrow \psi$ is defined as the conjunction
$(\varphi \to \psi) \wedge (\psi \to \varphi)$ of the two implications. -/
def iff (φ ψ : Formula Atom) : Formula Atom := .and (imp φ ψ) (imp ψ φ)

/-- **The eventually operator of LTL.** For an LTL formula $\varphi$, the formula
$\mathbf{F}\,\varphi$ ("eventually $\varphi$") is defined as the until formula
$\top \mathbin{\mathbf{U}} \varphi$.

On an ω-word, $\mathbf{F}\,\varphi$ holds at a position exactly when $\varphi$ holds at that
position or at some later one. -/
def eventually (φ : Formula Atom) : Formula Atom := .until .top φ

/-- **The always operator of LTL.** For an LTL formula $\varphi$, the formula
$\mathbf{G}\,\varphi$ ("always $\varphi$") is defined as $\neg\,\mathbf{F}\,\neg\varphi$, the
negation of "eventually $\neg\varphi$".

On an ω-word, $\mathbf{G}\,\varphi$ holds at a position exactly when $\varphi$ holds at that
position and at every later one. -/
def always (φ : Formula Atom) : Formula Atom := .not (eventually (.not φ))

/-- **The release operator of LTL.** For LTL formulas $\varphi$ and $\psi$, the release
formula $\varphi \mathbin{\mathbf{R}} \psi$ is defined as
$\neg(\neg\varphi \mathbin{\mathbf{U}} \neg\psi)$, the dual of until.

On an ω-word, $\varphi \mathbin{\mathbf{R}} \psi$ holds at a position when, from that position on,
$\psi$ holds up to and including the first position where $\varphi$ holds, or forever if there is
no such position. -/
def release (φ ψ : Formula Atom) : Formula Atom := .not (.until (.not φ) (.not ψ))

end Formula

end LTL
end Cslib
