/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Adèle rings of function fields

This file defines the restricted-product adèle ring attached to a field and a family of
valuation subrings.
-/

@[expose] public section

open scoped RestrictedProduct

/-- **Adèle ring of a field with respect to valuation subrings.** Let $F$ be a field, $P$ a type
(of places) and, for each $p \in P$, let $O_p$ be a valuation subring of $F$. The adèle ring of
$F$ with respect to $(O_p)_{p \in P}$ is the restricted product of the copies of $F$ with respect
to the subrings $O_p$: its elements are the families $(a_p)_{p \in P}$ with $a_p \in F$ for every
$p$ and $a_p \in O_p$ for all but finitely many $p$. -/
def FunctionFieldAdeleRing (F : Type*) [Field F] (P : Type*)
    (O : P → ValuationSubring F) : Type _ :=
  Πʳ p : P, [F, O p]

namespace FunctionFieldAdeleRing

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

noncomputable instance : CommRing (FunctionFieldAdeleRing F P O) :=
  inferInstanceAs (CommRing (Πʳ p : P, [F, O p]))

instance : DFunLike (FunctionFieldAdeleRing F P O) P (fun _ ↦ F) :=
  inferInstanceAs (DFunLike (Πʳ p : P, [F, O p]) P (fun _ ↦ F))

/-- **Extensionality for restricted-product adèles.** Let $F$ be a field, $P$ a type and, for
each $p \in P$, let $O_p$ be a valuation subring of $F$. If two adèles $a$ and $b$ of the adèle
ring of $F$ with respect to $(O_p)_{p \in P}$ satisfy $a_p = b_p$ for every $p \in P$, then
$a = b$. -/
@[ext]
theorem ext {a b : FunctionFieldAdeleRing F P O} (h : ∀ p, a p = b p) : a = b :=
  Subtype.ext <| funext h

/-- **Adèles are integral at almost all places.** Let $F$ be a field, $P$ a type and, for each
$p \in P$, let $O_p$ be a valuation subring of $F$. For every adèle $a$ of the adèle ring of $F$
with respect to $(O_p)_{p \in P}$, the component $a_p$ lies in $O_p$ for all but finitely many
$p \in P$. -/
theorem mem_valuationSubring_cofinitely (a : FunctionFieldAdeleRing F P O) :
    ∀ᶠ p in Filter.cofinite, a p ∈ O p :=
  a.2

end FunctionFieldAdeleRing
