/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Definable endomorphisms of ordered abelian groups (Kourovka Notebook Problem 18.16)

Kourovka Notebook, Problem 18.16 (O. V. Belegradek): is every definable endomorphism of every
ordered abelian group of the form `x ↦ r x` for a rational number `r`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Definability

@[expose] public section

namespace MathlibExt.ModelTheory.DefinableEndomorphismOrderedAbelianKourovka18Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.16 (O. V. Belegradek). UnsolvedMath
record UM-00701445 (`KOU-18.16`), dataset ulamai/UnsolvedMath v1.8.0.

Definable means definable with parameters in the pure language of ordered abelian groups, as in the
resolving paper; the language here has `0`, `-`, `+` and `≤`, which defines the same sets with
parameters as `{0, +, <}`. Since ordered abelian groups are torsion-free, `x ↦ (m / n) x` is stated
as `n • f x = m • x` with `n > 0`.
-/

/-- Function symbols of the pure language of ordered abelian groups: `0`, `-`, and `+`. -/
inductive OrderedAddGroupFunc : ℕ → Type
  | zero : OrderedAddGroupFunc 0
  | neg : OrderedAddGroupFunc 1
  | add : OrderedAddGroupFunc 2

/-- The relation symbol `≤` of the pure language of ordered abelian groups. -/
inductive OrderedAddGroupRel : ℕ → Type
  | le : OrderedAddGroupRel 2

/-- The pure first-order language of ordered abelian groups: `0`, `-`, `+` and `≤`. -/
def orderedAddGroupLanguage : FirstOrder.Language where
  Functions := OrderedAddGroupFunc
  Relations := OrderedAddGroupRel

/-- The canonical `orderedAddGroupLanguage`-structure on an ordered abelian group. -/
@[reducible]
def orderedAddGroupStructure (G : Type*) [AddCommGroup G] [LinearOrder G] :
    orderedAddGroupLanguage.Structure G where
  funMap := fun {_} f x =>
    match f with
    | .zero => 0
    | .neg => -x 0
    | .add => x 0 + x 1
  RelMap := fun {_} r x =>
    match r with
    | .le => x 0 ≤ x 1

/-- Kourovka 18.16: every endomorphism `f` of an ordered abelian group `G` whose graph
`{(x, f x)}` is definable with parameters in the pure language of ordered abelian groups is
`x ↦ r x` for a rational `r = m / n`, i.e. `n • f x = m • x` for all `x`. -/
def definableEndomorphismIsRationalMultiple : Prop :=
  ∀ (G : Type) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (f : G →+ G),
    @Set.Definable G Set.univ orderedAddGroupLanguage (orderedAddGroupStructure G) (Fin 2)
        {v | v 1 = f (v 0)} →
      ∃ (m : ℤ) (n : ℕ), 0 < n ∧ ∀ x : G, n • f x = m • x

/--
Resolved true: Ji, Xu and Qiu (arXiv:2608.17861, Theorem 3.2) prove that a definable endomorphism
`f` of an ordered abelian group, definable with parameters in the pure language, satisfies `d f(x) =
a x` for integers `a`, `d ≠ 0`; the Kourovka Notebook (21st issue) marks 18.16 solved citing this
preprint. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.16 (O. V. Belegradek);
resolution: H. Ji, F. Xu and D. Qiu, A note on definable endomorphisms of ordered abelian groups,
arXiv:2608.17861 (2026), Theorem 3.2; the Kourovka Notebook (21st issue) marks 18.16 solved,
https://arxiv.org/abs/2608.17861.
-/
public theorem_wanted definableEndomorphismIsRationalMultiple_holds :
    definableEndomorphismIsRationalMultiple

end MathlibExt.ModelTheory.DefinableEndomorphismOrderedAbelianKourovka18Problem16Wanted
