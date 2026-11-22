/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `ee403ff4d46e775da313d0820bb55de4a379a800`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Varieties

/-! # Tests for Eilenberg varieties, pseudovarieties, and Schützenberger's theorem -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.VarietiesTests

/-- A singleton language over `Bool` is star-free, so its syntactic monoid is aperiodic. -/
example : IsAperiodic (SyntacticMonoid ({[true]} : Language Bool)) :=
  IsStarFree.aperiodic_syntacticMonoid (IsStarFree.singleton true)

/-- A union of two singleton languages is star-free, so its syntactic monoid is aperiodic. -/
example : IsAperiodic (SyntacticMonoid (({[true]} : Language Bool) + {[false]})) :=
  IsStarFree.aperiodic_syntacticMonoid
    (IsStarFree.union (IsStarFree.singleton true) (IsStarFree.singleton false))

/-- A concatenation of two singleton languages is star-free, so its syntactic monoid
is aperiodic. This exercises the one-copy shift argument for concatenation. -/
example : IsAperiodic (SyntacticMonoid (({[true]} : Language Bool) * {[false]})) :=
  IsStarFree.aperiodic_syntacticMonoid
    (IsStarFree.concat (IsStarFree.singleton true) (IsStarFree.singleton false))

/-- The complement of a singleton language is star-free, so its syntactic monoid is aperiodic. -/
example : IsAperiodic (SyntacticMonoid (({[true]} : Language Bool)ᶜ)) :=
  IsStarFree.aperiodic_syntacticMonoid
    (IsStarFree.compl (IsStarFree.singleton true))

/-- Star-free languages are regular, applied to a union of singletons. -/
example : (({[true]} : Language Bool) + {[false]}).IsRegular :=
  IsStarFree.isRegular
    (IsStarFree.union (IsStarFree.singleton true) (IsStarFree.singleton false))

/-- The aperiodic finite monoids form a pseudovariety. -/
example :
    IsPseudovariety (fun (M : Type) [Monoid M] [Finite M] ↦ IsAperiodic M) :=
  aperiodic_isPseudovariety

#print axioms IsStarFree.aperiodic_syntacticMonoid
#print axioms aperiodic_isPseudovariety

end Cslib.Language.VarietiesTests
