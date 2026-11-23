/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeEquivalence

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeEquivalenceTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

/-- A beta-redex and its contractum have the same computed eta-long normal
form. -/
example :
    NbeEq
      (.app (.lam (.var .zero)) (.var .zero) : Tm [Atom] Atom)
      (.var .zero) := by
  rfl

/-- A function variable and its eta-expansion have the same computed normal
form. -/
example :
    NbeEq
      (.var .zero : Tm [Atom ⇒ Atom] (Atom ⇒ Atom))
      (.lam (.app (.var (.succ .zero)) (.var .zero))) := by
  rfl

/-- NbE equality implies equality in every set-theoretic model. -/
example (t u : Tm [Atom] (Atom ⇒ Atom)) (h : NbeEq t u) : ModelEq t u :=
  h.modelEq

/-- Canonical terms cannot be distinct while computing to the same normal
form. -/
example (t u : Tm [Atom] Atom) (ht : IsCanonical t) (hu : IsCanonical u)
    (h : NbeEq t u) : t = u := h.eq_of_isCanonical ht hu

#print axioms NbeEq.iff_normalizeTm_eq
#print axioms NbeEq.modelEq
#print axioms NbeEq.canonical_unique

end Cslib.Languages.LambdaCalculus.Stlc.NbeEquivalenceTests
