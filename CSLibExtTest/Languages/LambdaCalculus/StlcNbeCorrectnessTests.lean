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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCorrectness

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeCorrectnessTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

/-- NbE computes a beta redex in an open context. -/
example :
    normalizeTm
        (.app (.lam (.var .zero)) (.var .zero) : Tm [Atom] Atom) =
      (.var .zero : Tm [Atom] Atom) := rfl

/-- NbE eta-expands a neutral function. -/
example :
    normalizeTm (.var .zero : Tm [Atom ⇒ Atom] (Atom ⇒ Atom)) =
      .lam (.app (.var (.succ .zero)) (.var .zero)) := rfl

/-- The computed result is equal to its source in every set-theoretic model. -/
example (I : Unit → Type) (t : Tm [Atom] (Atom ⇒ Atom)) :
    SemEq I t (normalizeTm t) := normalizeTm_semEq I t

/-- The same correctness theorem is independent of the chosen base model. -/
example (t : Tm [Atom] (Atom ⇒ Atom)) : ModelEq t (normalizeTm t) :=
  normalizeTm_modelEq t

/-- Syntactically equal computed forms certify model equality of their inputs. -/
example (t u : Tm [Atom] (Atom ⇒ Atom)) (h : normalizeTm t = normalizeTm u) :
    ModelEq t u := modelEq_of_normalizeTm_eq h

#print axioms quote_denote
#print axioms reflect_related
#print axioms nbeEval_related
#print axioms normalizeTm_modelEq

end Cslib.Languages.LambdaCalculus.Stlc.NbeCorrectnessTests
