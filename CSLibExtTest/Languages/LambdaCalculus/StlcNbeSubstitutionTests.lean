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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeSubstitution

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeSubstitutionTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

/-- Reflected variables satisfy the logical invariant used by substitution. -/
example (x : Var [Atom, Atom] Atom) :
    Sem.Logical Atom (reflect Atom (.var x)) :=
  reflect_logical Atom (.var x)

/-- Reflection remains logical at function type, where the invariant includes
naturality and preservation of related arguments. -/
example (f : Var [Atom ⇒ Atom] (Atom ⇒ Atom)) :
    Sem.Logical (Atom ⇒ Atom) (reflect (Atom ⇒ Atom) (.var f)) :=
  reflect_logical (Atom ⇒ Atom) (.var f)

/-- Related base values have identical quoted normal forms. -/
example {v w : Sem [Atom] Atom} (h : Sem.Related Atom v w) :
    quote Atom v = quote Atom w :=
  quote_eq_of_related Atom h

/-- Related function values also have identical eta-long normal forms. -/
example {v w : Sem [Atom] (Atom ⇒ Atom)}
    (h : Sem.Related (Atom ⇒ Atom) v w) :
    quote (Atom ⇒ Atom) v = quote (Atom ⇒ Atom) w :=
  quote_eq_of_related (Atom ⇒ Atom) h

/-- Every entry in the semantic identity environment is logical. -/
example :
    @SemEnv.Logical Unit [Atom, Atom ⇒ Atom] [Atom, Atom ⇒ Atom]
      SemEnv.identity :=
  SemEnv.logical_identity

/-- Evaluation preserves logicality in an arbitrary logical environment. -/
example (t : Tm [Atom, Atom ⇒ Atom] (Atom ⇒ Atom))
    (η : SemEnv [Atom] [Atom, Atom ⇒ Atom]) (hη : η.Logical) :
    Sem.Logical (Atom ⇒ Atom) (nbeEval t η) :=
  nbeEval_logical t η hη

/-- Evaluation maps pointwise-related environments to related values. -/
example (t : Tm [Atom] (Atom ⇒ Atom))
    (ξ ζ : SemEnv [Atom, Atom] [Atom])
    (hξ : ξ.Logical) (hζ : ζ.Logical) (h : ξ.Related ζ) :
    Sem.Related (Atom ⇒ Atom) (nbeEval t ξ) (nbeEval t ζ) :=
  nbeEval_logically_related t ξ ζ hξ hζ h

/-- Interpreting the images of a substitution preserves logicality. -/
example (σ : Sub [Atom, Atom] [Atom])
    (η : SemEnv [Atom] [Atom]) (hη : η.Logical) :
    SemEnv.Logical (SemEnv.evalSub σ η) :=
  hη.evalSub σ

/-- The fundamental substitution result compares evaluation after syntactic
substitution with evaluation in the interpreted substitution environment. -/
example (t : Tm [Atom] (Atom ⇒ Atom)) (σ : Sub [Atom] [Atom, Atom])
    (η : SemEnv [Atom] [Atom, Atom]) (hη : η.Logical) :
    Sem.Related (Atom ⇒ Atom) (nbeEval (Tm.subst σ t) η)
      (nbeEval t (SemEnv.evalSub σ η)) :=
  nbeEval_subst_related t σ η hη

/-- Reification turns the logical substitution theorem into equality of
computed beta-eta normal forms. -/
example (t : Tm [Atom] (Atom ⇒ Atom)) (σ : Sub [Atom] [Atom, Atom]) :
    normalizeNf (Tm.subst σ t) =
      quote (Atom ⇒ Atom)
        (nbeEval t (SemEnv.evalSub σ SemEnv.identity)) :=
  normalizeNf_subst t σ

/-- The substitution law also applies to open applications. -/
example
    (t : Tm [Atom ⇒ Atom, Atom] Atom)
    (σ : Sub [Atom ⇒ Atom, Atom] [Atom, Atom]) :
    normalizeNf (Tm.subst σ t) =
      quote Atom (nbeEval t (SemEnv.evalSub σ SemEnv.identity)) :=
  normalizeNf_subst t σ

/-- The substitution theorem descends to canonical representatives as terms. -/
example (t : Tm [Atom] (Atom ⇒ Atom)) (σ : Sub [Atom] [Atom, Atom]) :
    normalizeTm (Tm.subst σ t) =
      (quote (Atom ⇒ Atom)
        (nbeEval t (SemEnv.evalSub σ SemEnv.identity))).toTm :=
  normalizeTm_subst t σ

/-- Ordinary beta instantiation is the single-substitution specialization. -/
example (body : Tm (Atom :: [Atom]) (Atom ⇒ Atom))
    (a : Tm [Atom] Atom) :
    normalizeNf (Tm.instantiate body a) =
      quote (Atom ⇒ Atom)
        (nbeEval body
          (SemEnv.evalSub (Sub.single a) SemEnv.identity)) :=
  normalizeNf_instantiate body a

/-- Substituting the identity function for a free function in an application
normalizes to the free argument. -/
example :
    normalizeNf
        (Tm.subst
          (fun
            | .zero => (.var .zero : Tm [Atom] Atom)
            | .succ .zero => (.lam (.var .zero) : Tm [Atom] (Atom ⇒ Atom)))
          (.app (.var (.succ .zero)) (.var .zero) :
            Tm [Atom, Atom ⇒ Atom] Atom)) =
      (.base (.var .zero) : Nf [Atom] Atom) := by
  rfl

/-- Substitution under a lambda keeps its bound variable while replacing the
free variable. -/
example :
    normalizeNf
        (Tm.subst
          (fun | .zero => (.var .zero : Tm [Atom] Atom))
          (.lam (.var (.succ .zero)) : Tm [Atom] (Atom ⇒ Atom))) =
      (.lam (.base (.var (.succ .zero))) : Nf [Atom] (Atom ⇒ Atom)) := by
  rfl

#print axioms reflect_logical
#print axioms quote_eq_of_related
#print axioms nbeEval_logical_related
#print axioms nbeEval_subst_related
#print axioms normalizeNf_subst
#print axioms normalizeTm_subst
#print axioms normalizeNf_instantiate

end Cslib.Languages.LambdaCalculus.Stlc.NbeSubstitutionTests
