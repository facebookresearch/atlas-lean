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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeNaturality

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeNaturalityTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

/-- Reflection of a base neutral is a natural semantic value. -/
example (n : Ne [Atom] Atom) : Sem.Natural Atom (reflect Atom n) :=
  reflect_natural Atom n

/-- Reflection of a function neutral is coherent at every future context. -/
example (n : Ne [Atom ⇒ Atom] (Atom ⇒ Atom)) :
    Sem.Natural (Atom ⇒ Atom) (reflect (Atom ⇒ Atom) n) :=
  reflect_natural (Atom ⇒ Atom) n

/-- Reification commutes with weakening a natural semantic value. -/
example (v : Sem [Atom] (Atom ⇒ Atom)) (hv : Sem.Natural (Atom ⇒ Atom) v) :
    (quote (Atom ⇒ Atom) v).rename
        (.succ : Ren [Atom] [Atom, Atom]) =
      quote (Atom ⇒ Atom)
        (Sem.rename (.succ : Ren [Atom] [Atom, Atom]) (Atom ⇒ Atom) v) :=
  quote_rename (Atom ⇒ Atom) .succ v hv

/-- The semantic identity environment is pointwise natural. -/
example :
    @SemEnv.Natural Unit [Atom, Atom ⇒ Atom] [Atom, Atom ⇒ Atom]
      SemEnv.identity := SemEnv.natural_identity

/-- Extending and then renaming a natural environment preserves the
naturality invariant. -/
example (η : SemEnv [Atom] [Atom]) (hη : η.Natural)
    (a : Sem [Atom] Atom) (ha : Sem.Natural Atom a) :
    SemEnv.Natural (SemEnv.rename
      (.succ : Ren [Atom] [Atom, Atom]) (SemEnv.cons a η)) :=
  SemEnv.Natural.rename (SemEnv.Natural.cons ha hη) .succ

/-- Evaluating an open function term in the identity environment yields a
natural Kripke function. -/
example (t : Tm [Atom] (Atom ⇒ Atom)) :
    Sem.Natural (Atom ⇒ Atom) (nbeEval t SemEnv.identity) :=
  nbeEval_natural t SemEnv.identity SemEnv.natural_identity

/-- Evaluation commutes with moving a natural environment into a future
context. -/
example (t : Tm [Atom] Atom)
    (ρ : Ren [Atom] [Atom, Atom]) :
    Sem.rename ρ Atom (nbeEval t SemEnv.identity) =
      nbeEval t (SemEnv.rename ρ SemEnv.identity) :=
  nbeEval_rename_sem t SemEnv.identity SemEnv.natural_identity ρ

/-- Renaming source variables is interpreted by precomposing the semantic
environment. -/
example (t : Tm [Atom] Atom)
    (ρ : Ren [Atom] [Atom, Atom]) (η : SemEnv [Atom] [Atom, Atom]) :
    nbeEval (Tm.rename ρ t) η = nbeEval t (SemEnv.compRen η ρ) :=
  nbeEval_rename_source t ρ η

/-- Evaluating a renaming viewed as a substitution agrees with environment
precomposition. -/
example (ρ : Ren [Atom] [Atom, Atom])
    (η : SemEnv [Atom] [Atom, Atom]) :
    @SemEnv.evalSub Unit [Atom] [Atom, Atom] [Atom] (Sub.ofRen ρ) η =
      @SemEnv.compRen Unit [Atom] [Atom, Atom] [Atom] η ρ :=
  SemEnv.evalSub_ofRen ρ η

/-- The identity substitution evaluates to the original environment. -/
example (η : SemEnv [Atom, Atom] [Atom]) :
    @SemEnv.evalSub Unit [Atom] [Atom] [Atom, Atom] Sub.id η = @η :=
  SemEnv.evalSub_id η

/-- Renaming substitution images before evaluation is accounted for by
precomposing the semantic environment. -/
example (σ : Sub [Atom] [Atom])
    (ρ : Ren [Atom] [Atom, Atom])
    (η : SemEnv [Atom] [Atom, Atom]) :
    @SemEnv.evalSub Unit [Atom] [Atom, Atom] [Atom]
        (fun x => Tm.rename ρ (σ x)) η =
      @SemEnv.evalSub Unit [Atom] [Atom] [Atom] σ
        (@SemEnv.compRen Unit [Atom] [Atom, Atom] [Atom] η ρ) :=
  SemEnv.evalSub_rename_images σ ρ η

/-- Evaluation of substitution images commutes with future weakening. -/
example (σ : Sub [Atom] [Atom ⇒ Atom])
    (η : SemEnv [Atom ⇒ Atom] [Atom ⇒ Atom])
    (hη : η.Natural) (ρ : Ren [Atom ⇒ Atom] [Atom, Atom ⇒ Atom]) :
    @SemEnv.rename Unit [Atom] [Atom ⇒ Atom] [Atom, Atom ⇒ Atom] ρ
        (@SemEnv.evalSub Unit [Atom] [Atom ⇒ Atom] [Atom ⇒ Atom] σ η) =
      @SemEnv.evalSub Unit [Atom] [Atom ⇒ Atom] [Atom, Atom ⇒ Atom] σ
        (@SemEnv.rename Unit [Atom ⇒ Atom] [Atom ⇒ Atom]
          [Atom, Atom ⇒ Atom] ρ η) :=
  SemEnv.rename_evalSub σ η hη ρ

/-- Normalization commutes with renaming an open term. -/
example (t : Tm [Atom] (Atom ⇒ Atom))
    (ρ : Ren [Atom] [Atom, Atom]) :
    normalizeTm (Tm.rename ρ t) = Tm.rename ρ (normalizeTm t) :=
  normalizeTm_rename t ρ

/-- The renaming law preserves equality by computed normal forms. -/
example (t u : Tm [Atom] (Atom ⇒ Atom)) (h : NbeEq t u)
    (ρ : Ren [Atom] [Atom, Atom]) :
    NbeEq (Tm.rename ρ t) (Tm.rename ρ u) := h.rename ρ

/-- A certified canonical term remains fixed after source renaming and
renormalization. -/
example (t : CanonicalTm [Atom] (Atom ⇒ Atom))
    (ρ : Ren [Atom] [Atom, Atom]) :
    normalizeTm (Tm.rename ρ t.1) = Tm.rename ρ t.1 := t.rename ρ

/-- Successive renamings of the source have the expected composite action on
the computed representative. -/
example (t : Tm [Atom] (Atom ⇒ Atom))
    (ρ : Ren [Atom] [Atom, Atom])
    (σ : Ren [Atom, Atom] [Atom, Atom, Atom]) :
    normalizeTm (Tm.rename σ (Tm.rename ρ t)) =
      Tm.rename (Var.comp ρ σ) (normalizeTm t) :=
  normalizeTm_rename_comp t ρ σ

/-- Semantic-environment precomposition is associative. -/
example (η : SemEnv [Atom] [Atom, Atom, Atom])
    (ρ : Ren [Atom, Atom] [Atom, Atom, Atom])
    (σ : Ren [Atom] [Atom, Atom]) :
    @SemEnv.compRen Unit [Atom] [Atom, Atom] [Atom]
        (@SemEnv.compRen Unit [Atom, Atom] [Atom, Atom, Atom] [Atom] η ρ) σ =
      @SemEnv.compRen Unit [Atom] [Atom, Atom, Atom] [Atom] η
        (Var.comp σ ρ) :=
  SemEnv.compRen_comp η ρ σ

/-- A concrete eta expansion remains stable when its free function is moved
under one additional source variable. -/
example :
    normalizeTm (Tm.rename (.succ : Ren [Atom ⇒ Atom] [Atom, Atom ⇒ Atom])
      (.lam (.app (.var (.succ .zero)) (.var .zero)) :
        Tm [Atom ⇒ Atom] (Atom ⇒ Atom))) =
      Tm.rename (.succ : Ren [Atom ⇒ Atom] [Atom, Atom ⇒ Atom])
        (normalizeTm (.lam (.app (.var (.succ .zero)) (.var .zero)) :
          Tm [Atom ⇒ Atom] (Atom ⇒ Atom))) :=
  normalizeTm_rename _ _

#print axioms reflect_natural
#print axioms quote_rename
#print axioms nbeEval_natural
#print axioms nbeEval_rename_sem
#print axioms nbeEval_rename_source
#print axioms SemEnv.rename_evalSub
#print axioms SemEnv.evalSub_rename_images
#print axioms normalizeNf_rename
#print axioms normalizeTm_rename

end Cslib.Languages.LambdaCalculus.Stlc.NbeNaturalityTests
