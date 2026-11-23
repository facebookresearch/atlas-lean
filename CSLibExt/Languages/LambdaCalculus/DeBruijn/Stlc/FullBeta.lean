/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Full beta termination for embedded intrinsic STLC terms
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.CslibEmbedding
import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.StrongNorm
public import Cslib.Foundations.Relation.Basic
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

/-!
# Full beta termination for embedded intrinsic STLC terms

The intrinsic de Bruijn development's existing `Step` relation is weak call-by-value reduction.
This module makes a different statement: the canonical locally nameless embedding of every
intrinsically typed term is strongly normalizing for upstream full beta reduction, including for
open source contexts.

The theorem is obtained by transporting typing and applying upstream `strong_norm`.  It introduces
no normalization hypothesis and does not identify full beta reduction with call-by-value.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ : List (Ty Base)}

/-- Upstream full beta reduction on the locally nameless target syntax. -/
abbrev LocallyNamelessFullBeta : LocallyNamelessTerm → LocallyNamelessTerm → Prop :=
  Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta

/-- Compatible full beta reduction on intrinsic terms.  Unlike `Step`, this relation contracts
without a value restriction and propagates under lambdas and through both application positions. -/
@[reduction_sys "βᵢ"]
inductive FullBeta {Base : Type u} :
    {Γ : List (Ty Base)} → {A : Ty Base} → Tm Γ A → Tm Γ A → Prop where
  | beta {Γ : List (Ty Base)} {A B : Ty Base}
      (body : Tm (A :: Γ) B) (a : Tm Γ A) :
      FullBeta (.app (.lam body) a) (Tm.instantiate body a)
  | appFun {Γ : List (Ty Base)} {A B : Ty Base}
      {f f' : Tm Γ (A ⇒ B)} (h : FullBeta f f') (a : Tm Γ A) :
      FullBeta (.app f a) (.app f' a)
  | appArg {Γ : List (Ty Base)} {A B : Ty Base}
      (f : Tm Γ (A ⇒ B)) {a a' : Tm Γ A} (h : FullBeta a a') :
      FullBeta (.app f a) (.app f a')
  | lam {Γ : List (Ty Base)} {A B : Ty Base}
      {body body' : Tm (A :: Γ) B} (h : FullBeta body body') :
      FullBeta (.lam body) (.lam body')

namespace Tm

/-- A source beta redex and its intrinsic capture-avoiding reduct embed as a genuine
upstream beta step. -/
theorem toLocallyNamelessWith_beta (names : List Nat)
    (hlen : names.length = Γ.length) (hnames : names.Nodup)
    (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    LocallyNamelessFullBeta
      (toLocallyNamelessWith names (.app (.lam body) a))
      (toLocallyNamelessWith names (Tm.instantiate body a)) := by
  rw [toLocallyNamelessWith_instantiate]
  apply Term.Xi.base
  apply Term.Beta.beta
  · exact (toLocallyNamelessWith_typing (.lam body) hlen hnames).lc
  · exact (toLocallyNamelessWith_typing a hlen hnames).lc

/-- Canonical-context form of `toLocallyNamelessWith_beta`. -/
theorem toLocallyNameless_beta (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    LocallyNamelessFullBeta
      (toLocallyNameless (.app (.lam body) a))
      (toLocallyNameless (Tm.instantiate body a)) := by
  apply toLocallyNamelessWith_beta
  · simp
  · exact List.nodup_range

end Tm

namespace FullBeta

/-- Every intrinsic full-beta step is simulated by one real upstream full-beta step, uniformly
for every well-formed choice of free names for the source context. -/
theorem toLocallyNamelessWith {t u : Tm Γ A} (h : FullBeta t u)
    {names : List Nat} (hlen : names.length = Γ.length) (hnames : names.Nodup) :
    LocallyNamelessFullBeta
      (Tm.toLocallyNamelessWith names t) (Tm.toLocallyNamelessWith names u) := by
  induction h generalizing names with
  | beta body a =>
      exact Tm.toLocallyNamelessWith_beta names hlen hnames body a
  | appFun h a ih =>
      rw [Tm.toLocallyNamelessWith_app, Tm.toLocallyNamelessWith_app]
      exact Term.Xi.appR
        (Tm.toLocallyNamelessWith_typing a hlen hnames).lc
        (ih hlen hnames)
  | appArg f h ih =>
      rw [Tm.toLocallyNamelessWith_app, Tm.toLocallyNamelessWith_app]
      exact Term.Xi.appL
        (Tm.toLocallyNamelessWith_typing f hlen hnames).lc
        (ih hlen hnames)
  | @lam Γ A B body body' h ih =>
      rw [Tm.toLocallyNamelessWith_lam, Tm.toLocallyNamelessWith_lam]
      apply Term.Xi.abs names.toFinset
      intro x hx
      rw [Tm.open_toLocallyNamelessWith_lam,
        Tm.open_toLocallyNamelessWith_lam]
      apply ih
      · simp [hlen]
      · exact List.nodup_cons.mpr ⟨by simpa using hx, hnames⟩

/-- Canonical embeddings simulate every intrinsic full-beta step. -/
theorem toLocallyNameless {t u : Tm Γ A} (h : FullBeta t u) :
    LocallyNamelessFullBeta t.toLocallyNameless u.toLocallyNameless := by
  apply h.toLocallyNamelessWith
  · simp
  · exact List.nodup_range

end FullBeta

namespace Tm

/-- Every embedded intrinsically typed term is strongly normalizing for real upstream full beta
reduction.  The statement includes open intrinsic contexts: their variables are represented by
the canonical upstream context `locallyNamelessContext Γ`. -/
theorem toLocallyNameless_stronglyNormalizing (t : Tm Γ A) :
    Relation.SN LocallyNamelessFullBeta t.toLocallyNameless :=
  Cslib.LambdaCalculus.LocallyNameless.Stlc.strong_norm t.toLocallyNameless_typing

/-- Intrinsic full beta reduction is strongly normalizing for every typed term.  Accessibility is
pulled back along `FullBeta.toLocallyNameless`; injectivity of the embedding is not needed. -/
theorem fullBeta_stronglyNormalizing (t : Tm Γ A) :
    Relation.SN (@FullBeta Base Γ A) t := by
  have embedded : Relation.SN LocallyNamelessFullBeta t.toLocallyNameless :=
    t.toLocallyNameless_stronglyNormalizing
  have pulled : Acc
      (InvImage (fun a b => LocallyNamelessFullBeta b a) Tm.toLocallyNameless) t :=
    InvImage.accessible Tm.toLocallyNameless embedded
  exact Acc.recOn pulled
    (motive := fun current _ => Relation.SN (@FullBeta Base Γ A) current)
    fun current _ ih =>
      Acc.intro current fun previous step =>
        ih previous step.toLocallyNameless

/-- Closed intrinsic terms are a direct special case of full-beta strong normalization. -/
theorem toLocallyNameless_stronglyNormalizing_closed (t : Tm [] A) :
    Relation.SN LocallyNamelessFullBeta t.toLocallyNameless :=
  t.toLocallyNameless_stronglyNormalizing

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
