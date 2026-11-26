/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.Named.Untyped.LocallyNamelessBridge

/-!
# Labelled λ-terms for control-flow analysis

Labelled untyped λ-terms for control-flow analysis. Every subterm carries a label, and variables
are names. A program is well labelled when its labels are pairwise distinct (D. Van Horn and
M. Might, *Abstracting Abstract Machines*, ICFP 2010, §2.1, footnote 2) and has unique binders
when its λ-bound variables are pairwise distinct (A. Møller and M. I. Schwartzbach, *Static
Program Analysis*, February 2022 edition, §9.1; §10.1 in later editions). `erase` forgets the
labels and translates into CSLib's locally nameless terms; the image is locally closed.

* `Tm Var Lab`: variables `var x l`, abstractions `lam x body l` and applications `app fn arg l`,
  each with its label `l`.
* `Tm.subterms` lists every subterm of a term in preorder, the term itself first, so the nodes of
  a program are the members of `P.subterms`. `Tm.labels`, `Tm.binders` and `Tm.fv` collect the
  labels, the λ-bound variables and the free variables.
* `Tm.WellLabelled`, `Tm.UniqueBinders` and `Tm.Closed` are conditions on programs, not
  restrictions of the syntax. In a well-labelled program a label determines its subterm
  (`Tm.WellLabelled.label_inj`).
* `Tm.forget` maps a labelled term to CSLib's named untyped term, and `Tm.erase` composes it with
  the translation of named terms into locally nameless terms
  (`Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge.toLocallyNameless`):
  `Tm.erase_lc`, `Tm.fv_erase`.

## References

* D. Van Horn and M. Might, *Abstracting Abstract Machines*, ICFP 2010 (arXiv:1007.4446), §2.1.
* A. Møller and M. I. Schwartzbach, *Static Program Analysis*, Aarhus University, February 2022
  edition, §9.1 *Closure Analysis for the λ-calculus* (§10.1 in later editions).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ZeroCFA

universe u v

/-- **Labelled λ-terms.** Untyped λ-terms over a type `Var` of names in which every subterm
carries a label from `Lab`: a variable `var x l`, an abstraction `lam x body l` binding `x` in
`body`, and an application `app fn arg l`. -/
inductive Tm (Var : Type u) (Lab : Type v) : Type (max u v) where
  /-- The variable `x`, with label `l`. -/
  | var (x : Var) (l : Lab)
  /-- The abstraction `λx. body`, with label `l`. -/
  | lam (x : Var) (body : Tm Var Lab) (l : Lab)
  /-- The application of `fn` to `arg`, with label `l`. -/
  | app (fn arg : Tm Var Lab) (l : Lab)
  deriving DecidableEq

namespace Tm

/-- **The label of a term.** The label carried by the outermost node of a term. -/
def label {Var : Type u} {Lab : Type v} : Tm Var Lab → Lab
  | var _ l => l
  | lam _ _ l => l
  | app _ _ l => l

/-- **Subterms.** The subterms of a term in preorder: the term itself, then the subterms of the
body of an abstraction, or of the function and then of the argument of an application. -/
def subterms {Var : Type u} {Lab : Type v} : Tm Var Lab → List (Tm Var Lab)
  | var x l => [var x l]
  | lam x body l => lam x body l :: body.subterms
  | app fn arg l => app fn arg l :: (fn.subterms ++ arg.subterms)

/-- **Labels.** The labels of the subterms of a term, in preorder. -/
def labels {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : List Lab :=
  e.subterms.map label

/-- **Binders.** The variables bound by the abstractions of a term, in preorder and with
repetitions. -/
def binders {Var : Type u} {Lab : Type v} : Tm Var Lab → List Var
  | var _ _ => []
  | lam x body _ => x :: body.binders
  | app fn arg _ => fn.binders ++ arg.binders

/-- **Free variables.** The variables of a term that no enclosing abstraction binds. -/
def fv {Var : Type u} {Lab : Type v} [DecidableEq Var] : Tm Var Lab → Finset Var
  | var x _ => {x}
  | lam x body _ => body.fv \ {x}
  | app fn arg _ => fn.fv ∪ arg.fv

/-- **Well-labelled terms.** A term is well labelled when the labels of its subterms are pairwise
distinct. -/
def WellLabelled {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : Prop :=
  e.labels.Nodup

/-- **Unique binders.** A term has unique binders when the variables bound by its abstractions are
pairwise distinct. -/
def UniqueBinders {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : Prop :=
  e.binders.Nodup

/-- **Closed terms.** A term is closed when it has no free variable. -/
def Closed {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) : Prop :=
  e.fv = ∅

/-- **A term is one of its subterms.** Every term is a member of its own list of subterms. -/
theorem mem_subterms_self {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : e ∈ e.subterms := by
  cases e <;> simp [subterms]

/-- **Subterms of subterms.** If `s` is a subterm of `e` and `t` is a subterm of `s`, then `t` is
a subterm of `e`. -/
theorem subterms_trans {Var : Type u} {Lab : Type v} {e s t : Tm Var Lab}
    (hs : s ∈ e.subterms) (ht : t ∈ s.subterms) : t ∈ e.subterms := by
  induction e with
  | var x l =>
    simp only [subterms, List.mem_singleton] at hs
    subst hs
    exact ht
  | lam x body l ih =>
    simp only [subterms, List.mem_cons] at hs ⊢
    rcases hs with rfl | hs
    · simpa only [subterms, List.mem_cons] using ht
    · exact .inr (ih hs)
  | app fn arg l ihf iha =>
    simp only [subterms, List.mem_cons, List.mem_append] at hs ⊢
    rcases hs with rfl | hs | hs
    · simpa only [subterms, List.mem_cons, List.mem_append] using ht
    · exact .inr (.inl (ihf hs))
    · exact .inr (.inr (iha hs))

/-- **Labels identify subterms.** Suppose `e` is well labelled. Two subterms of `e` with the same
label are equal. -/
theorem WellLabelled.label_inj {Var : Type u} {Lab : Type v} {e s t : Tm Var Lab}
    (he : e.WellLabelled) (hs : s ∈ e.subterms) (ht : t ∈ e.subterms)
    (hl : s.label = t.label) : s = t := by
  exact List.inj_on_of_nodup_map he hs ht hl

/-- **Forgetting the labels.** The named untyped term (`Cslib.LambdaCalculus.Named.Untyped.Term`)
obtained by deleting every label. -/
def forget {Var : Type u} {Lab : Type v} : Tm Var Lab → Cslib.LambdaCalculus.Named.Untyped.Term Var
  | var x _ => .var x
  | lam x body _ => .abs x body.forget
  | app fn arg _ => .app fn.forget arg.forget

/-- **Erasure to locally nameless terms.** The locally nameless term of a labelled term: forget
the labels, then translate the named term into a locally nameless term. -/
def erase {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) :
    Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var :=
  Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge.toLocallyNameless e.forget

/-- **Erasures are locally closed.** The erasure of every labelled term is locally closed. -/
theorem erase_lc {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) :
    e.erase.LC := by
  exact Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge.toLocallyNameless_lc e.forget

/-- **Free variables after forgetting the labels.** Forgetting the labels of a term keeps its free
variables. -/
private theorem fv_forget {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) :
    e.forget.fv = e.fv := by
  induction e with
  | var x l => simp [forget, fv]
  | lam x body l ih => simp [forget, fv, ih]
  | app fn arg l ihf iha => simp [forget, fv, ihf, iha]

/-- **Free variables of an erasure.** The erasure of a labelled term has the same free variables
as the term. -/
theorem fv_erase {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) :
    e.erase.fv = e.fv := by
  unfold erase
  rw [Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge.fv_toLocallyNameless, fv_forget]

end Tm

end Cslib.Languages.LambdaCalculus.ZeroCFA
