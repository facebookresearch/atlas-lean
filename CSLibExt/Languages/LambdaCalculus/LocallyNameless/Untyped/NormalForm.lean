/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
public import Cslib.Foundations.Relation.Defs

/-!
# Relational β-normal forms of locally closed terms

For CSLib's locally nameless untyped λ-terms a term `M` is *relationally* β-normal when it has
no full β-step, `Relation.Normal FullBeta M`, and *syntactically* β-normal, `M.BetaNormal`, when
it contains no β-redex. On locally closed terms the relational notion implies the syntactic one.
This transfers CSLib's leftmost normalization theorem `Term.Leftmost.normalization`, whose
hypothesis is syntactic, to relational normal forms, the notion used by the uniqueness and
existence of normal forms in `Relation`:

* `betaNormal_of_normal`: a locally closed term with no full β-step contains no β-redex;
* `leftmost_of_normal`: if a locally closed term `M` β-reduces to a term `N` with no full β-step,
  then leftmost reduction takes `M` to `N`;
* `exists_leftmost_of_normalizable`: a locally closed term with a relational normal form reaches
  one by leftmost reduction.

Local closure cannot be dropped from `betaNormal_of_normal`: in the ill-scoped term
`app (abs (bvar 0)) (bvar 1)` the β-rule and both congruence rules for application require a
locally closed argument, so the term has no full β-step, yet it contains a redex.

## References

* H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984,
  Chapter 13 (the normalization theorem for leftmost reduction).
* M. Copes, *A machine-checked proof of the Standardization Theorem in λ-calculus*, 2018,
  formalized in CSLib as `Term.Leftmost.normalization`.
-/

-- Upstream overlap: leanprover/cslib#965 (head 643c1203) proves a related characterization for a
-- separate, inductively defined normal-form predicate. This file is independent of it.

public section

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.NormalForm

open Term
open scoped Term

universe u

variable {Var : Type u}

-- An application whose head is not an abstraction is not itself a redex.
private theorem countRedexes_app_of_not_isAbs {L N : Term Var} (h : ¬ L.IsAbs) :
    (app L N).countRedexes = L.countRedexes + N.countRedexes := by
  cases L with
  | abs body => exact absurd (IsAbs.abs body) h
  | bvar _ => rfl
  | fvar _ => rfl
  | app _ _ => rfl

variable [HasFresh Var]

/-- **Relational normal forms are syntactic normal forms.** A locally closed term with no full
β-step contains no β-redex. Local closure is needed: `app (abs (bvar 0)) (bvar 1)` has no full
β-step but contains a redex. The conclusion is the hypothesis of `Term.Leftmost.normalization`. -/
theorem betaNormal_of_normal {M : Term Var} (lc : M.LC) (h : Relation.Normal FullBeta M) :
    M.BetaNormal := by
  classical
  induction lc with
  | fvar x => exact rfl
  | @app L N hL hN ihL ihN =>
    have hna : ¬ L.IsAbs := by
      rintro ⟨body⟩
      exact h ⟨_, Xi.base (Beta.beta hL hN)⟩
    have hL0 : L.countRedexes = 0 := ihL fun ⟨_, hs⟩ => h ⟨_, Xi.appR hN hs⟩
    have hN0 : N.countRedexes = 0 := ihN fun ⟨_, hs⟩ => h ⟨_, Xi.appL hL hs⟩
    change (app L N).countRedexes = 0
    rw [countRedexes_app_of_not_isAbs hna, hL0, hN0]
  | abs xs body _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists (xs ∪ body.fv)
    have hxs : x ∉ xs := fun hm => hx (Finset.mem_union_left _ hm)
    have hxfv : x ∉ body.fv := fun hm => hx (Finset.mem_union_right _ hm)
    have hclose : (body ^ fvar x)⟦0 ↜ x⟧ = body := (open_close x body 0 hxfv).symm
    have hn : Relation.Normal FullBeta (body ^ fvar x) := by
      rintro ⟨B, hs⟩
      have hstep := FullBeta.step_abs_close (x := x) hs
      rw [hclose] at hstep
      exact h ⟨_, hstep⟩
    have hopen : (body ^ fvar x).countRedexes = 0 := ih x hxs hn
    change body.countRedexes = 0
    rwa [countRedexes_open_fvar] at hopen

/-- **Leftmost normalization for relational normal forms.** If a locally closed term `M`
β-reduces to a term `N` with no full β-step, then leftmost reduction takes `M` to `N`. -/
theorem leftmost_of_normal {M N : Term Var} (lc : M.LC) (h : M ↠βᶠ N)
    (hn : Relation.Normal FullBeta N) : M ↠ℓ N := by
  classical
  have lcN : N.LC := by
    rcases FullBeta.steps_lc_or_rfl h with ⟨_, hN⟩ | rfl
    · exact hN
    · exact lc
  exact Leftmost.normalization lc h (betaNormal_of_normal lcN hn)

/-- **Leftmost reduction finds relational normal forms.** A locally closed term that has a
relational normal form reaches one by leftmost reduction. -/
theorem exists_leftmost_of_normalizable {M : Term Var} (lc : M.LC)
    (h : Relation.Normalizable FullBeta M) : ∃ N, M ↠ℓ N ∧ Relation.Normal FullBeta N := by
  obtain ⟨N, hMN, hN⟩ := h
  exact ⟨N, leftmost_of_normal lc hMN hN, hN⟩

end Cslib.LambdaCalculus.LocallyNameless.Untyped.NormalForm
