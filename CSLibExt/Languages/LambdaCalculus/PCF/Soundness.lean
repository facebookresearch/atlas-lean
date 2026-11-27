/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: soundness of the denotational semantics
-/
module

public import CSLibExt.Languages.LambdaCalculus.PCF.BigStep
public import CSLibExt.Languages.LambdaCalculus.PCF.Denotational

/-!
# Soundness

Evaluation preserves denotation (Plotkin 1977; Streicher 2006): if a closed term
`t` evaluates to `v`, then `t` and `v` have the same denotation. In particular a
closed term of ground type that evaluates to the numeral `n` denotes `n`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc
open OmegaCompletePartialOrder

namespace Tm

/-- **Soundness of the PCF denotational semantics.** Let $A$ be a PCF type and let $t$ and $v$
be closed terms of type $A$. If $t$ evaluates to $v$ under big-step call-by-name evaluation,
then for every environment $\eta$ of the empty context, the denotations of $t$ and $v$ at
$\eta$ are equal. -/
theorem Eval.denote_eq {A : Ty} {t v : Tm [] A} (h : Eval t v) (η : Env []) :
    denote t η = denote v η := by
  induction h with
  | lam => rfl
  | zero => rfl
  | succ _ ih => rw [denote_succ, ih, denote_numeral, denote_numeral, Part.map_some]
  | predZero _ ih => rw [denote_pred, ih, denote_zero, Part.map_some]; rfl
  | predSucc _ ih => rw [denote_pred, ih, denote_numeral, denote_numeral, Part.map_some]; rfl
  | ifzZero _ _ iht ihs =>
      rw [denote_ifz, iht, denote_zero, Part.bind_some]
      simp only [↓reduceIte]
      exact ihs
  | ifzSucc _ _ iht ihs =>
      rw [denote_ifz, iht, denote_numeral, Part.bind_some]
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      exact ihs
  | app _ _ ihf ihb =>
      rw [denote_app, ihf, denote_lam, ← denote_instantiate]
      exact ihb
  | fix _ ih =>
      rw [denote_fix_unfold]
      exact ih

/-- **Closed PCF terms that evaluate to a numeral denote its value.** Let $t$ be a closed PCF
term of the ground type of natural numbers and let $n$ be a natural number. If $t$ evaluates
to the numeral for $n$, then for every environment $\eta$ of the empty context, the denotation
of $t$ at $\eta$ is the defined element $n$ of the flat domain of partial natural numbers. -/
theorem Eval.denote_numeral {t : Tm [] .nat} {n : Nat} (h : Eval t (Tm.numeral n)) (η : Env []) :
    denote t η = Part.some n :=
  (h.denote_eq η).trans (Tm.denote_numeral η n)

end Tm

end Cslib.Languages.LambdaCalculus.PCF
