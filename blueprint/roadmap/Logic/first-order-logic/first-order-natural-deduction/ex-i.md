# Existential introduction

Let $\Gamma$ be a finite list of formulas of a first-order
language $L$ with free variables in $\alpha$, let $\varphi$ be such a formula with one
additional bound variable, let $t$ be a term, and write $\varphi[t]$ for $\varphi$ with $t$
substituted for that bound variable. If $\Gamma \vdash \varphi[t]$ in natural deduction, then
$\Gamma \vdash \exists \varphi$, where $\exists \varphi$ abbreviates $\neg \forall \neg \varphi$
as in Mathlib.
