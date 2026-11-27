# Satisfaction of LTL formulas on runs

Let $v$ be a valuation that says which atoms are true at each state, and for a run $\rho$ (a sequence
of states $\rho(0), \rho(1), \dots$) and a natural number $k$ let $\rho^{(k)}$ be the suffix
$i \mapsto \rho(k + i)$. Whether $\rho$ satisfies an LTL formula $\varphi$ under $v$ is defined by
recursion on $\varphi$: an atom $a$ holds when $v$ makes $a$ true at $\rho(0)$; truth always holds;
$\neg \varphi$ holds when $\varphi$ does not; $\varphi \wedge \psi$ holds when both do;
$\mathsf{X}\, \varphi$ holds when $\rho^{(1)}$ satisfies $\varphi$; and
$\varphi \mathbin{\mathsf{U}} \psi$ holds when there is a $k$ such that $\rho^{(k)}$ satisfies $\psi$
and $\rho^{(j)}$ satisfies $\varphi$ for all $j < k$.

This is the [satisfaction relation on ω-words](satisfies.md), stated for runs of a system with a
valuation on its states.
