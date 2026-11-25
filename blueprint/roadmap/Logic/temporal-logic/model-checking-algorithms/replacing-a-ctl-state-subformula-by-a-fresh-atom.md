# Replacing a CTL* state subformula by a fresh atom

Let $M = \langle S, R, L\rangle$ be a Kripke structure over $AP$ with a total transition relation, $\varphi$ a CTL$^*$ state formula, $\psi$ a state subformula of $\varphi$, and $p \notin AP$ a fresh atomic proposition. Let $M'$ be $M$ with $p$ added to the label of exactly the states $s$ with $M, s \models \psi$, and let $\varphi[p/\psi]$ replace every occurrence of $\psi$ in $\varphi$ by $p$.

**Theorem.** For every state $s$, $M, s \models \varphi$ if and only if $M', s \models \varphi[p/\psi]$. The same holds for every path formula and every path.

**Proof.** By structural induction on CTL$^*$ state and path formulas, simultaneously.
- An occurrence of $\psi$ is evaluated at a state, and $p$ holds in $M'$ at exactly the states where $\psi$ holds in $M$.
- Formulas without occurrences of $\psi$ do not mention $p$. Their truth is the same in $M$ and $M'$, since $M'$ differs only in the label $p$.
- Every other clause of the semantics is compositional: Boolean connectives, $\mathbf{X}$ and $\mathbf{U}$ on suffixes, path quantifiers over the same set of paths, and a state formula read on a path at its first state.

## Background

- [State formulas of CTL$^*$](../ctl/ctl-state-and-path-formulas/state-formula.md)

## Sources

- T. Willemse, *Algorithms for Model Checking (2IW55)*, Lecture 1 "The temporal logics CTL$^*$, CTL and LTL: syntax and semantics", Eindhoven University of Technology, 2008, <https://www.win.tue.nl/%7Etimw/teaching/amc/2008/week1.pdf>: the syntax of CTL$^*$ state and path formulas and their semantics on states and paths of a Kripke structure, on which the induction above is built.
