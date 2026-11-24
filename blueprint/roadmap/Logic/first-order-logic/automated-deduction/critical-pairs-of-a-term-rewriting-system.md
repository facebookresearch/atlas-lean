# Critical pairs of a term rewriting system

Let $l_1 \to r_1$ and $l_2 \to r_2$ be rules of a term rewriting system, renamed so that they share no variables, and let $p$ be a position of $l_1$ such that $l_1|_p$ is not a variable and $l_1|_p$ and $l_2$ are unifiable with most general unifier $\sigma$ (if both rules are the same rule, $p$ is not the root). Then $(\sigma(r_1), \sigma(l_1)[\sigma(r_2)]_p)$ is a *critical pair*. A finite term rewriting system has finitely many critical pairs up to renaming of variables.

## Depends on

- [Term rewriting systems](term-rewriting-systems.md)

## Proof depends on

- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- N-ary ranked-signature adapter for curried unification (proof prerequisite)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, 2019/20, Section 4.4, definition of critical pairs and the note on overlaps of a rule with itself, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>
- F. Baader and T. Nipkow, *Term Rewriting and All That*, Cambridge University Press, 1998
