# Agreeing to disagree

Two agents share a prior $\mu$, a finite measure on a finite set $\Omega$ of states in which every singleton
is measurable, and have information partitions
$\mathcal P_1, \mathcal P_2$. If at $\omega$ it is common knowledge that agent 1's posterior of $A$
is $q_1$ and agent 2's is $q_2$ (the cell of the meet of $\mathcal P_1$ and $\mathcal P_2$ that
contains $\omega$ lies in the event where the posteriors take these values), and that cell is not
null, then $q_1 = q_2$.

This is Aumann's two-agent theorem on a finite state space. Aumann works on an arbitrary
probability space whose join cells are nonnull, so the two statements are incomparable. On finite
spaces his hypothesis implies the one used here, which concerns only the meet cell of $\omega$;
that extra generality relies on the convention that the posterior on a null cell is $0$.

## Informally uses

- [The tower step of the agreement theorem](measure-real-inter-cell-eq-mul.md): applied once for
  each agent.

## Background

- [Agreement theorem](agreement.md): the same statement for any family of agents.

## Sources

- R. J. Aumann, "Agreeing to disagree", Ann. Statist. 4(6) (1976), 1236–1239, Theorem (p. 1236), model (p. 1236) and Proposition (p. 1237).
