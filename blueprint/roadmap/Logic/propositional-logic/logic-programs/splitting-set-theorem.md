# Splitting set theorem

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). A set $U$ of atoms *splits* $P$ if, for every rule of $P$ whose head is in $U$, all atoms of its body, positive and negative, are in $U$. The *bottom* $b_U(P)$ is the set of rules of $P$ whose head is in $U$. For a set $X \subseteq U$, the *partial evaluation* $e_U(Q, X)$ of a program $Q$ deletes every rule having a positive body atom in $U \setminus X$ or a negative body atom in $X$, and removes the remaining body atoms that are in $U$ from the other rules.

**Theorem.** If $U$ splits $P$, then a set $M$ of atoms is a [stable model](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md) of $P$ if and only if $M = X \cup Y$ where $X$ is a stable model of $b_U(P)$ and $Y$ is a stable model of $e_U(P \setminus b_U(P), X)$.

So a program can be solved in layers: first the bottom, then the top evaluated at each stable model of the bottom. The theorem is due to V. Lifschitz and H. Turner (1994).

## Depends on

- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)
- [Normal logic program](normal-logic-program.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.4 (splitting sets, the base $b_U$ and the partial evaluation $e_U$ for programs with negation as failure) and Proposition 3.10 (the splitting theorem for answer sets).
