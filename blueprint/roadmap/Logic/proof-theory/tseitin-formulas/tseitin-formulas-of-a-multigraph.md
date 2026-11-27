# Tseitin formulas of a multigraph

Let $G = (V, E)$ be a finite multigraph (parallel edges allowed; self-loops are ignored in parities) and $\chi : V \to \{0,1\}$ a *charge*. The Tseitin formula $T(G, \chi)$ has one variable $x_e$ per edge and, for every vertex $v$, the CNF encoding of the parity constraint $\bigoplus_{e \ni v} x_e = \chi(v)$, which, for $\deg(v) \ge 1$ (counting non-loop edges), consists of $2^{\deg(v) - 1}$ clauses of width $\deg(v)$ (an isolated vertex contributes the empty clause if $\chi(v) = 1$ and nothing otherwise). If the maximum degree is $k$, $T(G,\chi)$ is a $k$-CNF with at most $|V| \max(1, 2^{k-1})$ clauses. The associated *Tseitin parity system* is the system of the $|V|$ linear equations over $\mathbb{F}_2$, with the same solutions.

## Depends on

- [CNF encoding of a parity constraint](../../propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/cnf-encoding-of-a-parity-constraint.md)

## Sources

- G. S. Tseitin, "On the Complexity of Derivation in Propositional Calculus", in Automation of Reasoning 2, Springer, 1983 (original 1968).
- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Definition 4.1 and Lemma 4.2.
