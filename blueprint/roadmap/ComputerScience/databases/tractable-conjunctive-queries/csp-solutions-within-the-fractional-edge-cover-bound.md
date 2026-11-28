# Solutions of a constraint satisfaction instance can be listed within the fractional edge cover bound

A [CSP instance](constraint-satisfaction-instances-and-their-hypergraphs.md) $I$ has at most $\|I\|^{\rho^*(H_I)}$ solutions, and
all of them can be listed in time $\|I\|^{\rho^*(H_I) + O(1)}$, where $\rho^*$ is the fractional edge cover number. The algorithm
extends partial solutions one variable at a time, and the size bound applied to each induced instance bounds every
intermediate list; it does not need a fractional edge cover as input. Consequently $\mathrm{Csp}(\mathcal H)$ is in polynomial
time for every class $\mathcal H$ of bounded fractional edge cover number.

## Depends on

- [Constraint satisfaction instances and their hypergraphs](constraint-satisfaction-instances-and-their-hypergraphs.md)
- [Natural join queries, their hypergraphs and fractional edge covers](../join-processing/natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)

## Proof depends on

- [AGM output-size bound for join queries](../join-processing/agm-output-size-bound-for-join-queries.md)

## Sources

- M. Grohe and D. Marx, "Constraint solving via fractional edge covers", *ACM Trans. Algorithms* 11(1) (2014) 4; arXiv:1711.04506 <https://arxiv.org/abs/1711.04506>, Lemma 3.2, Theorem 3.5 and Corollary 3.6.
