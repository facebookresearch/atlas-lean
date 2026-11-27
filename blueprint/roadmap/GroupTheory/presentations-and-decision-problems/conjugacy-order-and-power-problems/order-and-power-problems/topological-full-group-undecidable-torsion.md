# Topological full groups of higher-dimensional full shifts have finitely generated subgroups with undecidable torsion problem

For $d \ge 2$, the topological full group of the full $\mathbb{Z}^d$-shift on at least two symbols contains a finitely generated subgroup with undecidable torsion problem; for $d = 1$ the corresponding finite-state machine groups have decidable torsion problem.

Let $A$ be a finite alphabet with $|A| \ge 2$, $d \ge 1$, and $\sigma$ the shift action of $\mathbb{Z}^d$ on $A^{\mathbb{Z}^d}$. The topological full group of the full $\mathbb{Z}^d$-shift is the group of homeomorphisms $f$ of $A^{\mathbb{Z}^d}$ for which there is a continuous map $c\colon A^{\mathbb{Z}^d} \to \mathbb{Z}^d$ with $f(x) = \sigma^{c(x)}(x)$ for all $x$. If $d \ge 2$, this group contains a finitely generated subgroup with undecidable torsion problem (Corollary 1.5 of the source).

More generally (Theorem 1.4), the group of reversible finite-state machines on $n \ge 2$ symbols, $k \ge 1$ states and dimension $d$ has decidable torsion problem if $d = 1$, and contains a finitely generated subgroup with undecidable torsion problem if $d \ge 2$; finite-state machines with a single state are exactly the elements of the topological full group.

## Depends on

- [Order problem and torsion problem of a finitely generated group](order-problem.md)
- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A finite-state machine moves a head over a fixed tape without changing it, so its periodicity is a question about the paths the head can follow on a configuration. In dimension one a pigeonhole argument decides periodicity, and indeed finiteness of finitely generated subgroups. In dimension two and higher, the source derives undecidability from Kari's undecidability of the snake tiling problem: a finitely generated group of finite-state machines can make a head follow a snake through tiles, and every element is periodic exactly when no infinite snake exists.

## Sources

- S. Barbieri, J. Kari and V. Salo, "The group of reversible Turing machines: subgroups, generators, and computability", Forum of Mathematics, Sigma 13 (2025), article e176, https://doi.org/10.1017/fms.2025.10118 (corrigendum: article e186, https://doi.org/10.1017/fms.2025.10142); read in arXiv:2303.17270v1 (Theorem 1.4 and Corollary 1.5 of arXiv:2303.17270v1).
