# Reachability of open sets by trajectories of a fixed planar billiard is undecidable

There is an explicitly constructible bounded planar billiard table to which the halting problem of every Turing machine reduces: from a machine and an input one computes a boundary point and an open set that the orthogonal trajectory from the point meets exactly when the machine halts with a prescribed output pattern.

Let billiard tables, billiard flows and computable points be as in [billiard tables and billiard flows](billiard-tables-and-billiard-flows.md).

**Theorem.** There exists an explicitly constructible planar, bounded and finitely piecewise smooth billiard table $B$ with the following property. Given any Turing machine $M$, any integer $N \ge 0$, any input tape $t$, any integer $k \in \mathbb{Z}$ and any finite string $(t^*_{k-N}, \ldots, t^*_{k+N})$ of tape symbols, one can algorithmically construct a point $p \in \partial B$ and an open set $U \subset \mathbb{R}^2$ such that the billiard trajectory starting perpendicularly to $\partial B$ from $p$ intersects $U$ if and only if $M$ halts on $t$ with its head at position $k$ and outputs a tape whose entries $k-N, \ldots, k+N$ are $t^*_{k-N}, \ldots, t^*_{k+N}$ (Corollary 3 of the source). Consequently, deciding for this table whether a given orthogonal trajectory from a computable boundary point reaches a given computable open set is undecidable.

## Depends on

- [Billiard tables and billiard flows](billiard-tables-and-billiard-flows.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Take the table that simulates a fixed universal reversible Turing machine, as in the proof of the periodicity result; with this fixed table every Turing machine is simulated through its encoding as an input of the universal machine. The trajectory starting orthogonally at the point encoding the initial computation state reaches the boundary orthogonally at the point encoding the halting state with output tape $t^*$ and head position $k$ exactly when the machine halts with that output and position. The halting states whose output agrees with the prescribed symbols in positions $k-N, \ldots, k+N$ form a finite union of disjoint subintervals of the image of the halting encoding, and $U$ is a computable open neighborhood of this union small enough to contain no other halting state. This is the notion of Turing completeness by reachability used for steady Euler flows.

## Sources

- E. Miranda and I. Ramos, "Two-dimensional billiards are Turing complete", Proceedings of the National Academy of Sciences of the United States of America 123 (2026), no. 37, e2614500123, https://doi.org/10.1073/pnas.2614500123; read in arXiv:2512.19156v5 (Theorem 2 and Corollary 3 in Section 3, "Turing completeness of two-dimensional billiards", of arXiv:2512.19156v5).
