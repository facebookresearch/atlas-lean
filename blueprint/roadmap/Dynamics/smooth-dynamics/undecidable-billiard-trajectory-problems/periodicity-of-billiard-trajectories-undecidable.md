# Periodicity of trajectories of a fixed planar billiard is undecidable

There is an explicitly constructible bounded planar billiard table with piecewise smooth boundary for which no algorithm decides whether the trajectory from a given computable point and direction is periodic.

A *billiard table* is a bounded planar domain $B \subset \mathbb{R}^2$ whose boundary $\partial B$ is finitely piecewise smooth. The *billiard flow* moves a point particle at unit speed along straight lines in the interior of $B$, with elastic (specular) reflection at $\partial B$: the angle of incidence equals the angle of reflection. A trajectory is *periodic* if it returns to its initial position with its initial velocity. A point or direction is *computable* if a Turing machine outputs rational approximations of it to within $2^{-n}$ on input $n$.

**Theorem.** There exists an explicitly constructible planar, bounded and finitely piecewise smooth billiard table for which deciding whether a trajectory starting at a computable point and direction is periodic is algorithmically undecidable (Corollary 2 of the source).

## Depends on

None.

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

For every reversible Turing machine $M$ the source constructs a bounded planar billiard table whose billiard flow simulates $M$ step by step (Theorem 2): there are embeddings of a Cantor-type encoding of computation states into the table, a computable initial state corresponds to a rational boundary point from which the particle is launched orthogonally to $\partial B$, each transition of $M$ corresponds to a passage of the trajectory through corridors of the table built by adapting the computational bordisms of topological Kleene field theory, and halting states correspond to orthogonal arrivals at the boundary. Every Turing machine has an equivalent reversible one (Theorem 1 of the source, due to Bennett), so taking $M$ to be a universal reversible machine gives a fixed table. If $M$ halts on the input encoded by the starting point, the trajectory hits the boundary orthogonally, retraces its path and is periodic. If $M$ does not halt, injectivity of the dynamics of a reversible machine on computation states rules out a periodic loop, so the trajectory is not periodic. Undecidability of halting for the universal machine then gives the statement. The construction also shows that planar billiards are Turing complete (Corollary 1).

## Sources

- E. Miranda and I. Ramos, "Two-dimensional billiards are Turing complete", Proceedings of the National Academy of Sciences of the United States of America 123 (2026), no. 37, e2614500123, https://doi.org/10.1073/pnas.2614500123; read in arXiv:2512.19156v5 (Theorem 1, Theorem 2 and Corollaries 1 and 2 in the section "Turing completeness of two-dimensional billiards" of arXiv:2512.19156v5).
