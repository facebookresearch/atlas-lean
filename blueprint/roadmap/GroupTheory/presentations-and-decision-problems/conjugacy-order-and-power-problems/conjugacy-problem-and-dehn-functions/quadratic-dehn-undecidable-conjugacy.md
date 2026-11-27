# A finitely presented group with quadratic Dehn function and undecidable conjugacy problem

There exists a finitely presented group whose Dehn function is quadratic and whose conjugacy problem is undecidable. This solves a problem of Rips from 1994.

For a finite presentation $\langle A \mid R \rangle$, the Dehn function $f(n)$ is the least non-decreasing function such that every word of length at most $n$ representing $1$ is freely equal to a product of at most $f(n)$ conjugates of relators and their inverses; it is quadratic when it is bounded above and below by quadratic functions up to the usual equivalence ($f \preceq g$ if $f(n) \le C g(Cn) + Cn$ for some $C$). There exists a finitely presented group with quadratic Dehn function and undecidable conjugacy problem (Theorem 1.2 of the source).

A finitely presented group with quadratic Dehn function has decidable word problem, so the group of the theorem separates the word and conjugacy problems.

## Depends on

- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The group is built from an $S$-machine, a group-theoretic model of computation, simulating a Turing machine with non-recursive language of accepted inputs, embedded into a group with quadratic Dehn function following Olshanskii's earlier constructions of groups with small Dehn functions. Accepted inputs correspond to conjugacy of certain words with a fixed one, so conjugacy is undecidable while van Kampen diagrams of all trivial words have quadratic area.

## Sources

- A. Yu. Olshanskii and M. V. Sapir, "Conjugacy problem in groups with quadratic Dehn function", Bulletin of Mathematical Sciences 10 (2020), no. 1, article 1950023, https://doi.org/10.1142/S1664360719500231; read in arXiv:1809.00280v3 (Theorem 1.2 of arXiv:1809.00280v3).
