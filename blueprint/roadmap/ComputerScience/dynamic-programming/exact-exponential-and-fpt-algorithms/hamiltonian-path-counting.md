# Counting Hamiltonian paths in O(2^n n^3) time and polynomial space

There is a deterministic word-RAM program that, given a directed graph on $n$ vertices by its adjacency matrix, computes the number of its Hamiltonian paths in $O\big((n^3 + 1)\, 2^n\big)$ instructions using $O(n^2)$ words of memory, at every word size of $O(n \log n)$ bits sufficient to store the counts. In particular the Hamiltonian path problem is decidable in $O^*(2^n)$ time and polynomial space.

## Proof sketch

Enumerate subsets $S$ by bitmask, compute $w(S)$ by $n - 1$ matrix-vector products restricted to $S$, and accumulate with sign $(-1)^{n-|S|}$.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [HAMILTONIAN PATH (UNDIRECTED) as a decision problem](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/undirected-hamiltonian-path/hamiltonian-path-undirected-dec.md)

## Proof depends on

- [Karp-Bax inclusion-exclusion formula for Hamiltonian paths](karp-bax-inclusion-exclusion-formula.md)

## Sources

- R. M. Karp, "Dynamic Programming Meets the Principle of Inclusion and Exclusion", Operations Research Letters 1(2), 1982.
- E. T. Bax, "Inclusion and Exclusion Algorithm for the Hamiltonian Path Problem", Information Processing Letters 47(4), 1993.
- F. V. Fomin and D. Kratsch, "Exact Exponential Algorithms", Springer, 2010.
