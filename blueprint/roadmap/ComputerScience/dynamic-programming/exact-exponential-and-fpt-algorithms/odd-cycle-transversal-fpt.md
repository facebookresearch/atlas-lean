# Odd cycle transversal is fixed-parameter tractable by iterative compression

There is a single deterministic word-RAM program that, given an $n$-vertex simple graph $G$ and an integer $k$, decides whether $G$ has an odd cycle transversal of at most $k$ vertices within $C \cdot 3^k \cdot (n+1)^5$ instructions for an absolute constant $C$, and on yes-instances also outputs such a transversal $X$ together with a proper $2$-colouring of $G - X$.

## Proof sketch

Iterative compression over $n$ vertices, at most $3^{k+1}$ guesses per compression step, and one minimum vertex separator computation per guess by dense augmenting paths in $O(n^4)$ instructions.

## Depends on

- [Odd cycle transversal instances](../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/odd-cycle-transversal/odd-cycle-transversal-instance.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Odd cycle transversal compression via minimum vertex separators](oct-compression-step.md)
- [Minimum vertex separators by vertex splitting](../../graph-algorithms/spanning-trees-flows-matchings/flow-decompositions-separators-and-chain-covers/minimum-vertex-separators.md)

## Sources

- B. Reed, K. Smith and A. Vetta, "Finding Odd Cycle Transversals", Operations Research Letters 32(4), 2004.
- F. Hüffner, "Algorithm Engineering for Optimal Graph Bipartization", Journal of Graph Algorithms and Applications 13(2), 2009.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
