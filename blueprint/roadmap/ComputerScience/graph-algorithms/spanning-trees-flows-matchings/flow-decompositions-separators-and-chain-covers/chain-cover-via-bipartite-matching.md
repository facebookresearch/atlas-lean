# Minimum chain cover and maximum antichain by bipartite matching

For a finite poset $P$ with elements $x_1, \dots, x_n$, let $H$ be the bipartite graph joining a left copy of $x_i$ to a right copy of $x_j$ whenever $x_i < x_j$. From a maximum matching $M$ of $H$ and a minimum vertex cover $K$ of $H$ (König), merging $x_i$ and $x_j$ into one chain for every matched pair yields a chain cover with $n - |M|$ chains, and the elements neither of whose copies lies in $K$ form an antichain of size at least $n - |K| = n - |M|$; both are therefore optimal (Fulkerson's proof of Dilworth's theorem). Using Hopcroft-Karp for the matching, a minimum chain cover and a maximum antichain of an $n$-element poset given by its comparability matrix are computed on the word RAM in $O(n^{5/2})$ instructions.

## Proof sketch

Each matched pair reduces the number of chains by one; an element that is uncovered on both sides is not comparable to any other uncovered element because every comparability edge is covered.

## Depends on

- [Dilworth's theorem](../../../../Combinatorics/partially-ordered-sets/dilworth-s-theorem/dilworth-decomposition.md)
- [Kőnig's theorem for finite bipartite graphs](../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)
- [Chain cover](../../../../Combinatorics/partially-ordered-sets/dilworth-s-theorem/is-chain-cover-fin.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)
- [Hopcroft and Karp's bound on the number of phases](../maximum-bipartite-matching/card-le-hopcroft-karp-aux-sqrt.md)

## Sources

- D. R. Fulkerson, "Note on Dilworth's Decomposition Theorem for Partially Ordered Sets", Proceedings of the American Mathematical Society 7(4), 1956.
- R. P. Dilworth, "A Decomposition Theorem for Partially Ordered Sets", Annals of Mathematics 51(1), 1950.
- J. E. Hopcroft and R. M. Karp, "An n^{5/2} Algorithm for Maximum Matchings in Bipartite Graphs", SIAM Journal on Computing 2(4), 1973.
