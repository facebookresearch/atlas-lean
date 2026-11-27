# Polynomial-time enumeration of maximal e-CCC-biclusters

**Definitions.** For a string $S$ over an alphabet $\Sigma$ and an integer $e \ge 0$, the $e$-neighbourhood $N(e,S)$ is the set of strings of length $|S|$ within Hamming distance $e$ of $S$; it has

$$|N(e,S)| = \sum_{i=0}^{e}\binom{|S|}{i}(|\Sigma|-1)^i = O\big(|S|^e|\Sigma|^e\big)$$

elements. In a discretized expression matrix with rows $R$ and columns $C$, an *$e$-CCC-bicluster* is a set of rows $I$ and contiguous columns $J$ together with a pattern $S$ of length $|J|$ such that the string of every row of $I$ on $J$ lies in $N(e,S)$. Maximality is defined as for exact [CCC-biclusters](maximal-ccc-biclusters-and-maxnodes-of-a-generalized-suffix-tree.md): row-, left- and right-maximal, with no other $e$-CCC-bicluster properly containing it.

**Theorem.** All maximal $e$-CCC-biclusters, optionally subject to minimum numbers of rows and columns, can be found and reported in time

$$O\Big(\max\big(|R|^2|C|^{1+e}|\Sigma|^e,\ |R||C|^{2+e}|\Sigma|^e\big)\Big),$$

which is $O(|R|^2|C|^{1+e}|\Sigma|^e)$ when $|R| \gg |C|$; for $e = 0$ the exact algorithm runs in $O(|R||C|)$. The same bound holds when missing values are treated as errors and when anticorrelated patterns are included; shifting patterns by up to $K$ symbols multiplies it by $K$.

## Expansion

The algorithm spells candidate patterns (models) over the transformed alphabet along a generalized suffix tree of the rows, tracking for each model its node-occurrences together with the number of errors used, in the manner of common-motif algorithms; a model is valid when enough distinct rows occur within $e$ errors, which yields all right-maximal $e$-CCC-biclusters. There are $O(|R||C|^{1+e}|\Sigma|^e)$ models, each extended in $O(|R|)$ work. A second pass inserts the valid models into a trie built from their reversed strings to delete those that are not left-maximal, and a hashing pass removes models defining the same bicluster. With $e > 0$ the suffix-link characterization of left-maximality no longer applies directly, which is why the explicit deletion step is needed.

## Depends on

- [Maximal CCC-biclusters correspond to MaxNodes of a generalized suffix tree](maximal-ccc-biclusters-and-maxnodes-of-a-generalized-suffix-tree.md)

## Sources

- Madeira SC, Oliveira AL, "A polynomial time biclustering algorithm for finding approximate expression patterns in gene expression time series", Algorithms Mol Biol (2009), Definitions 8–9, Lemma 4 and the section "e-CCC-Biclustering: Complexity analysis", <https://doi.org/10.1186/1748-7188-4-8>, PMCID PMC2709627.
