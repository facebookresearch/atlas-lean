# Hardness of string-to-graph substitution matching

**Problems.** A *labeled graph* $G=(V,E,\sigma)$ is a directed graph whose vertices carry strings over an alphabet $\Sigma$; a path spells the concatenation of its labels. Given $G$ and a query string $s$:
- **String to Graph Approximate Matching**: find a path and symbol substitutions, applied to the path labels and to $s$, making them equal, with the minimum number of substitutions.
- **String to Graph Restricted Approximate Matching**: the same with substitutions allowed only on the graph labels.
- **String to Graph Compatibility Matching** (decision): is there a path *compatible* with $s$, i.e. a path that becomes a restricted approximate matching of $s$ with any number of substitutions on the graph labels?

**Theorems.**
1. Compatibility Matching is NP-complete, even when all labels have length one, and even over a binary alphabet.
2. Consequently Restricted Approximate Matching admits no polynomial-time approximation within any factor unless P = NP (already deciding feasibility is hard), even with length-one labels or a binary alphabet.
3. Restricted Approximate Matching is W[2]-hard parameterized by the number of substitutions, even when the graph is at distance one from a DAG.
4. Approximate Matching (substitutions on both sides) is W[2]-hard parameterized by the number of substitutions, even at distance one from a DAG, and cannot be approximated within factors $\Omega(\log|V|)$ or $\Omega(\log|s|)$ unless P = NP.
5. With length-one labels, Compatibility Matching parameterized by $|s|$ is fixed-parameter tractable: it can be decided in time $2^{O(|s|)}\,O(|s|^{|s|+1}|V|^2\log|V|)$.

Restricting edits to the graph labels thus makes even feasibility intractable.

## Expansion

Compatibility asks for a path whose spelled length fits $s$ exactly, because substitutions on graph labels can fix any mismatch but cannot change lengths; with unit labels this is the problem of finding a simple path with exactly $|s|$ vertices, which encodes Longest Path. A separate reduction keeps the alphabet binary. The W[2]-hardness reductions are from Minimum Set Cover, with the number of substitutions corresponding to the number of chosen sets. The approximation lower bounds inherit Set Cover's logarithmic inapproximability. The FPT algorithm uses color coding: randomly color vertices with $|s|$ colors, and find colorful paths of length $|s|$ by dynamic programming over color subsets.

## Sources

- R. Dondi, G. Mauri, I. Zoppis, "Complexity Issues of String to Graph Approximate Matching", arXiv:2001.01961 (2020), Section 2 (problem definitions and compatibility), Section 3 (NP-completeness and inapproximability of compatibility and restricted matching), Section 4 (W[2]-hardness and logarithmic inapproximability), Section 5 (color-coding FPT algorithm parameterized by $|s|$), <https://doi.org/10.48550/arXiv.2001.01961>.
