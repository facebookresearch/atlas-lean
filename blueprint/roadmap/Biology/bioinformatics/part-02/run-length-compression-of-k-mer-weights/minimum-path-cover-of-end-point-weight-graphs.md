# Minimum path cover of end-point weight graphs

**Definition (end-point weight graph).** Given a collection of weighted strings, the graph $G$ has one node per string with two sides labelled by the weights of its first and last $k$-mer, and an edge between two nodes having a side with the same weight. A node may be reoriented (its two side labels swapped). An oriented path $u_1 \to \cdots \to u_\ell$ requires $u_i.\mathrm{back} = u_{i+1}.\mathrm{front}$; a path cover visits every node exactly once. Write a node by its end-points $(x, y)$ with $x \le y$.

**Incidence sets.** For a weight $w$ in the set $W$ of distinct end-points, the incidence set $I_w$ is the set of nodes with end-point $w$.

**Lemma 1.** If $d$ equal nodes $(x, y)$ are present, they can be oriented into one path with end-points $(x, x)$ or $(y, y)$ when $d$ is even, and with end-points $(x, y)$ when $d$ is odd.

After preprocessing with Lemma 1 (collapsing all $(x, x)$ nodes and all copies of $(x, y)$), no node has equal end-points and each $(x, y)$ occurs at most twice. Partition $W = W_{\mathrm{odd}} \cup W_{\mathrm{even}}$ by the parity of $|I_w|$.

**Lemma 2.** If $|I_w|$ is odd, $w$ is an end-point of some path in every optimal cover.

**Lemma 3.** $|W_{\mathrm{odd}}|$ is even.

**Lemma 4.** If $W_{\mathrm{even}} = \emptyset$, then an optimal cover has $|W_{\mathrm{odd}}|/2$ paths, and greedily extending maximal paths attains it.

**Lemma 5.** Repeatedly merging two nodes on a weight of minimum even frequency simplifies each connected component either to a single node or to a graph with $I_w = \emptyset$ for all even-frequency weights $w$.

**Theorem 1.** Let $\mathcal{C}_{\mathrm{even}}$ be the set of connected components of the preprocessed graph whose nodes have only even-frequency end-points. Then a minimum path cover $C^*$ satisfies

$$|C^*| = |\mathcal{C}_{\mathrm{even}}| + \frac{|W_{\mathrm{odd}}|}{2},$$

and the min-cover algorithm (preprocess, merge on minimum even frequency, then greedy cover) is optimal and runs in $\Theta(m)$ amortized time and space for $m$ nodes.

Although minimum path cover is NP-hard on general directed graphs, this structure makes it linear-time here, which gives the optimal reordering and reorientation of strings for run-length compressed $k$-mer weights.

## Depends on

- [Run-length encoding of order-preserving k-mer weights](run-length-encoding-of-order-preserving-k-mer-weights.md)

## Expansion

Each node contributes two end-point occurrences, so $\sum_w |I_w| = 2|G|$ is even and the number of odd terms is even (Lemma 3). Along a path every internal junction consumes two occurrences of one weight, so a weight of odd frequency always leaves one occurrence unmatched at a path end (Lemma 2); with only odd weights, each path accounts for exactly two of them and maximal greedy paths achieve this (Lemma 4). Merging on a minimum even frequency weight never changes parities and never strands a weight, so even-only components collapse to a single path (Lemma 5). Summing over components gives Theorem 1; constant-time retrieval of the minimum even frequency is what keeps the merging phase linear.

## Sources

- G. E. Pibiri, "On weighted k-mer dictionaries", Algorithms for Molecular Biology 18 (2023) 3, sections on representing runs of weights and computing a minimum-size path cover (Definitions 1-3, Lemmas 1-5, Theorem 1), <https://doi.org/10.1186/s13015-023-00226-2> (PMC10276434).
