# Ordered Jaccard index equals the k-mer Jaccard index for paralogs

**Definitions.** For a string $s$ let $K(s)$ be its set of $k$-mers. With $E(s,s')$ the edit distance and $\ell$ the length of an optimal alignment ($\max(|s|,|s'|) \le \ell \le |s| + |s'|$), the edit error is $\mathrm{err}(s,s') = E(s,s')/\ell$. A **segmental duplication** (SD) within error threshold $\varepsilon$ is a pair of paralogous sequences $(G_i, G_j)$ of a genome with $\mathrm{err}(G_i, G_j) \le \varepsilon$, alignment length $\ell \ge 1000$, and overlap of at most $\varepsilon \cdot n$ bases between the copies. A **colinear $k$-mer matching** between $s$ and $s'$ is a set of index pairs $(i,j)$ such that the $k$-mers starting at $i$ in $s$ and at $j$ in $s'$ are equal and no two pairs cross ($i < i'$ iff $j < j'$); $s \circledast s'$ is the size of a maximum colinear matching, and the **ordered Jaccard index** is

$$\hat J(s, s') = \frac{s \circledast s'}{|K(s) \cup K(s')|}.$$

**Lemma.** Let $s, s'$ be paralogs, neither containing a repeated $k$-mer, that arose by copying a common ancestral sequence and then diverged by independent point mutations and small indels, and assume every $k$-mer they share is an unmutated copy of the same ancestral $k$-mer. Then

$$\hat J(s,s') = J\big(K(s), K(s')\big) = \frac{|K(s) \cap K(s')|}{|K(s) \cup K(s')|}.$$

Moreover $s \circledast s'$ can then be computed in linear time by scanning $s$ and $s'$ simultaneously.

## Depends on

- [Edit distance algorithm](../../../../ComputerScience/string-algorithms/edit-distance/edit-distance.md)
- [The k-mers of a string](../../de-bruijn-graph-genome-assembly/kmers.md)

## Expansion

Since $s$ and $s'$ have no repeated $k$-mers, each shared $k$-mer occurs once in each and can be matched at most once, so $s \circledast s' \le |K(s) \cap K(s')|$. Conversely, every shared $k$-mer is an unmutated copy of one ancestral $k$-mer, so its positions in $s$ and $s'$ descend from the same ancestral position; point mutations and indels preserve the order of surviving ancestral positions, so all shared $k$-mers are matched colinearly. Without the hypothesis on $s, s'$ themselves the lemma fails: for $k = 2$, ancestor $ACGTA$, $s = ACGAC$ and $s' = ACACA$ share only $AC$, so $J = 1/4$, but $(1,1), (4,3)$ is a colinear matching and $\hat J = 2/4$. So under the error model the two indices coincide, and lower bounds on the Jaccard index implied by the divergence threshold (used to seed SD candidates) transfer to $\hat J$, while the colinear version is cheaper to evaluate and less fooled by shuffled shared content. The lemma underlies fast SD detection and cross-species SD decomposition into elementary SDs and core duplicons.

## Sources

- H. Išerić, C. Alkan, F. Hach, I. Numanagić, "Fast characterization of segmental duplication structure in multiple genome assemblies", Algorithms for Molecular Biology 17:4 (2022), Definition 1 and Lemma 1, <https://doi.org/10.1186/s13015-022-00210-2>, PMCID PMC8932185.
