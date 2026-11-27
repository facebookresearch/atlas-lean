# Canonical maximal unitigs as a spectrum-preserving string set

**Notation.** Strings are over $\Sigma = \{A, C, G, T\}$. For a multiset $R$ of strings, $\mathrm{occ}(x, R)$ counts occurrences of $x$ (overlapping occurrences counted separately), $x^{-1}$ is the reverse complement, $\mathrm{occ}_{cn}(x, R) = \mathrm{occ}(x, R) + \mathrm{occ}(x^{-1}, R)$ if $x \ne x^{-1}$ and $\mathrm{occ}(x, R)$ otherwise, $\mathrm{app}_{cn}(x, R) = \min(1, \mathrm{occ}_{cn}(x, R))$, and $\mathrm{ends}_{k}(U) = \{\mathrm{pre}_{k}(x), \mathrm{suf}_{k}(x) : x \in U\}$.

**Definition 1 (canonical maximal unitigs).** Given a multiset $R$ of strings and integers $k \ge 2$, $a \ge 1$, a set $U$ of strings is the set of canonical maximal unitigs of $R$ with $k$-mer size $k$ and abundance threshold $a$ if:

0. every $x \in U$ has $|x| \ge k$, and $x \ne y^{-1}$ for all $x, y \in U$;
1. (same canonical $k$-mer set, with abundances) for every $q \in \Sigma^k$, $\mathrm{occ}_{cn}(q, R) \ge a$ if and only if $\mathrm{occ}_{cn}(q, U) \ge 1$;
2. (no spanning of branching nodes) for every $q \in \Sigma^{k-1}$, if $\mathrm{occ}_{cn}(q, U) > 1$ then $q$ and $q^{-1}$ appear only as a prefix or suffix of strings of $U$;
3. (maximality) for every $q \in \mathrm{ends}_{k-1}(U)$,

$$\sum_{c \in \Sigma} \mathrm{app}_{cn}(q \cdot c, U) \ne 1 \quad \text{or} \quad \sum_{c \in \Sigma} \mathrm{app}_{cn}(c \cdot q, U) \ne 1.$$

Without reverse complements and with $a = 1$ these conditions describe exactly the maximal unitigs of the edge-centric de Bruijn graph of $R$ (nodes are $(k-1)$-mers, edges are the $k$-mers of $R$): unitigs are paths whose internal nodes have in- and out-degree one, and the maximal ones partition the $k$-mers of $R$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

Condition 1 makes $U$ a spectrum-preserving string set for the solid $k$-mers. Condition 2 forbids merging across a $(k-1)$-mer that occurs more than once in $U$, which is precisely a branching node, and also excludes two cyclic shifts of the same cycle. Condition 3 says an end of a unitig must be a source, a sink or a branching node, since otherwise the string could be extended by its unique neighbour. The string-centric form avoids bidirected-graph formalism and matches bottom-up algorithms that grow unitigs by $k$-mer membership queries.

## Sources

- A. Cracco, A. I. Tomescu, "Extremely fast construction and querying of compacted and colored de Bruijn graphs with GGCAT", Genome Research 33(7) (2023) 1198-1207, Methods (Definition 1, Lemma 1, Theorem 1, unitig merging), <https://doi.org/10.1101/gr.277615.122> (PMC10538363).
