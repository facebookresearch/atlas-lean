# PBWT prefix and divergence arrays and long-match conditioning sets

Let $x_1, \dots, x_M \in \{0,1\}^L$ be haplotypes over sites $0, \dots, L-1$. For a site $k$, the **prefix array** $a_k$ is the permutation of $\{1, \dots, M\}$ that sorts the haplotypes by their reversed prefixes $x[k-1], x[k-2], \dots, x[0]$ in lexicographic order (ties broken stably by the previous order). The **divergence array** $d_k$ records, for each position $i \ge 2$ in this order, the smallest $j$ such that haplotypes $a_k[i]$ and $a_k[i-1]$ agree on all sites $j, \dots, k-1$; the match between them ending at $k-1$ thus has length $k - d_k[i]$.

**Adjacency of long matches.** For positions $i < i'$ in the order of $a_k$, the longest common suffix (match ending at $k-1$) of haplotypes $a_k[i]$ and $a_k[i']$ starts at $\max_{i < l \le i'} d_k[l]$. In particular, the haplotype with the longest match ending at $k-1$ with $a_k[i]$ is one of its neighbours $a_k[i-1], a_k[i+1]$, and the $P$ haplotypes with the longest such matches occupy a contiguous block around position $i$.

**Linear update.** Given $a_k, d_k$ and the alleles at site $k$, the arrays $a_{k+1}, d_{k+1}$ are obtained by a stable partition of $a_k$ into haplotypes with allele $0$ followed by those with allele $1$, while carrying running maxima of the divergence values inside each part; hence all $L$ arrays are built in one $O(LM)$ sweep.

**Conditioning-set selection.** SHAPEIT4 builds the PBWT of all $2N$ current haplotype estimates before each MCMC iteration, storing $a_k, d_k$ every eighth site together with the inverse permutation, so that any haplotype's position is found in constant time. To update individual $i$'s pair $(h_1, h_2)$, it takes at each stored site the $P$ haplotypes adjacent to $h_1$ and $h_2$, removes duplicates, and uses the resulting $K$ distinct haplotypes as the conditioning set of the Li–Stephens copying model within a sliding window. Long matches recur across sites, so $K$ shrinks as matches lengthen, and the selection costs $O(LN)$ overall rather than the $O(LN^2)$ of Hamming-distance selection.

## Remarks

Reverse-lexicographic sorting by prefixes places haplotypes with common suffixes in contiguous blocks, exactly as suffix sorting does in the Burrows–Wheeler transform; the length of the common suffix of two haplotypes in sorted order is the minimum over the intervening adjacent pairs, which is the range-maximum formula for divergence. Extending by one site preserves the relative order of haplotypes with equal alleles at $k$, because their reversed prefixes now begin with the same symbol and are then compared exactly as before; a haplotype's new predecessor within its part is the last earlier haplotype in $a_k$ with the same allele, so its new divergence value is the maximum of the old divergence values of the haplotypes strictly after that predecessor up to and including itself (and $k+1$, meaning an empty match, if it is the first haplotype of its part). This gives Durbin's single-pass algorithm. In phasing, haplotypes sharing long identical segments with the current estimates are the most informative copying sources, so choosing neighbours in the PBWT order approximates choosing the closest haplotypes locally at linear cost.

## Depends on

- [The Li–Stephens copying model](../../../population-structure/li-stephens-haplotype-copying-model/hmm.md)

## Sources

- O. Delaneau, J.-F. Zagury, M. R. Robinson, J. L. Marchini and E. T. Dermitzakis, "Accurate, scalable and integrative haplotype estimation", *Nature Communications* 10 (2019), 5436, Methods "Haplotype sampling" and "Haplotype selection", <https://doi.org/10.1038/s41467-019-13225-y> (PMC6882857).
- R. Durbin, "Efficient haplotype matching and storage using the positional Burrows–Wheeler transform (PBWT)", *Bioinformatics* 30 (2014), 1266–1272, Algorithms 1–2, <https://doi.org/10.1093/bioinformatics/btu014>.
