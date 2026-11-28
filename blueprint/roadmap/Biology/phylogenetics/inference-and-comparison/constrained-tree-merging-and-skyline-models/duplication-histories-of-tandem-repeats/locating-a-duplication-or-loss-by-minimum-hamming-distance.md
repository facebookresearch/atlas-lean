# Locating a duplication or loss by minimum Hamming distance

**Setting.** Let $b = b_1\cdots b_{j-1}b_{j+1}\cdots b_n$ and $c = c_1 \cdots c_n$ be two tandem-repeat sequences made of segments of equal length, descended from a common ancestor that contained all segments except possibly the one at position $j$: either segment $c_j$ arose by a duplication in the lineage of $c$, or segment $b_j$ was lost in the lineage of $b$. Write $H(s,t)$ for the Hamming distance between segments, $c|i$ for $c$ with its $i$-th segment removed, and $H(b, c|i)$ for the segmentwise Hamming distance between $b$ and $c|i$.

**Proposition.** If $H(b_i, c_i) \le H(b_i, c_\ell)$ for all $i$ and all $\ell \ne i$, then $i \mapsto H(b, c|i)$ attains its minimum at $i = j$.

## Expansion

Indexing the segments of $b$ by $\{1,\dots,n\}\setminus\{j\}$, removing $c_j$ aligns every $b_k$ with $c_k$, while removing $c_i$ with $i < j$ shifts the alignment between positions $i$ and $j$ so that $b_k$ is compared with $c_{k+1}$ there; each such comparison costs at least $H(b_k, c_k)$ by hypothesis, and similarly for $i > j$. The hypothesis says that orthologous segments are closer than paralogous ones, which is expected on average (not for every pair) when the duplications that created the segments preceded the speciation. Without fixed segment boundaries, the same principle is applied by deleting every window of length equal to the length difference and taking the minimizing position.

## Sources

- Belcaid M, Bergeron A, Poisson G, "The evolution of the tape measure protein: units, duplications and losses", BMC Bioinformatics (2011), Problem 2 and Proposition 1, <https://doi.org/10.1186/1471-2105-12-s9-s10>, PMCID PMC3271669.
