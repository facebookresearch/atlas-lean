# Distinct-substring and k-mer repeat rates from LCP arrays

**Setting.** Let $g = g_1 \cdots g_n$ be a string (a genome) of length $n$ over a finite alphabet. For a string $x$ let $f(x)$ be its number of (possibly overlapping) occurrences in $g$. Let $S$ be the suffix array of $g$, so the suffixes $g_{S[1]}\cdots g_n, g_{S[2]}\cdots g_n, \dots$ are in increasing lexicographic order, and let $\mathrm{LCP}[1] = 0$ and, for $2 \le i \le n$, $\mathrm{LCP}[i]$ be the length of the longest common prefix of the suffixes starting at $S[i-1]$ and $S[i]$.

**Complexity measures.** The distinct-substring rate and, for a length $1 \le k \le n$, the length-sensitive distinct and repeat rates are

$$D(g) = \frac{2\,\lvert\{x : f(x) > 0\}\rvert}{n(n+1)}, \qquad D_k(g) = \frac{\lvert\{x : f(x) > 0,\ |x| = k\}\rvert}{n-k+1}, \qquad R_k(g) = \frac{\sum_{|x| = k,\ f(x) > 1} f(x)}{n-k+1},$$

where $x$ ranges over non-empty strings. $D_k$ is the fraction of the $n-k+1$ $k$-mer positions that are first copies of distinct $k$-mers; $R_k$ is the fraction of positions covered by $k$-mers that occur at least twice. If $C(k,r)$ is the number of distinct $k$-mers occurring exactly $r$ times, then $(n-k+1)R_k = \sum_{r > 1} r\,C(k,r)$. The source prints "Therefore, $R_k=\sum_{r>1}r\cdot C(k,r)$", without the factor $n-k+1$; the form here follows from its definition of $R_k$ displayed above, since $\sum_{|x|=k,\,f(x)>1}f(x)=\sum_{r>1}r\,C(k,r)$.

**Lemma 1 (distinct substrings).**

$$\lvert\{x : f(x) > 0\}\rvert = \sum_{i=1}^{n} i - \sum_{i=1}^{n} \mathrm{LCP}[i] = \frac{n(n+1)}{2} - \sum_{i=1}^{n} \mathrm{LCP}[i].$$

**Lemma 2 (distinct $k$-mers).**

$$\lvert\{x : f(x) > 0,\ |x| = k\}\rvert = \lvert\{\, j : S[j] \le n-k+1 \text{ and } \mathrm{LCP}[j] < k \,\}\rvert.$$

**Lemma 3 (repeated $k$-mer occurrences).** Let $I_k$ be the set of maximal index intervals $[i,j]$, $2 \le i \le j \le n$, with $\mathrm{LCP}[u] \ge k$ for all $i \le u \le j$ (maximal: $\mathrm{LCP}[i-1] < k$ and, if $j < n$, $\mathrm{LCP}[j+1] < k$). Then

$$\sum_{|x| = k,\ f(x) > 1} f(x) = \sum_{[i,j] \in I_k} (j - i + 2).$$

**Consequence.** Given $S$ and $\mathrm{LCP}$, which can be built in $O(n)$ time, each of $D(g)$, $D_k(g)$ and $R_k(g)$ is computed by a single linear scan, so in $O(n)$ time and space overall.

## Expansion

Lemma 1: every substring is a prefix of some suffix. Within a block of the suffix array whose suffixes share a prefix $s$, the first suffix of the block carries the representative occurrence of $s$ and the others carry repeat occurrences. The $\mathrm{LCP}[i]$ common prefixes of the suffixes at $S[i-1]$ and $S[i]$ are exactly the repeat occurrences charged to position $i$, and each repeat occurrence is charged once. Subtracting all repeat occurrences from the $n(n+1)/2$ substring occurrences leaves one occurrence per distinct substring.

Lemma 2: the suffix at $S[j]$ has a $k$-prefix iff $S[j] \le n-k+1$, and that prefix is new in lexicographic order iff it differs from the $k$-prefix of the previous suffix, i.e. iff $\mathrm{LCP}[j] < k$. Lemma 3: suffixes sharing a $k$-prefix are consecutive in $S$; a maximal run $\mathrm{LCP}[i..j] \ge k$ links the $j-i+2$ suffixes $S[i-1], \dots, S[j]$, which are exactly the occurrences of one repeated $k$-mer.

Empirically, across 100 bacterial, plant and eukaryotic sequences and ten short-read aligners, $D_k$ and $R_k$ with $k$ close to (at most) the read length correlate with alignment precision and recall at about $0.95$, whereas the length-insensitive $D$ shows no correlation; repeats of length near the read length are what make reads ambiguous.

## Sources

- V. Phan, S. Gao, Q. Tran, N. S. Vo, "How genome complexity can explain the difficulty of aligning reads to genomes", BMC Bioinformatics 16 (Suppl 17) (2015) S3, Lemmas 1–3 and the definitions of $D$, $D_k$, $R_k$, <https://doi.org/10.1186/1471-2105-16-s17-s3>, PMCID PMC4674900.
