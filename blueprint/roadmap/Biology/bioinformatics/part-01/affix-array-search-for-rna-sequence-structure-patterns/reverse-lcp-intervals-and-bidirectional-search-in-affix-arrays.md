# Reverse lcp-intervals and bidirectional search in affix arrays

**Definitions.** Let $S$ be a sequence of length $n$ over $\{A,C,G,U\}$, $S^F = S$ and $S^R = S^{-1}$ its reverse. For $X \in \{F,R\}$, $\mathrm{suf}_X$ is the suffix array of $S^X \#$ (with a terminator $\#$ larger than every character) and $\mathrm{lcp}_X[k]$ the length of the longest common prefix of the suffixes at ranks $k-1$ and $k$. A **suffix-interval** $\ell$-$[i..j]$ in $\mathrm{suf}_X$ satisfies $\mathrm{lcp}_X[i] < \ell$, $\mathrm{lcp}_X[j+1] < \ell$ and $\mathrm{lcp}_X[k] \ge \ell$ for $i < k \le j$; it is an **lcp-interval** if moreover $i < j$ and $\mathrm{lcp}_X[k] = \ell$ for some $k \in \{i+1,\dots,j\}$. Its suffixes share the prefix $\delta_X(\ell\text{-}[i..j])$ of length $\ell$, which occurs in $S^X$ exactly at positions $\mathrm{suf}_X[i],\dots,\mathrm{suf}_X[j]$. The **affix array** consists of $\mathrm{suf}_F, \mathrm{suf}_R, \mathrm{lcp}_F, \mathrm{lcp}_R$ and affix-link tables $\mathrm{aflk}_F, \mathrm{aflk}_R$.

An **RNA sequence-structure pattern** is a pair $(P,R)$ of an IUPAC pattern $P$ of length $m$ and a non-crossing structure string $R$ of length $m$; position $i$ of $S$ matches if $S[i+k] \in \varphi(P[k])$ for all $k$ and $S[i+l]$, $S[i+r]$ are complementary for every base pair $(l,r)\in R$.

**Lemma 1.** For every lcp-interval $q = \ell$-$[i..j]$ in $\mathrm{suf}_X$ there is exactly one lcp-interval $q^{-1} = \ell'$-$[i'..j']$ in the table of the reverse sequence, its **reverse interval**, such that $\ell' \ge \ell$, its common prefix of length $\ell$ is $\delta_X(q)^{-1}$, and $j - i = j' - i'$ (both represent the same number of occurrences).

**Lemma 2.** If $\ell' = \ell$ then $(q^{-1})^{-1} = q$; if $\ell' > \ell$ then $(q^{-1})^{-1} \ne q$.

**Use.** The affix links store, for each lcp-interval, a pointer to its reverse interval. A bidirectional search keeps the current match as an interval in either table; extending to the right refines an interval in $\mathrm{suf}_F$, and switching direction follows the affix link and refines in $\mathrm{suf}_R$. For a stem-loop pattern the loop is matched first and then each base pair is matched by two consecutive extensions in opposite directions, so the complementarity constraint prunes the search immediately.

## Depends on

- [Suffix array](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [The LCP array](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)

## Expansion

The occurrences of a substring $w$ in $S$ correspond bijectively to the occurrences of $w^{-1}$ in $S^{-1}$, so the set of suffixes of $S^R$ starting with $w^{-1}$ is a contiguous interval of the same size; it may be deeper ($\ell' > \ell$) because all occurrences of $w$ may share a longer common left context, in which case the reverse of the reverse is a different interval. Applying Lemma 1 twice, depth is nondecreasing at each reversal: in the unequal case $\ell' > \ell$ the double reverse $(q^{-1})^{-1}$ differs from $q$ and has depth at least $\ell'$, hence strictly greater than $\ell$ (Fig. 3 of the source has depths $4 \to 5 \to 5$). The link tables make the reverse interval available in constant time per direction switch, which makes bidirectional matching of sequence-structure patterns much faster than unidirectional suffix-array search, where the paired position is reached only after the whole intervening loop.

## Sources

- F. Meyer, S. Kurtz, R. Backofen, S. Will, M. Beckstette, "Structator: fast index-based search for RNA sequence-structure patterns", BMC Bioinformatics 12 (2011) 214, Methods (preliminaries; RNA structural motifs; affix array data structure), Lemmas 1–3, <https://doi.org/10.1186/1471-2105-12-214>, PMCID PMC3154205.
