# Transitive suffix–prefix matches and left contexts

Let $R$ be a set of reads over $\{A, C, G, T\}$ in which no read is a prefix or suffix of another. A **suffix–prefix match (SPM)** $\langle r, t, \ell\rangle$ with $r, t \in R$ and $1 \le \ell < \min(|r|, |t|)$ means that the length-$\ell$ suffix of $r$ equals the length-$\ell$ prefix of $t$. An SPM $\langle r, t, \ell''\rangle$ is **transitive** if there are SPMs $\langle r, s, \ell\rangle$ and $\langle s, t, \ell'\rangle$ with

$$\ell + \ell' = |s| + \ell'' ;$$

otherwise it is **irreducible**. For $1 \le \ell' < |s|$ the **left context** is $\mathrm{LC}(s, \ell') = s[1 \dots |s| - \ell']$.

**Theorem.** An SPM $\langle r, t, \ell''\rangle$ is transitive if and only if there exist $s \in R$ and an irreducible SPM $\langle s, t, \ell'\rangle$ such that

$$\ell' > \ell'', \qquad |r| - \ell'' \ge |s| - \ell', \qquad s[1 \dots |s| - \ell'] = r\big[|r| - \ell'' - (|s| - \ell') + 1 \dots |r| - \ell''\big],$$

i.e. $\mathrm{LC}(s, \ell')$ is a suffix of $\mathrm{LC}(r, \ell'')$.

**Corollary.** Among the SPMs with a fixed right read $t$, listed by decreasing match length, the first is irreducible, and each later one is transitive exactly when some stored left context of an earlier irreducible SPM is a suffix of its own left context.

## Expansion

If $\langle r, t, \ell''\rangle$ is transitive through $s$, the overlap with $t$ starts later in $s$ than in $r$, so $s$'s part to the left of the $t$-overlap lies inside $r$'s part to the left of it; choosing the longest such $s$-match makes the witnessing SPM irreducible. Conversely, the suffix condition places $s$ inside $r$ followed by $t$, producing both required SPMs. Enumerating SPMs by a bottom-up traversal of the lcp-interval tree of the sorted read suffixes, which emits matches for each right read from longest to shortest, a dictionary of reversed left contexts (a blind trie) classifies each SPM in time proportional to the compared symbols. The traversal makes at most $3g - d$ calls over buckets of total size $g$, for $O(g + z)$ time with $z$ processed SPMs. After also discarding redundant matches between reads and reverse complements and internally contained reads, the non-redundant irreducible SPMs are exactly the arcs of the assembly string graph.

## Sources

- G. Gonnella, S. Kurtz, "Readjoiner: a fast and memory efficient string graph-based sequence assembler", BMC Bioinformatics 13 (2012) 82, Methods (definition of transitive SPMs, Theorem 1, left contexts, Algorithm 2 analysis, Eq. 7), <https://doi.org/10.1186/1471-2105-13-82>, PMCID PMC3507659.
