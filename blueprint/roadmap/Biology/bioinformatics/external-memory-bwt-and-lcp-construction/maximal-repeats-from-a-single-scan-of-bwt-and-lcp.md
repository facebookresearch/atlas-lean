# Maximal repeats from a single scan of BWT and LCP

**Setting.** For a sequence collection of total length $n$ with suffix array $sa$, multi-string BWT $\mathrm{bwt}$ and LCP array $\mathrm{lcp}$ (constructed as in [BWT merging](merging-multi-string-bwts-with-lcp-computation.md)), a string $\alpha$ is a **Type 1 maximal repeat** if it occurs at least twice and every one-symbol extension $c\alpha$ or $\alpha c$ occurs fewer times; it is a **Type 2 maximal repeat** if it occurs at least twice and every extension occurs at most once.

**Interval characterization.** A string of length $\ell$ prefixes exactly the suffixes $sa[j],\dots,sa[i]$ iff $\mathrm{lcp}[k]\ge\ell$ for $k=j+1,\dots,i$ while $\mathrm{lcp}[j]<\ell$ and $\mathrm{lcp}[i+1]<\ell$. It is right-maximal iff some $\mathrm{lcp}[h]=\ell$ with $j<h\le i$, and left-maximal iff the BWT symbols preceding these suffixes are not all equal.

**Theorem 1.** All Type 1 maximal repeats can be computed in $O(n)$ time by a single sequential scan of $\mathrm{bwt}$ and $\mathrm{lcp}$, using $O(1)$ words of RAM (a stack of strictly increasing LCP values, size $O(\mathrm{maxlcp})$, kept in external memory with $O(1)$ amortized cost per operation).

**Theorem 2.** All Type 2 maximal repeats can be computed in $O(n)$ time by a single scan using $O(1)$ words of RAM: they correspond to runs $\mathrm{lcp}[j]<\mathrm{lcp}[j+1]=\dots=\mathrm{lcp}[i]>\mathrm{lcp}[i+1]$ whose BWT symbols $\mathrm{bwt}[j..i]$ are pairwise distinct.

## Depends on

- [Merging multi-string BWTs with LCP computation](merging-multi-string-bwts-with-lcp-computation.md)

## Expansion

The scan maintains, for each open LCP interval, its left end and minimum LCP value; an interval is closed when a smaller LCP value arrives, and at that moment its length, occurrence count and right-maximality are known. Left-maximality is tracked by an alphabet-size bit vector per stack entry that is OR-ed into the entry below on popping. For Type 2, a plateau of equal LCP values bounded by smaller values on both sides means each right extension occurs at most once, and distinct preceding symbols mean each left extension occurs at most once. Each position pushes at most one stack entry, giving linear time.

## Sources

- L. Egidi, F. A. Louza, G. Manzini, G. P. Telles, "External memory BWT and LCP computation for sequence collections with applications", Algorithms for Molecular Biology 14:6 (2019), section "Computation of maximal repeats", Theorems 1 and 2, <https://doi.org/10.1186/s13015-019-0140-0>, PMCID: PMC6408864.
