# Search schemes and the pigeonhole principle

**Setting.** Let $T$ be a text indexed by a bidirectional FM index, which can extend a matched pattern by one character on either side in constant time, and let $P$ be a pattern to be matched with at most $k$ errors (Hamming or edit distance).

**Pigeonhole principle.** If $P$ is partitioned into $k+1$ non-overlapping parts, every occurrence of $P$ with at most $k$ errors matches at least one part exactly. Hence all occurrences are found by exactly matching each part and extending each exact hit approximately to the full pattern.

**Search schemes.** Partition $P$ into $p$ parts $P_1,\dots,P_p$. A *search* is a triple $\mathcal{S} = (\pi, L, U)$ of arrays of length $p$, where $\pi$ is a permutation of $\{1,\dots,p\}$ with the *connectivity property* (for every $i$, the parts $P_{\pi[1]},\dots,P_{\pi[i]}$ form a contiguous block of $P$, so the match grows only to the left or right), and $L[i] \le U[i]$ are lower and upper bounds on the cumulative number of errors after parts $P_{\pi[1]},\dots,P_{\pi[i]}$ have been matched, with $L,U$ non-decreasing. A *search scheme* for $k$ errors is a set of searches such that every distribution of at most $k$ errors over the $p$ parts is accepted by at least one search; it is then lossless.

**Example ($k = 2$, $p = 3$).** The three searches $\mathcal{S}_1 = (123, 000, 022)$, $\mathcal{S}_2 = (321, 000, 012)$ and $\mathcal{S}_3 = (213, 001, 012)$ form a search scheme: $\mathcal{S}_1$ matches $P_1$ exactly and extends right with up to two errors; $\mathcal{S}_2$ matches $P_3$ exactly, then allows one error in $P_2$ and two in total; $\mathcal{S}_3$ matches $P_2$ exactly, extends left with at most one error, then right with between one and two.

## Depends on

- [FM-index backward search](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/backward-search.md)

## Expansion

The bidirectional index is what makes non-left-to-right part orders possible. The pigeonhole strategy is the special search scheme with $p = k+1$ searches, each starting with one exact part. General schemes limit the number of errors allowed while the matched string is still short, because near the root of the index the branching is dense and backtracking is expensive; later parts, when few index branches survive, may absorb the remaining errors. Checking losslessness amounts to enumerating the error vectors $(e_1,\dots,e_p)$ with $\sum e_i \le k$ and verifying that for some search the partial sums of $e_{\pi[1]}, e_{\pi[2]},\dots$ stay within $[L[i],U[i]]$. The cited paper keeps the scheme fixed but chooses the part boundaries dynamically for each pattern, from the sizes of the index intervals.

## Sources

- L. Renders, K. Marchal, J. Fostier, "Dynamic partitioning of search patterns for approximate pattern matching using search schemes", iScience 24(7) (2021) 102687, Background on search schemes (after Kucherov, Salikhov and Tsur), <https://doi.org/10.1016/j.isci.2021.102687>, PMCID PMC8246400.
