# Delta-encoded bit-vector edit distance in a verification window

Let $r = r_1\cdots r_m$ be a read and $s = s_1\cdots s_n$ a reference. The approximate-matching dynamic programme

$$C[i,j] = \min\{C[i,j-1]+1,\ C[i-1,j]+1,\ C[i-1,j-1] + [r_i \ne s_j]\}, \qquad C[0,j] = 0,\ C[i,0] = i,$$

gives in $C[m,j]$ the least edit distance between $r$ and a substring of $s$ ending at $j$.

**Verification window.** If a seed places the read at candidate start $d$ and the edit-distance threshold is $k$, every match within distance $k$ starts in $[d-k, d+k]$ and ends in $[d+m-k-1, d+m+k-1]$, so only a window of $m + 2k$ reference characters, and a band of $2k+1$ diagonals of $C$, needs to be computed.

**Delta encoding.** Adjacent cells of $C$ differ by $-1$, $0$ or $+1$, so column $j$ is encoded by bit vectors indexed by $i$: $VP_j[i] = [C[i,j]-C[i-1,j] = +1]$, $VN_j[i] = [C[i,j]-C[i-1,j] = -1]$, the horizontal analogues $HP_j, HN_j$, and the match mask $Eq[i] = [r_i = s_j]$. One column step is the word-parallel recurrence

$$\begin{aligned} X_v &= Eq \mid VN, & X_h &= \big(((Eq \mathbin{\&} VP) + VP) \oplus VP\big) \mid Eq,\\ HP &= VN \mid \lnot(X_h \mid VP), & HN &= VP \mathbin{\&} X_h,\\ VP' &= (HN \ll 1) \mid \lnot\big(X_v \mid (HP \ll 1)\big), & VN' &= (HP \ll 1) \mathbin{\&} X_v, \end{aligned}$$

with $C[m,j]$ updated from the top bits of $HP$ and $HN$. Each column costs $O(\lceil m/w\rceil)$ word operations on a $w$-bit machine, and $O(\lceil (2k+1)/w \rceil)$ in the banded variant.

Because $k$ is small for short reads (about 4–5% of the read length), the banded vectors fit in a few bits, so several candidate windows (or several reads) can be packed into the lanes of one SIMD register and verified simultaneously; a single pass over a window reports all end positions $j$ with $C[m,j] \le k$.

## Depends on

- [q-gram (seed) filtering lemma for approximate matching](../../q-gram-filtering-lemma-for-approximate-matching.md)
- [Edit distance algorithm](../../../../ComputerScience/string-algorithms/edit-distance/edit-distance.md)

## Expansion

At most $k$ deletions stretch a match to start as early as $d-k$ and end as late as $d+m+k-1$; at most $k$ insertions shrink it to the inner bounds; together they give the window. The bit-vector step works because, within a column, carries in the addition $(Eq \,\&\, VP) + VP$ propagate exactly along runs where a match lets a diagonal value travel down through $+1$ vertical steps, reproducing the min-recurrence for all rows at once. Pigeonhole or count filtering (any read within distance $k$ shares at least one of $k+1$ disjoint $q$-grams, or at least $|s| - (k+1)q + 1$ overlapping $q$-grams) generates the candidate locations $d$ that this verification consumes.

## Sources

- H. Cheng, H. Jiang, J. Yang, Y. Xu and Y. Shang, "BitMapper: an efficient all-mapper based on bit-vector computing", BMC Bioinformatics 16 (2015), Eqs. (1)–(3), Definition 1 and Lemma 1, <https://doi.org/10.1186/s12859-015-0626-9>, PMCID: PMC4462005.
- G. Myers, "A fast bit-vector algorithm for approximate string matching based on dynamic programming", Journal of the ACM 46 (1999), 395–415, <https://doi.org/10.1145/316542.316550>.
