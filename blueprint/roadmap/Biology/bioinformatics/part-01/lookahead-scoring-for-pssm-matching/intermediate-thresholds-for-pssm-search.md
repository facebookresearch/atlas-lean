# Intermediate thresholds for PSSM search

**Setting.** A PSSM of length $m$ over alphabet $\mathcal A$ is a function $M : [0, m-1] \times \mathcal A \to \mathbb R$, and the score of a word $w = w_0 \cdots w_{m-1}$ is $sc(w, M) = \sum_{h=0}^{m-1} M(h, w_h)$. Given a sequence $S$ of length $n$ and a threshold $th$, the PSSM matching problem asks for every $j \in [0, n-m]$ with $sc(S[j..j+m-1], M) \ge th$. Let $\max_h = \max_{a} M(h,a)$ and define, for $d \in [0, m-1]$,

$$\sigma_d = \sum_{h=d+1}^{m-1} \max_h, \qquad th_d = th - \sigma_d, \qquad pfxsc_d(w, M) = \sum_{h=0}^{d} M(h, w_h).$$

**Lemma (lookahead scoring).** The following are equivalent: (1) $pfxsc_d(w, M) \ge th_d$ for all $d \in [0, m-1]$; (2) $sc(w, M) \ge th$.

**Consequences.**
1. Scanning a window left to right and stopping at the first $d$ with $pfxsc_d < th_d$ is exact; it runs in $O(kn)$ time, $k$ the average number of columns evaluated per position ($k \le m$, usually much smaller).
2. On an enhanced suffix array of $S$, all suffixes sharing a prefix share its prefix scores, so a failed intermediate threshold at depth $d$ skips the whole interval of suffixes with that prefix (via the skip table), giving sublinear expected search time.
3. For a surjective alphabet map $\Phi : \mathcal A \to \underline{\mathcal A}$, the transformed matrix $\underline M(i, b) = \max\{M(i,a) : \Phi(a) = b\}$ satisfies $sc(\Phi(w), \underline M) \ge sc(w, M)$, so matches of $\underline M$ on the recoded sequence form a superset of the true matches and serve as an exact filter.
4. For integer-valued scores and an i.i.d. background, the smallest threshold $t$ whose tail probability $P(sc(X,M) \ge t)$ does not exceed a given p-value $\pi$ can be computed by a dynamic program over columns restricted to scores above the intermediate thresholds, and the rows may be permuted (most discriminative first) without changing the score distribution.

## Depends on

- [Score of a site under a position weight matrix](../../position-weight-matrices/score.md)
- [Suffix array](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [The LCP array](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)

## Expansion

For (2) ⇒ (1), the suffix after column $d$ contributes at most $\sigma_d$, so a full score of at least $th$ forces each prefix to be at least $th - \sigma_d$; for (1) ⇒ (2), take $d = m-1$, where $\sigma_{m-1} = 0$. Sorting columns by discrimination makes early failure likely, which is where the large speedups on nucleotide matrices come from (factors 17 to 275 over previous exact methods were reported). The filter in item 3 works because taking the maximum over each character class can only raise every column score.

## Sources

- M. Beckstette, R. Homann, R. Giegerich, S. Kurtz, "Fast index based algorithms and software for matching position specific scoring matrices", BMC Bioinformatics 7:389 (2006), Lemma 1, Definitions 1–2 (Eq 3) and the lazy-evaluation threshold algorithm, <https://doi.org/10.1186/1471-2105-7-389>, PMCID PMC1635428.
