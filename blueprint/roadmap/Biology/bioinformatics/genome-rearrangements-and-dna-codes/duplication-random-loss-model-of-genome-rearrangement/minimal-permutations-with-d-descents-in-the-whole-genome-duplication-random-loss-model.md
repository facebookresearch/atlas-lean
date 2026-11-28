# Minimal permutations with d descents in the whole-genome duplication–random loss model

**Model.** A genome of $n$ genes is a permutation $\sigma \in S_n$. A *duplication–loss step* duplicates a fragment of consecutive genes, inserting the copy immediately after the original (tandem duplication), and then deletes one copy of every duplicated gene (random loss). In the *whole-genome duplication–random loss* model the duplicated fragment is the whole genome. A descent of $\sigma$ is a position $i$ with $\sigma_i > \sigma_{i+1}$; $\pi$ is a pattern of $\sigma$ ($\pi \prec \sigma$) if some subsequence of $\sigma$ is order-isomorphic to $\pi$.

**Theorem (cost and pattern class).**

1. Exactly $\lceil \log_2 r(\sigma)\rceil$ whole-genome duplication–loss steps are necessary and sufficient to obtain $\sigma$ from the identity $12\cdots n$, where $r(\sigma)$ is the number of maximal increasing substrings of $\sigma$.
2. The permutations obtainable in at most $p$ steps are exactly those with at most $2^p - 1$ descents.
3. This set is a pattern-avoiding class with finite basis $\mathcal{B}_d$, $d = 2^p$: the permutations with $d$ descents that are minimal for $\prec$.

**Theorem (local characterization).** A permutation $\sigma$ of size $n$ is minimal with $d$ descents if and only if it has exactly $d$ descents and every ascent $\sigma_i\sigma_{i+1}$ satisfies $2 \le i \le n-2$ with $\sigma_{i-1}\sigma_i\sigma_{i+1}\sigma_{i+2}$ an occurrence of $2143$ or $3142$. In particular every ascent is surrounded by descents and $d+1 \le n \le 2d$.

**Theorem (enumeration of extreme sizes).**

1. Minimal permutations with $d$ descents of size $2d$ are the linear extensions (labellings by $1,\dots,2d$) of the ladder poset with $d$ steps, and are counted by the Catalan number

$$C_d = \frac{1}{d+1}\binom{2d}{d}.$$

2. Minimal permutations with $d$ descents of size $d+2$ are counted by

$$s_d = 2^{d+2} - (d+1)(d+2) - 2,$$

twice the number $2^{d+1} - \frac{(d+1)(d+2)}{2} - 1$ of non-interval subsets of $\{1,\dots,d+1\}$, via two explicit bijections onto the two kinds of such permutations.

## Expansion

One whole-genome duplication–loss step interleaves two increasing subsequences, so it can at most double the number of increasing runs, which gives the $\lceil\log_2 r\rceil$ cost and the descent bound $2^p - 1$. Having at most $d - 1$ descents is preserved under taking patterns, so the class is defined by avoiding its minimal non-members, the minimal permutations with $d$ descents. Minimality means that deleting any element destroys a descent; an ascent $\sigma_i < \sigma_{i+1}$ flanked by descents survives this test exactly when the four entries around it form $2143$ or $3142$. At the maximal size $2d$ ascents and descents alternate, and the order constraints form a ladder poset whose linear extensions biject with Dyck paths of length $2d$; at size $d+2$ there are exactly two ascents and the configurations are indexed by non-interval subsets.

## Sources

- Mathilde Bouvel and Elisa Pergola, "Posets and permutations in the duplication-loss model: minimal permutations with d descents", arXiv:0806.1494 (2008), Section 1 (Theorems 1–3, Proposition 1), Section 2 (Proposition 2, Theorem 4), Section 3 (Proposition 3, Theorem 5) and Section 4 (Theorem 6, Propositions 4–7), <https://doi.org/10.48550/arXiv.0806.1494>. Published version: Theoretical Computer Science 411 (2010) 2487–2501, <https://doi.org/10.1016/j.tcs.2010.03.008>.
