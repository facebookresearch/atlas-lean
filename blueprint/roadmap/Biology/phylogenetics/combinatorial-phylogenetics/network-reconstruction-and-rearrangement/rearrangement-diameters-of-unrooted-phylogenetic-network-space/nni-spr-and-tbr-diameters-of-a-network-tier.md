# NNI, SPR and TBR diameters of a tier of unrooted phylogenetic networks

**Setting.** An (unrooted, binary) **phylogenetic network** on a leaf set $X$ with $\ell = |X| \ge 3$ is a connected graph whose vertices have degree 1 or 3, the degree-1 vertices bijectively labelled by $X$. If $N$ has $n$ vertices, then $n = 2(\ell + i - 1)$ for an integer $i \ge 0$, the **tier** (reticulation number) of $N$: the number of edges that must be deleted to obtain a phylogenetic tree (Lemma 5.1). Let $\mathcal N_i(X)$ be the set of tier-$i$ networks; NNI, SPR and TBR operations preserve the tier, and $\Delta_i$, $\Delta_i^{\mathrm{SPR}}$, $\Delta_i^{\mathrm{TBR}}$ denote the diameters of $\mathcal N_i(X)$ under these operations.

**Theorem.** For $i \ge 1$:
1. (Counting, Corollary 3.4) $|\mathcal N_i(X)| \ge \dfrac{(\ell+i-3)!}{(i-1)!}$.
2. (NNI lower bound, Theorem 4.3)

$$\Delta_i \ge \frac{1}{20}\Big[(n-3)\log_6\Big(\frac n2 - 2\Big) - (2i-1)\log_6(i-1) - (n-2i)\log_6 e - 2n\Big].$$

3. (NNI upper bound, Theorem 5.6) $\Delta_i \le 3n + \binom{n/2 + i - 1}{2} - 2$.
4. (SPR and TBR, Propositions 7.1–7.2) $\Delta_i^{\mathrm{TBR}} \le \Delta_i^{\mathrm{SPR}} \le n^2 + 4n$ and

$$\Delta_i^{\mathrm{TBR}} \ge \frac12 \Delta_i^{\mathrm{SPR}} \ge \frac{(n-3)\ln(\frac n2 - 2) - (2i-1)\ln(i-1) - (n-2i)}{8 \ln 2\,(n+i)}.$$

Moreover the whole space $\bigcup_i \mathcal N_i(X)$ is connected by NNI (or SPR, or TBR) moves together with triangle operations that blow a degree-3 vertex up into a 3-cycle or collapse one (Proposition 2.2, Corollary 2.3).

## Expansion

The lower bounds are counting arguments: at most $6^{2(\ell+i-1)+10m}$ networks lie within $m$ NNI moves of a given one (Proposition 4.1), while an explicit family of "echidna" networks built from a cycle with pendant leaves shows the tier contains at least $(\ell+i-3)!/(i-1)!$ networks; comparing the two with Stirling's formula forces $m$ to be of order $n \log n$. The upper bound is constructive: at most $\ell + i - 3$ NNI moves remove all non-trivial cut-edges and make the network simple, at most $n$ more make it pseudo-Hamiltonian, and two pseudo-Hamiltonian networks differ by at most $\binom{n/2+i-1}{2}$ moves, as in sorting by adjacent transpositions. Since NNI $\subseteq$ SPR $\subseteq$ TBR (Lemma 6.3) and TBR and SPR distances agree up to a factor of two (Lemma 6.4), the SPR and TBR diameters are sandwiched by the same counting. These bounds govern how far local search in network space may need to travel.

## Sources

- Andrew Francis, Katharina T. Huber, Vincent Moulton and Taoyang Wu, "Bounds for phylogenetic network space metrics", arXiv:1702.05609 (2017), Sections 2–7, Proposition 2.2, Corollaries 2.3 and 3.4, Proposition 4.1, Theorem 4.3, Lemmas 5.1 and 5.3–5.5, Theorem 5.6, Lemmas 6.3–6.4, Propositions 7.1–7.2, <https://doi.org/10.48550/arXiv.1702.05609>. Published version: Journal of Mathematical Biology 76 (2017) 1229–1248, <https://doi.org/10.1007/s00285-017-1171-0>.
