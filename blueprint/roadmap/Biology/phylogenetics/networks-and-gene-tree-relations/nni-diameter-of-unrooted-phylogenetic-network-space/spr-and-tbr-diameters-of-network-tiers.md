# SPR and TBR diameters of phylogenetic network tiers

Use the networks and tiers $N_i(X)$ of [the NNI diameter bounds](nni-diameter-bounds-for-network-tiers.md), with $n = 2(\ell + i - 1)$ vertices in tier $i$. Subtree prune and regraft (SPR) and tree bisection and reconnection (TBR) extend to networks by detaching an edge at one or both ends and reattaching it elsewhere, keeping the result a network in the same tier. Each tier is connected under SPR and under TBR, and these define metrics $d_{\rm SPR}$, $d_{\rm TBR}$ within a tier, with diameters $\Delta_i^{\rm SPR}$, $\Delta_i^{\rm TBR}$.

**Theorem.**
1. (Inclusions) $\mathrm{NNI} \subseteq \mathrm{SPR} \subseteq \mathrm{TBR}$ as sets of moves, so $d_{\rm TBR} \le d_{\rm SPR} \le d_{\rm NNI}$; conversely $d_{\rm SPR}(N,N') \le 2\,d_{\rm TBR}(N,N')$ for $N, N' \in N_i(X)$.
2. (Lower bound) For $i \ge 1$ and $n \ge 6$,

$$\Delta_i^{\rm TBR} \ge \tfrac12\Delta_i^{\rm SPR} \ge \frac{(n-3)\ln(n/2 - 2) - (2i-1)\ln(i-1) - (n-2i)}{8\ln\big(2(n+i)\big)},$$

with the convention $\ln 0 = 0$.
3. (Upper bound) $\Delta_i^{\rm TBR} \le \Delta_i^{\rm SPR} \le n^2 + 4n$.

For tier 0 (trees) linear-order bounds on $\Delta_0^{\rm TBR} \le \Delta_0^{\rm SPR}$ were known before; the results above concern $i \ge 1$.

## Depends on

- [NNI diameter bounds for tiers of phylogenetic networks](nni-diameter-bounds-for-network-tiers.md)

## Expansion

Every TBR move can be simulated by at most two SPR moves, which gives the factor 2. The lower bound repeats the counting argument of the NNI case: the number of networks within $m$ SPR moves of a fixed one is bounded by counting, for each move, the choices of edge to detach and of attachment points, a polynomial in $n + i$ per move, while $|N_i(X)| \ge (\ell + i - 3)!/(i-1)!$. The upper bound transforms both networks into pseudo-Hamiltonian form and then rearranges the cycle with SPR moves; it would improve with a better bound on the SPR distance between pseudo-Hamiltonian networks.

## Sources

- A. Francis, K. T. Huber, V. Moulton, T. Wu, "Bounds for phylogenetic network space metrics", Journal of Mathematical Biology (2018), Definitions 2–3, Corollary 1, Lemmas 7–8, Propositions 4–5, <https://doi.org/10.1007/s00285-017-1171-0>, PMCID PMC5829221.
