# Trade-offs and joint amplifiers under Bd and dB updating

Let $G_N$ be a connected undirected graph on $N$ nodes with positive edge weights $w(u,v)$; residents have fitness $1$ and mutants fitness $r\ge 1$. In the **Birth-death (Bd)** process a node $u$ reproduces with probability proportional to fitness and replaces a neighbour $v$ with probability $w(u,v)/\sum_{v'}w(u,v')$. In the **death-Birth (dB)** process a uniformly random node $v$ dies and is replaced by a neighbour $u$ with probability $f(u)w(u,v)/\sum_{u'}f(u')w(u',v)$. Write $\rho^{Bd}_r(G_N,v)$ and $\rho^{dB}_r(G_N,v)$ for the fixation probability of a single mutant at $v$, and $\rho_r(G_N)$ for its average over a uniformly random initial node. For the complete graph $K_N$,

$$\rho_r^{Bd}(K_N)=\frac{1-1/r}{1-1/r^N},\qquad \rho_r^{dB}(K_N)=\frac{N-1}{N}\cdot\frac{1-1/r}{1-1/r^{N-1}},$$

and $G_N$ is a **Bd$_r$-amplifier** (resp. **dB$_r$-amplifier**) if $\rho_r^{Bd}(G_N)>\rho_r^{Bd}(K_N)$ (resp. $\rho_r^{dB}(G_N)>\rho_r^{dB}(K_N)$).

**Theorem 1 (neutral trade-off).** For every graph $G_N$ and node $v$, either $\rho_1^{Bd}(G_N,v)<\rho_1^{Bd}(K_N)$, or $\rho_1^{dB}(G_N,v)<\rho_1^{dB}(K_N)$, or both equal their complete-graph values. The statement fails for initial mutant sets of size $k\ge 2$.

**Theorem 2 (first-step trade-off).** Let $\gamma_r^{Bd}(G_N,u)$ be the probability that the first event changing the number of mutants is a reproduction of the initial mutant at $u$ rather than its replacement, and $\gamma_r^{dB}$ analogously. For every $G_N$, $u$ and $r\ge 1$, either $\gamma_r^{Bd}(G_N,u)<\gamma_r^{Bd}(K_N)$, or $\gamma_r^{dB}(G_N,u)<\gamma_r^{dB}(K_N)$, or both equalities hold.

**Theorem 3 (joint amplifier).** For every large enough $N$ there is a weighted graph $A_N$ with $\rho_r^{Bd}(A_N)>\rho_r^{Bd}(K_N)$ and $\rho_r^{dB}(A_N)>\rho_r^{dB}(K_N)$ for all $r\in(1,1.2)$.

## Proof depends on

- [Jensen's inequality](../../../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

For $r=1$ on an undirected graph with weighted degrees $d_u$, the known neutral formulas are $\rho_1^{Bd}(G_N,v)=d_v^{-1}/\sum_u d_u^{-1}$ and $\rho_1^{dB}(G_N,v)=d_v/\sum_u d_u$, both equal to $1/N$ on $K_N$. Their product is $1/\bigl(\sum_u d_u^{-1}\sum_u d_u\bigr)\le 1/N^2$ by the Cauchy–Schwarz inequality, so they cannot both exceed $1/N$, with equality only when the degrees are all equal. Theorem 2 uses the **temperature** $T(u)=\sum_{v:(v,u)\in E}w(v,u)/\deg(v)$, the rate at which $u$ is replaced under neutral Bd: above-average temperature lowers $\gamma^{Bd}$, and below-average temperature lowers $\gamma^{dB}$ by Jensen's inequality for a concave function. The amplifier $A_N$ joins a strong Bd-amplifier chunk (a fan-like hub with two-node blades) to a Fan graph (a strong dB-amplifier) by one edge of tiny weight. The chunks then resolve to homogeneous states between rare cross-chunk events; a mutant arising in the chunk that favours the current update rule fixes there with enhanced probability and later invades the other chunk, which gains more than is lost when it arises in the unfavourable chunk. For $N=1001$ with $(a,b,f)=(30,85,801)$ numerics give Bd amplification for $r\in(1,1.09)$ and dB amplification for $r\in(1,1.2)$, with ratios above $1.44$ and $1.14$ at $r=1.05$.

## Sources

- J. Svoboda, S. Joshi, J. Tkadlec, K. Chatterjee, "Amplifiers of selection for the Moran process with both Birth-death and death-Birth updating", PLOS Computational Biology 20(3) (2024) e1012008, <https://doi.org/10.1371/journal.pcbi.1012008>, PMCID PMC11006194. Eq. (1), Theorems 1–3 and Fig. 3.
