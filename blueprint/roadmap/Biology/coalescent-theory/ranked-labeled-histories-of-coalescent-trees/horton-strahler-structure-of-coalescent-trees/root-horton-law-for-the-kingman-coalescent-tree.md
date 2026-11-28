# Root-Horton law for the Kingman coalescent tree

**Setting.** Let $T^{(N)}_{\mathrm K}$ be the binary tree recording the merger history of Kingman's $N$-coalescent (every pair of clusters merges at rate $1/N$; leaves are the $N$ initial particles, the root is the last merger). Let $N_j = N^{(N)}_j$ be the number of branches of Horton–Strahler order $j$ in $T^{(N)}_{\mathrm K}$.

**Theorem (Theorem 23).**
1. For each $j \ge 1$, $N_j/N \to \mathcal N_j$ in probability as $N \to \infty$, with $\mathcal N_j$ finite. Moreover

$$\mathcal N_j = \frac12 \int_0^\infty g_j(x)^2\,dx, \qquad g'_{j+1} - \frac{g_j^2}{2} + g_j\,g_{j+1} = 0, \quad g_1(x) = \frac{2}{x+2}, \quad g_j(0) = 0 \ (j \ge 2).$$

2. The asymptotic Horton ratios satisfy the root-Horton law

$$\lim_{j\to\infty} \mathcal N_j^{-1/j} = R, \qquad 2 \le R \le 4.$$

Numerically $R = 3.0438279\ldots$, below the value $R = 4$ of the critical binary Galton–Watson tree. Furthermore (Theorem 21), the combinatorial shape of $T^{(N)}_{\mathrm K}$ has the same law as the shape of the level-set tree of the extended white noise $\tilde W^{(N)}$ (Example 15: $2N-1$ values with $N$ local maxima, built from a white noise $W^{(N)}_1,\dots,W^{(N)}_{N-1}$ of length $N-1$); equivalently, one Horton pruning of $\mathrm{shape}(T^{(N)}_{\mathrm K})$ has the law of the level-set tree of a discrete white noise of length $N-1$ ((183)). So the white-noise tree obeys the same root-Horton law (Corollary 17).

## Depends on

- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)

## Expansion

In the hydrodynamic limit, the fraction of clusters carrying a branch of order $k$ obeys a Smoluchowski-type system: two clusters of equal order $k$ merge into order $k+1$, while unequal orders keep the larger one. T. Kurtz's limit theorem for density-dependent population processes gives the law of large numbers, and a change of variables turns the system into the quasilinear Riccati chain for $g_j$ above, with $g_1$ the total cluster density $2/(x+2)$. The bounds $2 \le \mathcal N_j/\mathcal N_{j+1} \le 4$ follow from integral identities of this chain such as $\frac12\int g_k^2 = \int g_k g_{k+1}$ (Proposition 16). The theorem identifies the coalescent genealogy of a large neutral sample as a self-similar branching structure in the Horton sense, with a Horton exponent different from that of critical branching trees.

## Sources

- Yevgeniy Kovchegov and Ilya Zaliapin, "Random self-similar trees: A mathematical theory of Horton laws", *Probab. Surv.* 17 (2020), 1-213. <https://doi.org/10.1214/19-PS331>
- Preprint version (the locators in this item follow its numbering): Yevgeniy Kovchegov and Ilya Zaliapin, "Random self-similar trees: A mathematical theory of Horton laws", arXiv:1905.02629 (2019), section "Kingman's coalescent process", Theorems 21 and 23, Corollary 17, Proposition 16, <https://doi.org/10.48550/arXiv.1905.02629>.
