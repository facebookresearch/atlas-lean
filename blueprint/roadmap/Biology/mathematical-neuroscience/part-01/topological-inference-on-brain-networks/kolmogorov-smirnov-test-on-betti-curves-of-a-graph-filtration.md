# Kolmogorov–Smirnov test on Betti curves of a graph filtration

Let $\mathcal X = (V, w)$ be a weighted network on $p$ nodes with distinct positive edge weights $w_{ij}$ (for brain networks, $w_{ij} = 1 - c_{ij}$ or $\sqrt{1 - c_{ij}}$ for a correlation $c_{ij}$). For $\epsilon \ge 0$ the **binary network** $\mathcal X_\epsilon$ keeps the edges with $w_{ij} > \epsilon$. With sorted weights $0 = w_{(0)} < w_{(1)} < \cdots < w_{(q)}$, $q \le (p^2 - p)/2$, the **graph filtration** is the nested sequence

$$\mathcal X_0 \supset \mathcal X_{w_{(1)}} \supset \cdots \supset \mathcal X_{w_{(q)}},$$

from the complete graph down to the bare node set. Let $\beta_0(\mathcal X_\epsilon)$ be the number of connected components and $\beta_1(\mathcal X_\epsilon)$ the number of independent cycles.

**Monotonicity.** Along the graph filtration $\beta_0$ is nondecreasing and $\beta_1$ is nonincreasing in $\epsilon$, and at each level $\beta_1 = \beta_0 - p + q_\epsilon$, where $q_\epsilon$ is the number of edges of $\mathcal X_\epsilon$ (Euler characteristic of a graph). Both curves are step functions that change only at the edge weights, so $q + 1$ levels determine them.

**KS distance.** For networks $\mathcal X^1, \mathcal X^2$ on the same nodes and $j \in \{0, 1\}$,

$$D_{KS}(\mathcal X^1, \mathcal X^2) = \sup_{\epsilon \ge 0}\big|\beta_j(\mathcal X^1_\epsilon) - \beta_j(\mathcal X^2_\epsilon)\big|,$$

which equals its discretization $D_q = \max_{1 \le i \le q}|\beta_j(\mathcal X^1_{\epsilon_i}) - \beta_j(\mathcal X^2_{\epsilon_i})|$ when the $\epsilon_i$ run through all sorted edge weights.

**Null distribution.** Under the null hypothesis of no topological difference, the law of $D_q$ is computed exactly by combinatorial lattice-path counting (the two monotone step curves interleave like two empirical distribution functions), and asymptotically

$$\lim_{q \to \infty}\mathbb P\Big(D_q / \sqrt{2q} \ge d\Big) = 2\sum_{i=1}^\infty (-1)^{i-1} e^{-2 i^2 d^2},$$

giving the asymptotic p-value $2e^{-2 d_o^2} - 2e^{-8 d_o^2} + 2e^{-18 d_o^2} - \cdots$ for the observed normalized statistic $d_o = D_q/\sqrt{2q}$; its first term is the $i = 1$ term of the series. (The prose after Eq. 4 of the source writes the first term as $2e^{-d_o^2}$, inconsistent with Eq. 4.)

## Expansion

Removing an edge either splits a component ($\beta_0$ rises by one) or breaks a cycle ($\beta_1$ falls by one), never both, which gives monotonicity and the Euler relation. Because $\beta_0$ over the filtration encodes the single-linkage dendrogram (components merge in the order of single-linkage distances), the test is invariant under any monotone reparametrization of the edge weights, such as $1 - c$ versus $\sqrt{1 - c}$. In a two-sample setting the exact law replaces permutation tests whose permutation counts are astronomically large. Applied to twin correlation matrices $C_{\mathrm{MZ}}, C_{\mathrm{DZ}}$, with Falconer's heritability index $\mathrm{HI} = 2(C_{\mathrm{MZ}} - C_{\mathrm{DZ}})$ from $\mathrm{corr}_{\mathrm{MZ}} = A + C$ and $\mathrm{corr}_{\mathrm{DZ}} = A/2 + C$, it detects that monozygotic twin networks are more connected and contain more cycles at every correlation level.

## Sources

- M. K. Chung, H. Lee, A. DiChristofano, H. Ombao, V. Solo, "Exact topological inference of the resting-state brain networks in twins", Network Neuroscience 3(3) (2019) 674–694, sections "Graph filtration" (Eq. 2), "Betti numbers", "Kolmogorov–Smirnov distance" (Eq. 4) and "Twin correlations" (Eqs. 5–6), <https://doi.org/10.1162/netn_a_00091>, PMCID PMC6663192.
