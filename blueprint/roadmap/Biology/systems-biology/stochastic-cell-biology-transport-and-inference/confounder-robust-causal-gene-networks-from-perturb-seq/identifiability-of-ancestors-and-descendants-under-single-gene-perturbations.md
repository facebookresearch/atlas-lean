# Identifiability of ancestors and descendants under single-gene perturbations

**Perturb-seq measurement and structural model.** In cell $i$ with sequencing depth $\ell_i$, the UMI count of gene $j$ is $Y_{ij} \mid \lambda_{ij} \sim \mathrm{Poisson}(\ell_i\lambda_{ij})$, with $\lambda_{ij}$ a point mass or a Gamma variable around the true expression $\mu_{ij}$ (Poisson or negative-binomial observations). Each cell receives at most one CRISPR guide: $D_{ij} \in \{0,1\}$ with $\sum_j D_{ij} \le 1$. True expression follows a log-linear structural equation model on a directed acyclic graph $G$:

$$\log\mu_{ij} = \theta_{j0} + \sum_{k \in \mathrm{pa}(j)}\theta_{jk}\log\mu_{ik} + \tau_jD_{ij} + \beta_j^\top X_i + \gamma_j^\top U_i + \epsilon_{ij},$$

with observed covariates $X_i$, unobserved confounders $U_i$ (enhancer accessibility, hidden subtypes, unmeasured genes), i.i.d. mean-zero noise $\epsilon_{ij}$, and the assignment condition $D_{ij} \perp U_i \mid \ell_i, X_i$.

**Assumption 1 (non-degenerate direct effects).** $\theta_{jk} \neq 0$ for every $k \in \mathrm{pa}(j)$, and $\tau_j \neq 0$ for every gene $j$.

**Theorem 1.** Under Assumption 1 and the measurement model with an intervention on every node, the descendant set $\mathrm{des}(j)$ and the ancestor set $\mathrm{anc}(j)$ of every gene $j$ are identifiable.

## Expansion

Assumption 1 replaces faithfulness: only direct edge effects and guide effects must be nonzero, while cancellations along multiple paths are allowed. The argument uses an *exclusive directed path* (a unique directed path between two nodes within a suitable subgraph), shows such a path exists between any ancestor–descendant pair, and shows that along it the effect of perturbing $j$ on gene $k$ cannot cancel, so $k \in \mathrm{des}(j)$ exactly when perturbing $j$ shifts the distribution of $Y_k$. Since guides are independent of $U$ given $(\ell,X)$, these comparisons are unconfounded even though the network edges are not. Ancestor sets then give a causal ordering, from which the DAG is assembled once parent sets are found.

## Sources

- Kwangmoon Park, Hongzhe Li, "Confounder-robust causal discovery and inference in Perturb-seq using proxy and instrumental variables", Journal of the American Statistical Association (2026), 1–44, <https://doi.org/10.1080/01621459.2026.2749694>. Published version of arXiv:2601.01830, cited next; locators there refer to the arXiv version.
- Kwangmoon Park and Hongzhe Li, *Confounder-robust causal discovery and inference in Perturb-seq using proxy and instrumental variables*, arXiv:2601.01830 (2026). <https://doi.org/10.48550/arXiv.2601.01830> Sections 2.2–2.3 (measurement model and structural equation model), Section 3 (Assumption 1 and Theorem 1).
