# Moment duality of the multitype Λ-Wright–Fisher process

**Multitype Λ-coalescent.** Fix $d$ types, rates $\rho = (\rho_{ij}) \in \mathbb{R}_+^{d\times d}$ and measures $\mathcal{Q}_1, \dots, \mathcal{Q}_d$ on $[0,1]^d\setminus\{0\}$ with $\int\sum_j u_j^{1+\delta_{ij}}\,\mathcal{Q}_i(du) < \infty$. When there are $b = (b_1,\dots,b_d)$ blocks by type, a merger of $k \le b$ blocks into one block of type $i$ occurs at rate
$$\lambda_{b,k}^i = \rho_{ii}1_{\{k = 2e_i\}} + \sum_{j\ne i}\rho_{ij}1_{\{k = e_j\}} + \int u^k(1-u)^{b-k}\,\mathcal{Q}_i(du), \qquad u^k(1-u)^{b-k} = \prod_j u_j^{k_j}(1-u_j)^{b_j - k_j};$$
$\rho_{ij}$ ($i \ne j$) is a type switch (migration), $\rho_{ii}$ binary merging, $\mathcal{Q}_i$ multiple mergers possibly across types. Multitype Kingman ($\mathcal{Q} \equiv 0$), seed-bank and Beta-type coalescents are special cases.

**Theorem 2.5.** The $d$-dimensional SDE
$$d\mathsf{R}_i = \sum_{j\ne i}\Big(\rho_{ji} - \int u_i\,\mathcal{Q}_j(du)\Big)(\mathsf{R}_j - \mathsf{R}_i)\,dt + \sqrt{\rho_{ii}\mathsf{R}_i(1 - \mathsf{R}_i)}\,dB_i + \sum_{j=1}^d\int\!\!\int_0^1 u_i\big(1_{\{v\le \mathsf{R}_j(t-)\}} - \mathsf{R}_i(t-)\big)\,\widetilde{\mathcal{N}}_j(dt,du,dv),$$
with independent Brownian motions $B_i$ and compensated Poisson measures of intensity $dt\,\mathcal{Q}_j(du)\,dv$, has a unique strong solution on $[0,1]^d$ (the **multitype Λ-Wright–Fisher process**). It is Feller with generator
$$\mathcal{A}f(r) = \sum_i\sum_{j\ne i}\rho_{ji}(r_j - r_i)\partial_i f + \sum_i\frac{\rho_{ii}}{2}r_i(1-r_i)\partial_{ii}f + \sum_k\int\big(r_k f(r + (1-r)\odot u) + (1-r_k) f(r - r\odot u) - f(r)\big)\mathcal{Q}_k(du).$$

**Theorem 2.6.** For all $r \in [0,1]^d$, $n \in \mathbb{N}_0^d$, $t \ge 0$,
$$\mathbb{E}_r\Big[\prod_i \mathsf{R}_i(t)^{n_i}\Big] = \mathbb{E}_n\Big[\prod_i r_i^{N_i(t)}\Big],$$
where $N$ is the block-counting process of the multitype Λ-coalescent: from $n$ it jumps to $n - 2e_i + e_i$ at rate $\binom{n_i}{2}\big(\rho_{ii} + \int u^{2e_i}(1-u)^{n-2e_i}\mathcal{Q}_i(du)\big)$, to $n - e_j + e_i$ at rate $n_j\big(\rho_{ij} + \int u^{e_j}(1-u)^{n-e_j}\mathcal{Q}_i(du)\big)$, and to $n - k + e_i$ at rate $\binom{n}{k}\int u^k(1-u)^{n-k}\mathcal{Q}_i(du)$ for the remaining $k$.

With $\mathcal{Q} \equiv 0$ this is the duality between Shiga's neutral stepping-stone model and the structured Kingman coalescent.

## Depends on

- [Generator of the Λ-coalescent block-counting process](../coalescents/block-counting-generator.md)

## Expansion

Known existence and uniqueness results do not apply directly to this multidimensional SDE with square-root diffusion and state-dependent jumps, so the paper proves strong existence and pathwise uniqueness directly (appendix). Duality follows by applying $\mathcal{A}$ to $f(r) = r^n$: migration terms produce $n_j\rho_{ij}(r^{n - e_j + e_i} - r^n)$, the Wright–Fisher term gives $\binom{n_i}{2}\rho_{ii}(r^{n - e_i} - r^n)$, and expanding $r_k(r + (1-r)\odot u)^n + (1-r_k)(r - r\odot u)^n$ binomially reproduces the multiple-merger rates; this equals the coalescent generator acting on $n \mapsto r^n$, and the standard generator criterion gives the duality.

## Sources

- A. González Casanova, N. Kurt, I. Nuñez, J. L. Pérez, "From multitype branching to multitype coalescents and back: Genealogies, duality and examples", arXiv:2501.00329 (2025), Definition 2.1, Theorems 2.5, 2.6, 3.1 and 3.2, and the multitype Beta coalescents of Section 3, <https://doi.org/10.48550/arXiv.2501.00329>.
