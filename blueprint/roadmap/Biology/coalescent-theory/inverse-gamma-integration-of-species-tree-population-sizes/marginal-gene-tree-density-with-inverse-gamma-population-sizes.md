# Marginal gene-tree density with inverse-gamma population sizes

Let $S$ be a species tree with branches $b$, each carrying a constant effective population size $N_b > 0$, and let $g_1, \dots, g_L$ be dated gene trees embedded in $S$ at $L$ independent loci, locus $\ell$ having ploidy factor $\psi_\ell > 0$. Under the multispecies coalescent, while $k$ lineages of locus $\ell$ are in branch $b$, each pair coalesces at rate $1/(\psi_\ell N_b)$. For branch $b$ let $q_b$ be the total number of coalescences occurring in $b$ over all loci, and

$$\gamma_b \;=\; \sum_{\ell=1}^{L} \frac{1}{\psi_\ell} \sum_{\text{intervals } j \text{ of locus } \ell \text{ in } b} \binom{k_{\ell j}}{2}\,\delta_{\ell j},$$

where $\delta_{\ell j}$ is the length of the $j$-th inter-event interval of locus $\ell$ within $b$ and $k_{\ell j}$ the number of lineages during it. Then the coalescent density factorizes over branches as

$$p(g_1, \dots, g_L \mid S, N) \;=\; \prod_b \Bigl(\prod_{\ell}\psi_\ell^{-q_{b\ell}}\Bigr)\, N_b^{-q_b}\, e^{-\gamma_b/N_b},$$

with $q_{b\ell}$ the coalescences of locus $\ell$ in $b$. If the $N_b$ are independent with inverse-gamma prior density $p(N) = \frac{\beta^\alpha}{\Gamma(\alpha)} N^{-\alpha-1} e^{-\beta/N}$, then

$$p(g_1, \dots, g_L \mid S, \alpha, \beta) \;=\; \prod_b \Bigl(\prod_{\ell}\psi_\ell^{-q_{b\ell}}\Bigr)\, \frac{\beta^{\alpha}\,\Gamma(\alpha + q_b)}{\Gamma(\alpha)\,(\beta + \gamma_b)^{\alpha + q_b}},$$

and a posteriori $N_b \mid g, S \sim \text{Inv-Gamma}(\alpha + q_b, \beta + \gamma_b)$, independently across branches. With the default shape $\alpha = 3$ the prior mean is $\mu = \beta/(\alpha - 1) = \beta/2$, the prior standard deviation equals $\mu$, and the coefficient of variation is $1$.

## Depends on

- [MSC realization gene-tree probability](../multispecies-coalescent/msc-realization-gene-tree-probability-equals-the.md)

## Expansion

Within a branch, the coalescent with $k$ lineages and pairwise rate $\lambda$ has waiting density $\binom{k}{2}\lambda\, e^{-\binom{k}{2}\lambda\delta}$ for an interval ending in a coalescence and survival $e^{-\binom{k}{2}\lambda\delta}$ for an interval ending at the branch's upper boundary or at a sampling event. A specific pair merges with probability $1/\binom{k}{2}$, so each coalescence of a labelled tree contributes $\lambda$. Multiplying over intervals and loci with $\lambda = 1/(\psi_\ell N_b)$ gives the displayed factorization. The integral $\int_0^\infty N^{-q} e^{-\gamma/N}\, \frac{\beta^\alpha}{\Gamma(\alpha)} N^{-\alpha-1} e^{-\beta/N}\, dN$ is the normalizing constant of an $\text{Inv-Gamma}(\alpha + q, \beta + \gamma)$ density, which gives the marginal and the posterior. For $\alpha > 2$ the inverse-gamma variance is $\beta^2/((\alpha-1)^2(\alpha-2))$, which equals $\mu^2$ at $\alpha = 3$. Integrating out the sizes removes one parameter per species-tree branch from the Markov chain; together with coordinated tree operators this made inference an order of magnitude faster than its predecessor on the empirical data sets analysed.

## Sources

- H. A. Ogilvie, R. R. Bouckaert, A. J. Drummond, "StarBEAST2 brings faster species tree inference and accurate estimates of substitution rates", *Molecular Biology and Evolution* 34(8) (2017) 2101–2114, New Approaches, "Analytical Integration of Population Sizes" (Equations (1)–(2)), <https://doi.org/10.1093/molbev/msx126> (PMC5850801).
