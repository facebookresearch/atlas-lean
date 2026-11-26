# Identifiability of the hierarchical cell-type mixture model for methylation

**Multiplicative confounding.** Let $O_{ji}$ be the methylation level at CpG site $j$ in sample $i$, a mixture of $K$ cell types with proportions $p_{ki} \ge 0$, $\sum_k p_{ki} = 1$. If site $j$ shifts by $\delta_{j1}$ in cell type 1 in cases ($Z_i = 1$) only, then

$$O_{ji} = \delta_{j1}\, p_{1i}\, Z_i + \sum_{k=1}^K \mu_{jk}\, p_{ki} + \epsilon_{ji},$$

so the cell proportion multiplies the phenotype effect; the coefficient $\tau_j$ of $Z_i$ in the additive model $O_{ji} = \alpha_j + \tau_j Z_i + \sum_{k<K} b_{jk}\hat p_{ki} + \epsilon_{ji}$ generally differs from $\delta_{j1}$.

**Hierarchical model.** For $n$ samples, $m$ sites and $q$ phenotypes with covariates $x_{i\ell}$, the cell-type-specific methylation of sample $i$ at site $j$ in cell type $k$ is $\mathcal{N}\big(\mu_{jk} + \sum_\ell x_{i\ell}\beta_{jk\ell},\ \sigma^2_{jk}\big)$, and the observed level is the $P_i$-weighted mixture plus noise of variance $\sigma^2_{\epsilon j}$. Integrating out the cell-type-specific levels gives the likelihood

$$L(\Theta \mid O) = \prod_{i=1}^n\prod_{j=1}^m \mathcal{N}\Big(O_{ji};\ P_i^{\mathsf T}\mu_j + \sum_{\ell=1}^q x_{i\ell}\, P_i^{\mathsf T} B_\ell(j),\ \sum_{k=1}^K \sigma^2_{jk} P_{ik}^2 + \sigma^2_{\epsilon j}\Big),$$

with parameters $\Theta = \{P_i, \mu_j, B_\ell(j), \sigma^2_{jk}, \sigma^2_{\epsilon j}\}$, where $P_i$ is the composition vector of sample $i$, $\mu_j$ the baseline methylation vector and $B_\ell(j) = (\beta_{j1\ell},\dots,\beta_{jK\ell})$ the cell-type-specific effects of phenotype $\ell$. Write $P = (P_1,\dots,P_n)$ ($K \times n$), $J_1 = \mathbf{1}_n\mathbf{1}_K^{\mathsf T}$, $J_{x_\ell} = x_\ell \mathbf{1}_K^{\mathsf T}$ and $\odot$ for the entrywise product.

**Theorem (identifiability).** Suppose (a) for each cell type $k$ there is a CpG site $r_k$ with $B_\ell(r_k) = 0$ for all phenotypes $\ell$, $\mu_{r_k k} = 1$ and $\mu_{r_k k'} = 0$ for $k' \ne k$; and (b)

$$\operatorname{rank}\big(J_1 \odot P^{\mathsf T},\ J_{x_1}\odot P^{\mathsf T},\ \dots,\ J_{x_q}\odot P^{\mathsf T}\big) = (q+1)K \quad\text{and}\quad \operatorname{rank}\big((\mathbf{1}_n, P^{\mathsf T}) \odot (\mathbf{1}_n, P^{\mathsf T})\big) = K + 1.$$

Then the model is identifiable: $L(\Theta \mid O) = L(\tilde\Theta \mid O)$ for all $O$ implies $\Theta = \tilde\Theta$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Equality of the likelihoods for all data forces equality of every marginal normal law of $O_{ji}$, hence of its mean and variance for every $(i,j)$. At an anchor site $r_k$ the mean is exactly $p_{ki}$, so condition (a) pins down every composition vector $P_i$; this removes the rotation ambiguity that makes plain non-negative matrix factorization $O = \mu P$ non-identifiable (with constant compositions, $u_1 p_1 + u_2 p_2$ can be rewritten as $(u_1 + p_2 C)p_1 + (u_2 - p_1 C)p_2$). With $P$ known, the means at each site are linear in $(\mu_j, B_1(j),\dots,B_q(j))$ through the design matrix in the first rank condition, and the variances are linear in $(\sigma^2_{\epsilon j}, \sigma^2_{j1},\dots,\sigma^2_{jK})$ through the squared-composition matrix in the second, so full column rank makes both solutions unique. The second condition formalizes the requirement that cellular compositions vary enough across samples.

## Sources

- X. Luo, C. Yang, Y. Wei, "Detection of cell-type-specific risk-CpG sites in epigenome-wide association studies", Nature Communications 10 (2019) 3113, Methods (Eqs. (3)–(4), model likelihood, Theorem 1 and its proof), <https://doi.org/10.1038/s41467-019-10864-z>, PMCID PMC6629651.
