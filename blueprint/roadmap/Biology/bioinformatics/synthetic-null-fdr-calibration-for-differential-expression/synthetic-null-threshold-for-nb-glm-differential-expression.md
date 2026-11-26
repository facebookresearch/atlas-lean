# Synthetic-null threshold for NB-GLM differential expression

**Model.** Let $\mathbf{Y} = [Y_{ij}] \in \mathbb{N}^{n \times p}$ be an RNA-seq count matrix ($n$ samples, $p$ genes). With condition indicators $\mathbf{x}_i \in \{0,1\}^{K-1}$ and covariates $\mathbf{z}_i \in \mathbb{R}^d$, the negative binomial generalized linear model (NB-GLM) used by DESeq2 and edgeR is

$$Y_{ij} \overset{\mathrm{ind}}{\sim} \mathrm{NB}(\mu_{ij}, \phi_j), \qquad \log \mu_{ij} = \log s_i + \alpha_j + \mathbf{x}_i^\top \boldsymbol{\beta}_j + \mathbf{z}_i^\top \boldsymbol{\gamma}_j,$$

with size factors $s_i > 0$ and dispersions $\phi_j > 0$. Gene $j$ is null (not differentially expressed) if $\boldsymbol{\beta}_j = \mathbf{0}$; write $\mathcal{S}_0$, $\mathcal{S}_1$ for the null and non-null genes and $s = \#\mathcal{S}_1$.

**Synthetic null data.** From the fit to the observed data, draw $\widetilde{Y}_{ij} \overset{\mathrm{ind}}{\sim} \mathrm{NB}(\mu^0_{ij}, \hat\phi_j)$ with $\mu^0_{ij} = \exp(\log \hat s_i + \hat\alpha_j + \mathbf{z}_i^\top \hat{\boldsymbol{\gamma}}_j)$, i.e. the fitted model with every condition effect set to zero. Compute the same per-gene statistic on both data sets, $\widehat{T}_j$ (observed) and $\widetilde{T}_j$ (synthetic null), and estimate the false discovery proportion at threshold $t$ by

$$\widehat{\mathrm{FDP}}(t) = \frac{\#\{j : |\widetilde{T}_j| \ge t\}}{\max\{\#\{j : |\widehat{T}_j| \ge t\}, 1\}}, \qquad \tau_q = \min\{t > 0 : \widehat{\mathrm{FDP}}(t) \le q\},$$

declaring $\widehat{\mathcal{S}}(\tau_q) = \{j : |\widehat{T}_j| \ge \tau_q\}$ differentially expressed.

**Theorem (asymptotic FDR control and power).** Take two conditions ($K = 2$) and Wald statistics $\widehat{T}_j = |\hat\beta_j|/\mathrm{se}(\hat\beta_j)$, $\widetilde{T}_j = |\tilde\beta_j|/\mathrm{se}(\tilde\beta_j)$. Assume:
1. *(Estimation accuracy)* there are constants $L > l > 0$ with $l \le \mathrm{se}(\hat\beta_j), \mathrm{se}(\tilde\beta_j) \le L$ for all $j$ with probability at least $1 - p^{-1}$, and a deterministic $\gamma_{n,p} = O(\log p/\sqrt{n})$, $\gamma_{n,p} \to 0$, with $\max_j |\hat\beta_j - \beta_j| \le \gamma_{n,p}$ and $\max_j |\tilde\beta_j| \le \gamma_{n,p}$, each with probability at least $1 - p^{-2}$;
2. *(Beta-min)* $\min_{j \in \mathcal{S}_1} |\beta_j| \ge 2 L l^{-1} \gamma_{n,p}$;
3. *(Independence)* the statistics $\widehat{T}_1, \dots, \widehat{T}_p$ are independent;

and $\log p/\sqrt{s} \to 0$. Then for every $q \in (0,1)$, with constants $c_1, c_2 > 0$,

$$\mathrm{FDR}(\tau_q) = \mathbb{E}\left[\frac{\#(\widehat{\mathcal{S}}(\tau_q) \cap \mathcal{S}_0)}{\max\{\#\widehat{\mathcal{S}}(\tau_q), 1\}}\right] \le q\left(1 + \frac{c_1 \log p}{\sqrt{s}} + c_2 \gamma_{n,p}\right),$$

and the power $\mathbb{E}[\#(\widehat{\mathcal{S}}(\tau_q) \cap \mathcal{S}_1)/s]$ is at least $1 - 2/p$ (the source states it as $1 - 2/p$). For NB-GLM maximum likelihood estimates under a well-behaved two-group design and fixed nuisance parameters, assumption 1 holds with $\gamma_{n,p} = C_0\sqrt{\log p/n}$ whenever $n \gg \log p$, so the FDR is asymptotically at most $q$ and the power tends to $1$.

## Expansion

The synthetic statistics $\widetilde{T}_j$ are all drawn from the fitted null, so for any $t$ their exceedance count estimates the number of null genes among the observed exceedances; this is a knockoff-free analogue of a target–decoy threshold. Assumption 1 makes the null exceedance counts of the observed and synthetic data agree up to a factor $1 + O(\gamma_{n,p})$, a Chernoff bound on sums of independent indicators makes the ratio concentrate up to $O(\log p/\sqrt{s})$, and beta-min places every non-null statistic above $\tau_q$ with probability $1 - O(p^{-1})$. With few replicates the $\gamma_{n,p}$ term dominates, which is why the source recommends the conservative target $q/(1 + \sqrt{\log p/n})$.

## Sources

- Chenxin Jiang, Changhu Wang, Jingyi Jessica Li, "Nullstrap-DE: A General Framework for Calibrating FDR and Preserving Power in DE Methods, with Applications to DESeq2 and edgeR", arXiv:2507.20598 (2025): Methods (NB-GLM, synthetic null data definition, Algorithm 1); Supplementary Section S1.1 (Assumptions 1–3, Theorem 1, and the corollary on NB-GLM maximum likelihood guarantees). <https://doi.org/10.48550/arXiv.2507.20598>
