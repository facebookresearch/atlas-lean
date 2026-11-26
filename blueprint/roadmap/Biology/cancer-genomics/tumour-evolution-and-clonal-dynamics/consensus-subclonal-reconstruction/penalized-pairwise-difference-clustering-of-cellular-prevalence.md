# Penalized pairwise-difference clustering of cellular prevalence

For single-nucleotide variants $i = 1, \dots, N$ with variant read count $r_i$ out of $n_i$ reads, tumour purity $\rho \in (0,1]$ and clonal total copy number $C_i$, estimate the multiplicity

$$m_i = \Big[\frac{r_i}{n_i}\, \frac{\rho C_i + 2(1 - \rho)}{\rho}\Big]_0, \qquad [x]_0 = \max\{1, \operatorname{round}(x)\},$$

and model $r_i \sim \mathrm{Binomial}(n_i, \theta_i)$ with expected variant allele fraction

$$\theta_i = \frac{\phi_i\, m_i}{2(1 - \rho) + \rho C_i}, \qquad \phi_i = \frac{e^{\omega_i}}{1 + e^{\omega_i}},$$

where $\phi_i \in (0,1)$ is the cellular prevalence. CliP estimates $\omega = (\omega_1, \dots, \omega_N)$ by the penalized problem

$$\hat\omega = \arg\min_{\omega} \; \frac12 \sum_{i=1}^{N} \frac{n_i (\theta_i - \hat\theta_i)^2}{\theta_i (1 - \theta_i)} + \sum_{1 \le i < j \le N} p_\lambda\big(\lvert \omega_i - \omega_j \rvert\big),$$

with $\hat\theta_i = r_i / n_i$ and a sparsity-inducing penalty $p_\lambda$ (lasso, MCP or SCAD). Variants with equal fitted $\hat\omega_i$ form a cluster (a subclonal lineage), $\lambda$ is chosen by an information criterion or a bootstrap likelihood-ratio test, and clusters holding fewer than $1\%$ of variants are merged into the nearest larger cluster.

## Depends on

- [Maximum-likelihood cancer cell fraction](../../cancer-cell-fraction-estimation/ccf-mle.md)

## Expansion

The quadratic term is the Gaussian (Wald) approximation to the binomial negative log-likelihood, since $\operatorname{Var}(\hat\theta_i) = \theta_i(1 - \theta_i)/n_i$. Penalizing all pairwise differences of the logit prevalences fuses variants with similar prevalence, so the number of clusters is an output of the fit rather than an input, as in convex clustering; the logit transform keeps $\phi_i$ in $(0,1)$. The problem is solved by the alternating direction method of multipliers along a path of $\lambda$ values. If the clonal cluster is assumed to have prevalence $1$, purity can be re-estimated as the largest fitted $\phi_i$ and the fit iterated until the purity estimate stabilizes.

## Sources

- S. C. Dentro, I. Leshchiner, K. Haase et al., "Characterizing genetic intra-tumor heterogeneity across 2,658 human cancer genomes", Cell 184 (2021), <https://doi.org/10.1016/j.cell.2021.03.009> (PMC8054914). STAR Methods, subclonal architecture methods and consensus approaches.
