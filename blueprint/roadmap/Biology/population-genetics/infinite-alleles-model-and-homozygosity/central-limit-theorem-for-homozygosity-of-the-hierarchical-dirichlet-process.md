# Central limit theorem for the homozygosity of the hierarchical Dirichlet process

**Setting.** For a type-frequency vector $\mathbf x = (x_1, x_2, \dots)$ in the infinite simplex, the $m$th order homozygosity $\varphi_m(\mathbf x) = \sum_i x_i^m$ ($m \ge 2$) is the probability that $m$ individuals sampled from the population all carry the same allele. Let $\mathbf V = (V_1, V_2, \dots)$ be GEM($\alpha$) stick-breaking weights (i.i.d. $U_k \sim \mathrm{Beta}(1, \alpha)$, $V_n = U_n\prod_{k<n}(1 - U_k)$), so their ranked version is Poisson–Dirichlet($\alpha$). Given $\mathbf V$, let $W_n \sim \mathrm{Beta}\bigl(\beta V_n, \beta(1 - \sum_{k \le n} V_k)\bigr)$ independently and $Z_n = W_n\prod_{k<n}(1 - W_k)$. Then $\sum_n Z_n\delta_{\xi_n}$ is the hierarchical Dirichlet process (HDP): a Dirichlet process with concentration $\beta$ whose base measure is itself a Dirichlet process with concentration $\alpha$. Write $H_m(\alpha, \beta) = \varphi_m(\mathbf Z)$ and let ${m \brack j}$ be unsigned Stirling numbers of the first kind.

**Theorem.** As $\alpha, \beta \to \infty$ with $\alpha/\beta \to c \in (0, \infty)$,

$$\sqrt\beta\;\frac{H_m(\alpha, \beta) - \beta^{1-m}\sum_{j=1}^m {m \brack j}\,\Gamma(j)\,(\alpha/\beta)^{1-j}}{\beta^{1-m}\sum_{j=1}^m {m \brack j}\,\Gamma(j)\, c^{1-j}} \xrightarrow{D} N(0, \sigma_c^2),$$

with

$$\sigma_c^2 = \frac{\sum_{j=1}^{2m} {2m \brack j}\Gamma(j)c^{1-j} - \sum_{1 \le i, j \le m} {m \brack i}{m \brack j}\Gamma(i+1)\Gamma(j+1)c^{1-i-j}}{\left(\sum_{j=1}^m {m \brack j}\Gamma(j)c^{1-j}\right)^2} - m^2.$$

In the same regime $H_m(\alpha,\beta)$ divided by its centering tends to $1$ in probability, and $\{H_m(\alpha, \beta)\}$ satisfies a large deviation principle on $[0, 1]$ with speed $\max\{\alpha, \beta\}$. Analogous CLTs hold for the finite-dimensional HDP and for the HDP with $L$ groups sharing the base measure.

## Depends on

- [Equilibrium homozygosity in the infinite-alleles model](eq-homozygosity.md)

## Expansion

Conditionally on the base weights $\mathbf V$, the second-level weights are a Dirichlet process with concentration $\beta$, so $m$-fold homozygosity is the probability that $m$ draws from a Chinese restaurant process with parameter $\beta$ seated over a base CRP with parameter $\alpha$ all land on one dish. Expanding by the number $j$ of distinct second-level tables gives the Stirling-number sums: ${m \brack j}$ counts arrangements of $m$ customers into $j$ cycles, and each group of $j$ tables then shares one base atom with probability involving $\Gamma(j)/\alpha^{j-1}$. Fluctuations come from both levels; with $\alpha/\beta \to c$ they are of the same order $\beta^{-1/2}$, and the variance combines the $2m$-fold moment with the squared $m$-fold one. For $\beta \to \infty$ alone one recovers the Joyce–Krone–Kurtz CLT for Poisson–Dirichlet homozygosity.

## Sources

- Shui Feng and J. E. Paguyo, "Central limit theorems associated with the hierarchical Dirichlet process", Stoch. Process. Appl. 190 (2025), 104767, <https://doi.org/10.1016/j.spa.2025.104767>. Numbering follows the arXiv version, arXiv:2404.16034 (2024): Theorems 1.1–1.4 and Proposition 3.3, <https://doi.org/10.48550/arXiv.2404.16034>.
