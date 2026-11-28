# Deterministic approximation of posteriors (DAP) for multi-SNP association

Let $y = \mu\mathbf 1 + \sum_{i=1}^p \beta_i g_i + e$, $e \sim N(0,\sigma^2 I)$, at a locus of $p$ SNPs, with association indicators $\gamma_i = \mathbf 1\{\beta_i \ne 0\}$ having independent logistic priors $\log\frac{\Pr(\gamma_i=1)}{\Pr(\gamma_i=0)} = \alpha_0 + \sum_{k=1}^q \alpha_k d_{ik}$ in SNP annotations $d_{ik}$. For a configuration $\boldsymbol\gamma$ let $\mathrm{BF}(\boldsymbol\gamma) = P(y\mid G, \boldsymbol\gamma)/P(y \mid G, \boldsymbol\gamma \equiv 0)$. The posterior is

$$\Pr(\boldsymbol\gamma \mid y, G, \boldsymbol\alpha) = \frac{\Pr(\boldsymbol\gamma\mid\boldsymbol\alpha)\,\mathrm{BF}(\boldsymbol\gamma)}{C}, \qquad C = \sum_{\boldsymbol\gamma'}\Pr(\boldsymbol\gamma'\mid\boldsymbol\alpha)\,\mathrm{BF}(\boldsymbol\gamma'),$$

and the posterior inclusion probability of SNP $i$ is its marginal. Write $C_s$ for the part of $C$ from configurations of size $\|\boldsymbol\gamma\| = s$ and $\omega = \frac1p\sum_{i=1}^p \exp(\alpha_0 + \sum_k \alpha_k d_{ik})$ for the average prior odds.

**Combinatorial bounds (Appendix B).** Suppose exactly $K$ SNPs are detectably associated and that adding a non-associated SNP to a model does not, on average, increase its Bayes factor. Approximating the prior-odds ratio between consecutive model sizes by $\omega$, for $s \ge K$,

$$\frac{p-s-K}{s+1}\,\omega\, C_s \;\lesssim\; C_{s+1} \;\lesssim\; \frac{p-s}{s-K+1}\,\omega\, C_s,$$

and DAP uses the $K$-free interpolant $C_{s+1} \approx \frac{p-s}{s+1}\,\omega\,C_s$.

**Algorithm (adaptive DAP).** Explore the null and all single-SNP models exactly, so $C^*_0 = C_0$ and $C^*_1 = C_1$. For $s = 1, 2, 3,\dots$, take the best model $\boldsymbol\gamma^*$ of size $s-1$ (for $s = 1$ this is the null model, so the first screen is a marginal one), compute for every SNP $i \notin \boldsymbol\gamma^*$ the conditional probability $\mathrm{PIP}^*_i = \mathrm{BF}(\boldsymbol\gamma^*\cup\{i\}) / \sum_j \mathrm{BF}(\boldsymbol\gamma^*\cup\{j\})$, and add SNPs with $\mathrm{PIP}^*_i \ge \lambda$ to a cumulative priority set; for $s \ge 2$, enumerate all size-$s$ subsets of the priority set to get $C^*_s$, recording the best size-$s$ model as the next $\boldsymbol\gamma^*$. Stop at the first $t$ with $C^*_t \le (p-t+1)\,\omega\, C^*_{t-1}$ (optionally also requiring $\log_{10}(S_t/S_{t-1}) < \kappa$ for the partial sums $S_k = \sum_{i \le k} C^*_i$), and approximate

$$C \approx C^* = \sum_{\boldsymbol\gamma \in \Omega}\Pr(\boldsymbol\gamma\mid\boldsymbol\alpha)\,\mathrm{BF}(\boldsymbol\gamma) + \epsilon, \qquad \epsilon = \sum_{s=t+1}^{p} R^*_s,\quad R^*_t = C^*_t,\quad R^*_{s+1} = \frac{p-s}{s+1}\,\omega\,R^*_s,$$

with $\Omega$ the explicitly explored models. As $\lambda, \kappa \to 0$ the procedure enumerates every model and is exact.

## Remarks

Among size-$s$ models, those containing $m$ of the $K$ true signals number $\binom{p-K}{s-m}\binom{K}{m}$; under saturation each class contributes about its count times an average prior times an average Bayes factor $\overline{\mathrm{BF}}_{\{m\}}$ that does not depend on $s$. Passing from $s$ to $s+1$ multiplies the count by $\frac{p-K-(s-m)}{s+1-m}$, which lies between $\frac{p-s-K}{s+1}$ and $\frac{p-s}{s+1-K}$, and multiplies the prior by about $\omega$; summing over $m$ gives the bounds. The conditional screen $\mathrm{PIP}^*$ is a Bayesian stepwise conditional analysis that accounts for LD, and any SNP whose conditional probabilities stay below $\lambda$ at every size has overall PIP below $\lambda$. The annotation coefficients $\boldsymbol\alpha$ are estimated by an EM algorithm whose E-step computes PIPs (with the single-signal variant DAP-1) and whose M-step is a logistic regression of PIPs on annotations.

## Depends on

- [Posterior inclusion probability](pip.md)

## Sources

- X. Wen, Y. Lee, F. Luca and R. Pique-Regi, "Efficient integrative multi-SNP association analysis via deterministic approximation of posteriors", American Journal of Human Genetics 98 (2016), 1114–1129, Equations 1–6 and Appendices A (Equation A1), B (Equations B1–B5) and D (Equations D1–D4), <https://doi.org/10.1016/j.ajhg.2016.03.029> (PMC4908152).
