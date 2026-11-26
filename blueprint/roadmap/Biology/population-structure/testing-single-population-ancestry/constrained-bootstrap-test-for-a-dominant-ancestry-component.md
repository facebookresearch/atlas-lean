# Constrained parametric bootstrap test for a dominant ancestry component in the admixture model

**Supervised admixture model.** A diploid individual is typed at $M$ markers in linkage equilibrium; marker $m$ has $I_m$ alleles, and the allele frequencies $p_{kim}$ in each of $K \ge 2$ ancestral populations are known. With admixture vector $q' = (q_1, \dots, q_{K-1}, 1 - \sum_{k<K} q_k)$ in the simplex, the allele counts at marker $m$ are independent,

$$ X_m \sim \mathrm{Multi}\bigl( 2, (\langle q', p_{\cdot i m} \rangle)_{i = 1, \dots, I_m} \bigr), \qquad \ell(q \mid X) = \frac{1}{M} \sum_{m=1}^{M} \Bigl( \log \frac{2}{\prod_i X_{im}!} + \sum_{i} X_{im} \log \langle q', p_{\cdot i m} \rangle \Bigr), $$

and $\hat q$ is the maximum likelihood estimator over $\Theta = \{ q \in [\varepsilon_q, 1 - \varepsilon_q]^{K-1} : \varepsilon_q \le \sum_k q_k \le 1 - \varepsilon_q \}$.

**Hypotheses.** With the dominant component $d_\infty = \max_k q'_k$ and a dominance threshold $\varepsilon_\infty \in (\tfrac12, 1 - (K-1)\varepsilon_q)$ (for example $0.75$, the expected contribution of three grandparents from one population),

$$ H_0 : d_\infty \le \varepsilon_\infty \quad \text{versus} \quad H_1 : d_\infty > \varepsilon_\infty, $$

so rejecting $H_0$ declares a dominant single-population ancestry while controlling the rate of false declarations.

**Test.** Compute $\hat d_\infty = \max_k \hat q'_k$. Let $\hat{\hat q} = \hat q$ if $\hat d_\infty \le \varepsilon_\infty$, and otherwise the constrained maximizer of $\ell$ subject to $\max_k q'_k = \varepsilon_\infty$. Draw $B$ bootstrap samples from the admixture model with parameter $\hat{\hat q}$, recompute $\hat d^*_\infty$ on each, and reject $H_0$ when $\hat d_\infty$ exceeds the empirical $(1-\alpha)$-quantile $\xi^*_{1-\alpha}$ of the bootstrap statistics.

**Theorem 1.** Assume (A1) the parameter space $\Theta$ above; (A2) $p_{kim} \ge \varepsilon_p > 0$; (A3) the empirical design measures $\frac{1}{M} \sum_m \delta_{p_{\cdot\cdot m}}$ converge weakly to a design measure $\mu$; and (A4) identifiability: for every $h \ne 0$ with $h^\top \mathbf{1} = 0$, $\mu\{ \mathbf{p} : \exists i,\ h^\top \mathbf{p}_i > 0 \} > 0$. Let the true admixture $q_0$ lie in the interior of $\Theta$ and $\alpha \in (0, 0.5)$. Then as $M \to \infty$:

1. under $H_0$, $\Pr(\hat d_\infty > \xi^*_{1-\alpha}) \to 0$ if $d_\infty < \varepsilon_\infty$ and $\to \alpha$ if $d_\infty = \varepsilon_\infty$, so the test has asymptotic level $\alpha$;
2. under $H_1$, $\Pr(\hat d_\infty > \xi^*_{1-\alpha}) \to 1$, so the test is consistent.

## Expansion

The supporting lemmas show that the null-constrained estimator $\hat{\hat q}$ is consistent for $q_0$ whenever $d_\infty \le \varepsilon_\infty$, and that the bootstrap MLE is consistent conditionally on the data for any data-measurable bootstrap parameter. Assumptions (A1)-(A2) bound the log-likelihood and its derivatives uniformly, (A3) stabilizes averages over markers, and (A4) makes the limiting Kullback-Leibler contrast uniquely minimized, so $\sqrt{M}(\hat q - q_0)$ and, conditionally, $\sqrt{M}(\hat q^* - \hat{\hat q})$ are asymptotically $N(0, \Gamma^{-1}(q_0))$ with $\Gamma(q_0) = \lim_M \frac{1}{M} \sum_m \mathbb{E}_{q_0}[\dot\phi_m \dot\phi_m^\top]$. On the boundary $d_\infty = \varepsilon_\infty$ the bootstrap distribution of $\hat d^*_\infty$ mimics that of $\hat d_\infty$, giving exact asymptotic level; strictly inside $H_0$ the bootstrap is centered at a point at least as close to the boundary as the truth, so the rejection probability vanishes; under $H_1$, $\hat d_\infty \to d_\infty > \varepsilon_\infty$ while the bootstrap quantiles concentrate at $\varepsilon_\infty$.

## Sources

- Holger Dette, Carola Sophia Heinzel, Zoe Lange, Peter Pfaffelhuber, "Testing for Single-Population Ancestry in the Admixture Model", arXiv (2026). Section 2 (supervised admixture model), Section 3 (hypotheses, constrained bootstrap algorithm, assumptions (A1)-(A4), consistency lemmas, Theorem 1). <https://doi.org/10.48550/arXiv.2606.01990>
