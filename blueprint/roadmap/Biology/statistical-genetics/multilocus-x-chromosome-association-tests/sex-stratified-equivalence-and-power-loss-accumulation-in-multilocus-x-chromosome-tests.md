# Sex-stratified equivalence and power-loss accumulation in multilocus X-chromosome association tests

**Setting.** For $n_f$ females and $n_m$ males with responses $Y = (Y_f, Y_m)$, a covariate matrix $X = (X_f, X_m)$ of $p$ genetic covariates (codings of $k$ X-chromosomal variants) and sex indicator $S$ ($0$ for females, $1$ for males), consider the generalised linear model with link $g$

$$\mathcal{M}:\ g(\mathbb{E}Y) = \beta_0 + \beta_S S + X\boldsymbol\beta_1 + (XS)\boldsymbol\beta_2, \qquad XS = \begin{pmatrix} 0 \\ X_m \end{pmatrix},$$

and the sex-stratified models $\mathcal{M}_f: g(\mathbb{E}Y_f) = \beta_{0,f} + X_f\boldsymbol\beta_f$ and $\mathcal{M}_m: g(\mathbb{E}Y_m) = \beta_{0,m} + X_m\boldsymbol\beta_m$. Let $P(x,d,\nu)$ be the CDF at $x$ of the noncentral $\chi^2$ distribution with $d$ degrees of freedom and noncentrality $\nu$, $\chi^2_{d,\alpha}$ its upper $\alpha$-quantile under $\nu = 0$, and $z_\alpha$ the upper $\alpha$-quantile of $N(0,1)$.

**Theorem 1 (stratified equivalence).** The Wald, score and likelihood-ratio tests of $H_0: \boldsymbol\beta_1 = \boldsymbol\beta_2 = 0$ in $\mathcal{M}$ coincide with those of $H_0: \boldsymbol\beta_f = \boldsymbol\beta_m = 0$ in the pair of sex-stratified models. Hence multilocus tests on the X chromosome (burden, SKAT-type and related tests) can be run separately in each sex and combined, and the combined test is invariant to the X-inactivation coding.

**Theorem 2 (single-variant power loss from misspecified X-inactivation).** For one additive variant with effect $\beta_A$, the 1-df statistic is noncentral $\chi^2$ with noncentrality $c_1\beta_A^2$ under the correct X-inactivation coding and $c_2\beta_A^2$ under the wrong one, $c_1 > c_2 > 0$. For any $a \in (c_2,c_1)$, choosing the level so that $z_{\alpha/2} = \sqrt{a}\,|\beta_A|$ gives

$$P(\chi^2_{1,\alpha}, 1, c_2\beta_A^2) - P(\chi^2_{1,\alpha}, 1, c_1\beta_A^2) \to 1 \qquad (|\beta_A| \to \infty),$$

so the misspecified test can lose essentially all power.

**Theorem 3 (accumulation over variants).** With $k$ variants, the classical additive test has $k$ degrees of freedom and the robust test (adding dominance and gene–sex interaction for every variant) has $3k$. If both have noncentrality $ck$ with $c > 0$ (both are $O(k)$), then for any $b \in \big(\sqrt{c-3\log(1+c/3)},\ \sqrt{c-\log(1+c)}\big)$ and $z_\alpha = b\sqrt{k}$,

$$P(\chi^2_{3k,\alpha}, 3k, ck) - P(\chi^2_{k,\alpha}, k, ck) \to 1 \qquad (k \to \infty),$$

so the robust test's power loss relative to a correctly specified additive test approaches one as the number of variants grows. The interval for $b$ is nonempty for every $c > 0$ because $(1+c/3)^3 > 1+c$.

## Depends on

- [Wald's test](../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-wald-statistic.md)
- [Rao's score test, known information](../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-score-statistic.md)
- [Wilks' theorem (simple null)](../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-two-mul-log-like.md)

## Expansion

Theorem 1 holds because $\mathcal{M}$ is a reparametrisation of fitting the two sexes separately: the columns $(\mathbf 1, S, X, XS)$ span the same space as $(\mathbf 1_f, \mathbf 1_m, X_f \oplus 0, 0 \oplus X_m)$, the likelihood factorises over sexes, and the null hypotheses correspond. Theorems 2 and 3 compare noncentral $\chi^2$ tails: a threshold placed between the two critical values makes one test reject with probability tending to one and the other with probability tending to zero. For Theorem 3, $\chi^2_{3k}(ck)/k \to 3+c$ and $\chi^2_k(ck)/k \to 1+c$ in probability, with fluctuations of order $\sqrt k$. The level satisfies $\log\alpha \sim -b^2k/2$. Writing $I(x) = (x-1-\log x)/2$ for the Cramér rate function of $\chi^2_d/d$, Cramér's theorem gives $\chi^2_{3k,\alpha}/(3k) \to x_3$ and $\chi^2_{k,\alpha}/k \to x_1$, where $x_3, x_1 > 1$ solve $I(x_3) = b^2/6$ and $I(x_1) = b^2/2$. The difference of CDFs tends to $1$ when the robust test does not reject, $3x_3 > 3+c$, and the additive test does, $x_1 < 1+c$; since $I$ is increasing on $(1,\infty)$, these are $b^2 > c-3\log(1+c/3)$ and $b^2 < c-\log(1+c)$. The source obtains its window instead from Fisher's approximation $\chi^2_{d,\alpha} \approx \tfrac12(z_\alpha+\sqrt{2d})^2$, which requires $\tfrac12b^2+\sqrt6\,b-c > 0$ and $\tfrac12b^2+\sqrt2\,b-c < 0$, i.e. $b \in \big(\sqrt{2c+6}-\sqrt6,\ \sqrt{2c+2}-\sqrt2\big)$. That approximation is not exact when $z_\alpha = b\sqrt k$, and the approximate window overshoots the exact one: for $c = 1$ it is $(0.379, 0.586)$ against the exact $(0.370, 0.554)$, and at $b = 0.57$ the exact limit $x_1 \approx 2.036 > 1+c$ makes both powers tend to $0$. The single-variant bound (a maximal loss of under 20%, known for the 3-df test) is therefore not the right guide for multilocus testing; the paper's remedy is to combine the classical and robust tests rather than replace one by the other.

## Sources

- Ruilin Bai and Bo Chen, *X-chromosome multilocus association studies for common and rare variants*, J. Comput. Biol. (2026, published online 12 November 2026). <https://doi.org/10.1177/15578666261502459> Section 3 (Theorem 1, proof in Appendix A), Section 4 (Lemmas 1–2, Theorems 2 and 3). Locators use the numbering of the preprint arXiv:2511.18948. The statement of Theorem 3 there has $\sqrt6$ and $\sqrt2$ under the roots, $b \in (\sqrt{2c+\sqrt6}-\sqrt6, \sqrt{2c+\sqrt2}-\sqrt2)$, where its proof (Supplementary Appendix B) gives $6$ and $2$; that corrected window rests on a normal approximation to the null quantile, so this page states the exact window from the large-deviation limit instead (see Expansion).
