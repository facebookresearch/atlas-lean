# Reference dependence of the proportionality coefficient after an additive log-ratio transform

**Setting.** Relative expression $X_1, \dots, X_d$ of $d$ genes has logged absolute amounts $A_i = \log(s X_i)$, where $s$ is the unobserved total. The additive log-ratio (alr) transform with reference gene $d$ gives $Y_i = \log(X_i / X_d) = A_i - A_d$ (Eq. (5)), so log-ratio variances are unchanged, $\operatorname{var}(Y_i - Y_j) = \operatorname{var}(A_i - A_j)$, but the individual variances now depend on $A_d$. Let $\rho$ be the proportionality coefficient $\rho(U, V) = 2\operatorname{cov}(U, V)/(\operatorname{var}(U) + \operatorname{var}(V))$, and for a fixed pair $i, j$ define

$$\varphi(A_d) = \sqrt{\frac{\operatorname{var}(2A_d)}{\operatorname{var}(A_i) + \operatorname{var}(A_j)}}, \qquad F(A_d) = \varphi^2(A_d) - 2\sqrt{1 + \rho(A_i, A_j)}\,\operatorname{corr}(A_i + A_j, A_d)\,\varphi(A_d).$$

**Proposition 3.** If $\rho(A_i, A_j) < 1$ and $F(A_d) \ne 0$,

$$\rho(Y_i, Y_j) - \rho(A_i, A_j) = \frac{1 - \rho(A_i, A_j)}{1 + 2/F(A_d)},$$

and $\rho(Y_i, Y_j) = \rho(A_i, A_j)$ when $F(A_d) = 0$. In particular a reference that is unchanged on the absolute data ($\operatorname{var}(A_d) = 0$) reproduces the absolute coefficient exactly.

**Corollary 1.** Assume $\rho(A_i, A_j) < 1$, $\operatorname{var}(A_d) > 0$ and $\operatorname{var}(A_i + A_j) > 0$. Then $\rho(Y_i, Y_j) \ge \rho(A_i, A_j)$ if and only if $\operatorname{corr}(A_i + A_j, A_d) \le \sqrt{\operatorname{var}(A_d)/\operatorname{var}(A_i + A_j)}$. Hence relative data inflate the coefficient whenever the reference is negatively correlated with the pair, or whenever $\operatorname{var}(A_d) \ge \operatorname{var}(A_i + A_j) = 4\operatorname{var}((A_i + A_j)/2)$.

**Corollary 2 (classification at a cut-off).** Fix $0 < K < 1$ and call a pair proportional on absolute (relative) data when $\rho(A_i, A_j) \ge K$ ($\rho(Y_i, Y_j) \ge K$). With $\tilde K = 2(K - \rho(A_i, A_j))/(1 - K)$, the pair is a true positive iff $F(A_d) \ge \tilde K$ and $\tilde K \le 0$; a false positive iff $F(A_d) \ge \tilde K > 0$; a true negative iff $F(A_d) < \tilde K$ and $\tilde K > 0$; a false negative iff $F(A_d) < \tilde K \le 0$.

**Corollary 3 (spurious proportionality of unchanged genes).** Let $\epsilon$ describe the noise of unchanged genes, $\operatorname{var}(A_i), \operatorname{var}(A_j) \le \operatorname{var}(\epsilon)$, and suppose $\rho(A_i, A_j) < K$. Then $\rho(Y_i, Y_j) \ge K$ for every reference with

$$\operatorname{var}(A_d) \ge \frac{8\operatorname{var}(\epsilon)}{1 - K}.$$

## Depends on

- [Proportionality coefficient and its identities](proportionality-coefficient-and-its-identities.md)

## Expansion

Write $V = \operatorname{var}(A_i) + \operatorname{var}(A_j)$ and $S = A_i + A_j$. Since $\operatorname{var}(Y_i) + \operatorname{var}(Y_j) = V - 2\operatorname{cov}(S, A_d) + 2\operatorname{var}(A_d)$ and the log-ratio variance is unchanged, identity 1 of the proportionality coefficient gives $1 - \rho(Y_i, Y_j) = (1 - \rho(A_i, A_j))/(1 + F/2)$, using $\operatorname{var}(S) = (1 + \rho)V$ to rewrite $4\operatorname{cov}(S, A_d)/V$ as $2\sqrt{1 + \rho}\,\operatorname{corr}(S, A_d)\,\varphi$. Rearranging gives Proposition 3. As a function of $\varphi$, $F$ is a parabola with minimum $-(1 + \rho)\operatorname{corr}^2(S, A_d) \ge -2$ (Lemma 1 of the appendix), so the sign of the change equals the sign of $F$, and $F \ge 0$ is the condition of Corollary 1. The difference is increasing in $F$, so solving $F(A_d) = \tilde K$ for the cut-off gives Corollary 2; Corollary 3 solves the quadratic $F = \tilde K$ for the positive root in $\varphi$ and bounds it using the variance bound on unchanged genes.

The practical reading is a Pearson-style spurious correlation for scaled log-ratio variances: a high-variance reference (for example the geometric mean in a centred log-ratio transform when most genes change) creates false positives among noisy unchanged genes and false negatives among truly proportional ones. In the fission yeast quiescence data the near-unchanged reference had absolute log variance $0.014$ against $0.51$ for the geometric mean, and the alr coefficient matched the absolute calls far better.

## Sources

- I. Erb, C. Notredame, "How should we measure proportionality on relative gene expression data?", Theory in Biosciences 135 (2016) 21–36, Eqs. (3)–(5), (10), Proposition 3, Corollaries 1–3 and Lemma 1 (Appendix), <https://doi.org/10.1007/s12064-015-0220-8>, PMCID PMC4870310.
