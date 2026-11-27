# Pearson–Aitken selection formulas under linear homoscedastic regression

Let $z = (x, y)$ be a random vector with mean $(\mu_x, \mu_y)$ and covariance blocks $V_x$ (invertible), $C_{xy} = C_{yx}^\top$ and $V_y$, and suppose the relationship among the variables is linear and homoscedastic: $E[y \mid x] = \mu_y + C_{yx} V_x^{-1}(x - \mu_x)$ and $\operatorname{Var}(y \mid x)$ does not depend on $x$, with no assumption that the residual $y - E[y \mid x]$ is independent of $x$. If selection acts on $x$ only, changing its mean to $\tilde\mu_x$ and its covariance to $\tilde V_x$ while leaving the conditional law of $y$ given $x$ unchanged, then after selection

$$\tilde\mu_y = \mu_y + C_{yx} V_x^{-1}(\tilde\mu_x - \mu_x), \qquad \tilde C_{xy} = \tilde V_x V_x^{-1} C_{xy}, \qquad \tilde V_y = V_y - C_{yx}\bigl(V_x^{-1} - V_x^{-1} \tilde V_x V_x^{-1}\bigr) C_{xy}.$$

These are the Pearson–Aitken selection formulas, given by Pearson (1903) and Aitken (1935); Lawley (1943) showed that they hold under linearity and homoscedasticity of the regression alone (see also Dolan, Molenaar and Boomsma 1994, equations (2a)–(2c)). When $y = a + B x + E$ with a residual $E$ independent of $x$ and selection reweights the law by a function of $x$, the formulas are [selected means under linear regression selection](../not-yet-classified/pearson-aitken-lawley-selection/integral-response-selected.md) and [selected covariance blocks under linear regression selection](../not-yet-classified/pearson-aitken-lawley-selection/covariance-selected.md); this page states Lawley's extension. They follow from the laws of total expectation and total covariance: with $B = C_{yx} V_x^{-1}$ and $\Sigma = \operatorname{Var}(y \mid x) = V_y - B C_{xy}$, selection gives $\tilde C_{yx} = B \tilde V_x$ and $\tilde V_y = \Sigma + B \tilde V_x B^\top$, which is the stated form by [Aitken's block identity](../not-yet-classified/pearson-aitken-lawley-selection/aitken-block-identity.md).

## Proof depends on

- [Aitken's block identity](../not-yet-classified/pearson-aitken-lawley-selection/aitken-block-identity.md)

## Expansion

1. The model: a joint law with linear homoscedastic regression of $y$ on $x$, with a residual that need not be independent of $x$, and selection that leaves the conditional law of $y$ given $x$ unchanged.
2. The selected mean and cross-covariance by the law of total expectation, using only the linearity of $E[y \mid x]$.
3. The selected covariance of $y$ by the law of total covariance, using the homoscedasticity of $\operatorname{Var}(y \mid x)$, and its rewriting by Aitken's block identity.
4. Correlated responses to selection in quantitative genetics, as a separate statement.

## Sources

- Original result: K. Pearson, Mathematical contributions to the theory of evolution. XI. On the influence of natural selection on the variability and correlation of organs, Philos. Trans. Roy. Soc. London A 200 (1903), 1–66. <https://doi.org/10.1098/rsta.1903.0001>
- Original result: A. C. Aitken, Note on selection from a multivariate normal population, Proc. Edinburgh Math. Soc. 4 (1935), 106–110. <https://doi.org/10.1017/s0013091500008063>
- D. N. Lawley, A note on Karl Pearson's selection formulae, Proc. Roy. Soc. Edinburgh Sect. A 62 (1943), 28–30.
- C. V. Dolan, P. C. M. Molenaar and D. I. Boomsma, Simultaneous genetic analysis of means and covariance structure: Pearson–Lawley selection rules, Behav. Genet. 24 (1994), 17–24, equations (2a)–(2c).
