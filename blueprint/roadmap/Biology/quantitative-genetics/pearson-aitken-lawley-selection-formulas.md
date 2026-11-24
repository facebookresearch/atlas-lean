# Pearson–Aitken selection formulas

Let $z = (x, y)$ be a random vector with mean $(\mu_x, \mu_y)$ and covariance blocks $V_x$ (invertible), $C_{xy} = C_{yx}^\top$ and $V_y$, and suppose the relationship among the variables is linear and homoscedastic: $E[y \mid x] = \mu_y + C_{yx} V_x^{-1}(x - \mu_x)$ and $\operatorname{Var}(y \mid x)$ does not depend on $x$, as for jointly normal vectors. If selection acts on $x$ only, changing its mean to $\tilde\mu_x$ and its covariance to $\tilde V_x$ while leaving the conditional law of $y$ given $x$ unchanged, then after selection

$$\tilde\mu_y = \mu_y + C_{yx} V_x^{-1}(\tilde\mu_x - \mu_x), \qquad \tilde C_{xy} = \tilde V_x V_x^{-1} C_{xy}, \qquad \tilde V_y = V_y - C_{yx}\bigl(V_x^{-1} - V_x^{-1} \tilde V_x V_x^{-1}\bigr) C_{xy}.$$

These are the Pearson–Aitken selection formulas (Carey, handout). They follow from the laws of total expectation and total covariance: with $B = C_{yx} V_x^{-1}$ and $\Sigma = \operatorname{Var}(y \mid x) = V_y - B C_{xy}$, selection gives $\tilde C_{yx} = B \tilde V_x$ and $\tilde V_y = \Sigma + B \tilde V_x B^\top$.

## Proof depends on

- [Gaussian conditioning (Schur complement)](../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)

## Expansion

1. The model: a joint law with linear homoscedastic regression of $y$ on $x$, and selection as reweighting of the law of $x$ by a nonnegative function of $x$.
2. Preservation of the conditional law of $y$ given $x$ under such reweighting.
3. The three formulas by the laws of total expectation and total covariance.
4. The Gaussian case, where linearity and homoscedasticity follow from [Gaussian conditioning](../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md).
5. Correlated responses to selection in quantitative genetics, as a separate statement.

## Sources

- G. Carey, Pearson–Aitken selection formula, course handout, Institute for Behavioral Genetics, University of Colorado.
- Original result: K. Pearson, Mathematical contributions to the theory of evolution. XI. On the influence of natural selection on the variability and correlation of organs, Philos. Trans. Roy. Soc. London A 200 (1903), 1–66. <https://doi.org/10.1098/rsta.1903.0001> The selection formulas follow Carey's handout.
- Original result: A. C. Aitken, Note on selection from a multivariate normal population, Proc. Edinburgh Math. Soc. 4 (1935), 106–110. <https://doi.org/10.1017/s0013091500008063> The matrix form follows Carey's handout.
