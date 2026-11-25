# Local-linear regression adjustment in approximate Bayesian computation

Let $(\theta_i,s_i)$, $i=1,\ldots,m$, be parameter–summary pairs with $\theta_i\in\mathbb R$ drawn from the prior and $s_i\in\mathbb R^q$ simulated given $\theta_i$, let $s_{\rm obs}$ be the observed summary, and let $w_i=K_\varepsilon(\lVert s_i-s_{\rm obs}\rVert)\ge0$ be kernel weights for a kernel $K_\varepsilon$ supported on $[0,\varepsilon]$. The Beaumont–Zhang–Balding regression adjustment fits the weighted least-squares problem

$$(\hat a,\hat b)\in\operatorname*{arg\,min}_{a\in\mathbb R,\ b\in\mathbb R^q}\ \sum_{i=1}^mw_i\bigl(\theta_i-a-b^{\top}(s_i-s_{\rm obs})\bigr)^2,$$

which has a unique solution when the weighted Gram matrix $\sum_iw_i\,x_ix_i^{\top}$, $x_i=(1,(s_i-s_{\rm obs})^{\top})^{\top}$, is invertible, and returns the adjusted parameters

$$\theta_i^*=\theta_i-\hat b^{\top}(s_i-s_{\rm obs})$$

with weights $w_i$. With $b=0$ in place of $\hat b$ the adjustment is the identity and the weighted sample is that of kernel rejection ABC.

Exactness with the true slope: suppose that, for $s$ in the window $\{\lVert s-s_{\rm obs}\rVert\le\varepsilon\}$, the conditional law of $\theta$ given $S=s$ is that of $m(s)+e$, where $m(s)=\alpha+\beta^{\top}(s-s_{\rm obs})$ is affine and the residual $e$ has a law not depending on $s$. Then for each accepted pair, $\theta_i-\beta^{\top}(s_i-s_{\rm obs})$ given $s_i$ has the law of $\theta$ given $S=s_{\rm obs}$; so the sample adjusted with $\beta$ in place of $\hat b$ is a sample from the posterior given $S=s_{\rm obs}$, whatever the weights. Without an affine conditional mean the adjustment can be biased.

## Depends on

- [Rejection ABC returns the tolerance-conditioned posterior](abc-rejection-target-law-and-zero-tolerance-disc.md)

## Proof depends on

- [Weighted means and scatter matrices](../../../../Probability/linear-models-multivariate/weighted-means-and-scatter-matrices/README.md)

## Expansion

A full proof page must establish:

- Existence and uniqueness of the weighted least-squares solution under invertibility of the weighted Gram matrix.
- The case $b=0$ recovers kernel rejection ABC.
- Exactness with the true slope under the affine-mean, location-residual hypothesis.
- A counterexample with a nonlinear conditional mean for which the adjusted sample is biased.

## Sources

- M. A. Beaumont, W. Zhang and D. J. Balding, *Approximate Bayesian computation in population genetics*, Genetics (2002), <https://pmc.ncbi.nlm.nih.gov/articles/PMC1462356/>, abstract: a local-linear regression of simulated parameter values on simulated summary statistics, with the observed summaries substituted into the regression equation.
