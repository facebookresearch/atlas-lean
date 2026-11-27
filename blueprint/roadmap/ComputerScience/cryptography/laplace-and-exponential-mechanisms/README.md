# Laplace and exponential mechanisms

The two basic ways of achieving pure differential privacy (Dwork and Roth 2014, Sections 3.3 and 3.4). The Laplace mechanism answers a numeric query $f$ by adding Laplace noise of scale $\Delta f / \varepsilon$, where $\Delta f$ is the $\ell_1$-sensitivity of $f$: the most one individual can change $f$. The exponential mechanism answers a query with an arbitrary range by sampling an output with probability proportional to $\exp(\varepsilon u(x, r) / (2 \Delta u))$, for a utility score $u$ of sensitivity $\Delta u$; it loses at most $O((\Delta u / \varepsilon) \log |R|)$ in utility with high probability. The Gaussian mechanism, which gives $(\varepsilon, \delta)$-privacy with noise calibrated to the $\ell_2$-sensitivity, is treated in [differential privacy](../differential-privacy/README.md).

## Laplace mechanism

- [Laplace mechanism](laplace-mechanism.md)
- [The Laplace mechanism is differentially private](laplace-mechanism-differentially-private.md)
- [The Laplace mechanism for vector-valued queries](laplace-mechanism-pi-differentially-priv.md)

## Exponential mechanism

- [Weights of the exponential mechanism](exp-mech-weight.md)
- [Output probabilities of the exponential mechanism](exp-mech-prob.md)
- [Exponential mechanism](exp-mechanism.md)
- [Events under the exponential mechanism](exp-mechanism-apply.md)
- [Output probabilities on neighbouring databases](exp-mech-prob-le-exp-mul.md)
- [The exponential mechanism is differentially private](exp-mechanism-differentially-private.md)
- [Optimal utility](opt-utility.md)
- [Utility of the exponential mechanism](exp-mechanism-utility.md)
- [Utility of the exponential mechanism, simple form](exp-mechanism-utility-card.md)

## Related topics

- [Differential privacy](../differential-privacy/README.md): the definition these mechanisms satisfy, and the composition theorems used to combine them.
- [Laplace distribution](../../../Probability/distributions/continuous/laplace-distribution/README.md): the noise law of the Laplace mechanism, its normalisation and the density shift bound behind its privacy.
- [Least squares, ridge and lasso regression](../../machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md): the same Laplace density appears there as the prior whose MAP estimate is the lasso.
