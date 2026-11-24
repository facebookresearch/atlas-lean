# Logistic regression and support vector machines

Training a linear classifier is a convex optimization problem for the two standard losses. Logistic regression minimizes the negative log-likelihood $\sum_k \big(\log(1 + e^{z_k}) - y_k z_k\big)$ of the logistic model $P(y_k = 1) = \sigma(z_k)$, $z = X\theta$, a sum of the convex softplus function composed with affine maps. The soft-margin support vector machine minimizes the hinge loss plus a ridge penalty, $\sum_k \max(0, 1 - y_k(x_k^{\mathsf T} w + b)) + \lambda \|w\|^2$, a convex upper bound on the number of misclassified examples. Convexity means that every local minimizer is global (see [first-order conditions](../../../../Analysis/convex-analysis-and-variations/first-order-conditions-for-convexity/README.md)) and that general-purpose convex methods such as [gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/README.md) and interior-point methods apply.

- [Derivative of the softplus function](has-deriv-at-log-one-add-exp.md)
- [Convexity of the softplus function](convex-on-log-one-add-exp.md)
- [Negative log-likelihood of logistic regression](logistic-nll.md)
- [The logistic loss is the negative log-likelihood of the logistic model](logistic-nll-eq-neg-log-likelihood.md)
- [Logistic regression is a convex problem](convex-on-logistic-nll.md)
- [Soft-margin support vector machine objective](svm-objective.md)
- [The support vector machine is a convex problem](convex-on-svm-objective.md)
- [The hinge loss bounds the number of misclassified examples](card-misclassified-le-sum-hinge.md)

With a kernel $k$, the linear predictor $x \mapsto x^{\mathsf T} w$ is replaced by a function $f$ of the reproducing kernel Hilbert space of $k$, penalized by $\|f\|^2$. By the representer theorem every minimizer is a finite kernel expansion $f = \sum_i \alpha_i k(\cdot, x_i)$, the support vector expansion, so the problem reduces to the $m$ coefficients $\alpha_i$ and the offset.

- [Soft-margin support vector machine objective with offset](svm-risk.md)
- [The support vector expansion](exists-eq-kernel-expansion-of-is-minimiz.md)

## Related topics

- [Least squares, ridge and lasso regression](../least-squares-ridge-and-lasso-regression/README.md)
- [Cross-entropy loss](../cross-entropy-loss/README.md)
- [Lagrange duality](../../../../Analysis/convex-analysis-and-variations/lagrange-duality/README.md)
- [Representer theorem](../../../../Analysis/hilbert-spaces/representer-theorem/README.md): the general statement behind the support vector expansion, for any loss of the values $f(x_i)$ and any strictly increasing function of $\|f\|$.
