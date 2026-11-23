# Soft-margin support vector machine objective

Let $X$ be a real $m \times \iota$ matrix with rows $x_k$, let $y \in \mathbb{R}^m$ (labels in $\{-1, 1\}$), and let $\lambda \in \mathbb{R}$. The SVM objective of the affine classifier $x \mapsto x^{\mathsf T} w + b$ is

$$J(w, b) = \sum_{k=1}^m \max\big(0, 1 - y_k(x_k^{\mathsf T} w + b)\big) + \lambda\, w^{\mathsf T} w,$$

the hinge loss plus a ridge penalty on $w$; the intercept $b$ is not penalized. Eliminating the slack variables of Boyd–Vandenberghe's support vector classifier gives the same hinge terms.

## Sources

- T. Hastie, R. Tibshirani and J. Friedman, *The Elements of Statistical Learning*, 2nd ed., Springer, 2009, §12.3.2 ("The SVM as a Penalization Method").
- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §8.6.1 (the support vector classifier, in slack-variable form).
