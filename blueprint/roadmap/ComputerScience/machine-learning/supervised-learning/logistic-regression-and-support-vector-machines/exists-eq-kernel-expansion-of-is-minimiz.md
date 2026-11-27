# The support vector expansion

**The support vector expansion** (Schölkopf, Herbrich and Smola, *A generalized
representer theorem*, COLT 2001, Theorem 1 and Example 2). Let $H$ be a real reproducing kernel
Hilbert space of functions on a set $X$ with kernel $k$, let $x_1, \dots, x_m \in X$,
$y_1, \dots, y_m \in \mathbb{R}$ and $\lambda \in \mathbb{R}$. If $(f, b) \in H \times \mathbb{R}$
minimizes the [soft-margin SVM objective with offset](svm-risk.md)
$\lambda^{-1} \sum_i \max(0, 1 - y_i (g(x_i) + c)) + \|g\|^2$ over all $g \in H$ and all offsets
$c \in \mathbb{R}$, then $f = \sum_i \alpha_i k(\cdot, x_i)$ for some coefficients
$\alpha_1, \dots, \alpha_m \in \mathbb{R}$.

Only the training points enter the expansion, and in practice many coefficients $\alpha_i$ vanish: the remaining $x_i$ are the support vectors. The offset $b$ is left free; Schölkopf, Herbrich and Smola treat it through their semiparametric representer theorem (Theorem 2, with $\psi_1 = 1$), while for each fixed offset the hinge term is a loss of the values $f(x_i)$ and the nonparametric theorem applies.

## Background

- [Soft-margin support vector machine objective](svm-objective.md): the linear SVM in $\mathbb{R}^d$, whose objective is convex; it is the case of the linear kernel, up to the scaling of the two terms.
