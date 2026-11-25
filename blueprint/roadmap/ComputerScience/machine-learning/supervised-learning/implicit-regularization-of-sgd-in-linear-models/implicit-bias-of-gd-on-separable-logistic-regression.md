# Implicit bias of GD on separable logistic regression

Let $\{(x_i, y_i)\}_{i=1}^n$ be linearly separable with $y_i \in \{\pm 1\}$, and minimize
$\mathcal{L}(w) = \sum_i \ell(y_i \langle w, x_i \rangle)$ by gradient descent with a constant step size small enough
for the smoothness of $\mathcal{L}$, where $\ell$ is positive, differentiable, strictly decreasing to $0$, has a
Lipschitz derivative and has a tight exponential tail as in Soudry et al. (logistic loss is an example). Then
$\lVert w_t \rVert \to \infty$ and $w_t / \lVert w_t \rVert$ converges to the $\ell_2$ max-margin direction
$\hat w / \lVert \hat w \rVert$, where $\hat w$ solves the hard-margin SVM problem; the directional distance
decreases as $O(1/\log t)$ in the regimes stated in the source. The rate statements are those of the source and
are not claimed for every loss with exponential tail.

## Depends on

- [Hard-margin SVM and margin-based sample complexity](../logistic-regression-and-support-vector-machines/hard-margin-svm-and-margin-based-sample-complexity.md)

## Proof depends on

- [Sublinear rate of gradient descent for smooth convex functions](../../../../Analysis/convex-analysis-and-variations/gradient-descent/gradient-descent-convex-sublinear-rate.md)

## Sources

- The Implicit Bias of Gradient Descent on Separable Data (Soudry et al., JMLR 2018; arXiv:1710.10345) — arXiv / JMLR: Assumptions 1–3 and Theorem 3 (convergence of $w(t)/\lVert w(t) \rVert$ to the max-margin direction for $\beta$-smooth decreasing losses with a tight exponential tail and step size $\eta < 2\beta^{-1}\sigma_{\max}^{-2}(X)$), with the $O(1/\log t)$ rate. <https://arxiv.org/abs/1710.10345>
