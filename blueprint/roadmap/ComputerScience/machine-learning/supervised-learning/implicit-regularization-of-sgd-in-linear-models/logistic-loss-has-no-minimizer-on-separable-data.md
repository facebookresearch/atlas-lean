# Logistic loss has no minimizer on separable data

Let $(x_i, y_i)_{i=1}^n$ with $x_i \in \mathbb{R}^d$ and $y_i \in \{\pm 1\}$ be linearly separable: some $w^\star$ has $y_i \langle w^\star, x_i \rangle > 0$ for every $i$. Then the logistic
loss $\mathcal{L}(w) = \sum_i \log(1 + e^{-y_i \langle w, x_i \rangle})$ has infimum $0$ over $\mathbb{R}^d$ and no minimizer.

## Proof

$\mathcal{L}(w) > 0$ for every $w$, since each term is positive. Along $c w^\star$ each margin $y_i \langle c w^\star, x_i \rangle$ tends to $+\infty$ as $c \to \infty$, so every term,
and hence $\mathcal{L}(c w^\star)$, tends to $0$.

## Related topics

- [Implicit bias of GD on separable logistic regression](implicit-bias-of-gd-on-separable-logistic-regression.md)

## Sources

- D. Soudry, E. Hoffer, M. S. Nacson, S. Gunasekar and N. Srebro, *The implicit bias of gradient descent on separable data*, JMLR 19 (2018). Background reference.
