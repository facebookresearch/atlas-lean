# GD on overparameterized two-layer ReLU networks reaches zero training loss (Du et al.)

Consider a two-layer ReLU network $f(x) = \frac{1}{\sqrt m} \sum_{r=1}^m a_r \max(0, \langle w_r, x \rangle)$ in which only
the first-layer weights $w_r$ are trained and the signs $a_r \in \{\pm 1\}$ are fixed, with $w_r(0)$ independent standard
Gaussian and $a_r$ uniform, square loss on $n$ training points with $\lVert x_i \rVert = 1$, $\lvert y_i \rvert$ bounded and
no two inputs parallel, so that the limiting Gram matrix $H^\infty$ has $\lambda_0 = \lambda_{\min}(H^\infty) > 0$. If
$m \ge c\, n^6/(\lambda_0^4 \delta^3)$ and gradient descent uses step size $\eta = c' \lambda_0 / n^2$, then with
probability at least $1 - \delta$ the training loss decreases as $(1 - \eta\lambda_0/2)^t$ times its initial value (Du
et al., Theorem 4.1). This is a theorem about this model, not a general
convergence result for deep learning.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: Neural tangent kernel and the kernel-gradient training identity.

## Sources

- Gradient Descent Provably Optimizes Over-parameterized Neural Networks (Du, Zhai, Poczos, Singh, ICLR 2019; arXiv:1810.02054) — arXiv / ICLR: Theorem 3.1 ($\lambda_0 > 0$ when no two inputs are parallel) and Theorem 4.1 ($m = \Omega(n^6/(\lambda_0^4\delta^3))$, $\eta = O(\lambda_0/n^2)$, linear convergence with factor $1 - \eta\lambda_0/2$). <https://arxiv.org/abs/1810.02054>
