# Time dilation of the Bregman-Lagrangian flow (Euclidean case)

Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$. Let $\tau : \mathbb{R} \to \mathbb{R}$ be differentiable at $t$ with $\dot\tau(t) > 0$, and suppose that $X, Z : \mathbb{R} \to E$ solve the Euler–Lagrange system for the parameters $(\alpha, \beta)$ at time $\tau(t)$:

$$
\dot X = e^{\alpha}(Z - X), \qquad \dot Z = -e^{\alpha + \beta}\nabla f(X) \qquad \text{at } \tau(t).
$$

Then $Y = X \circ \tau$ and $W = Z \circ \tau$ solve the same system at $t$ for the parameters

$$
\tilde\alpha_t = \alpha_{\tau(t)} + \log\dot\tau(t), \qquad \tilde\beta_t = \beta_{\tau(t)} .
$$

Traversing a solution curve at another speed gives a solution for other parameters, and the [ideal scaling is preserved](time-dilation-ideal-scaling.md); so in the polynomial family the rates $O(1/t^p)$ for all $p$ come from one curve: the curve for $p$ is the curve for $p = 2$ traversed with $\tau(t) = t^{p/2}$ (Wibisono, Wilson and Jordan, Section 3).

## Background

- [Polynomial rate for the polynomial Bregman-Lagrangian family](polynomial-family-rate.md): the family of flows related by time dilation.

## Sources

- A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351–E7358), Theorem 2.2 with the parameters (2.10a)–(2.10b), for the first-order form (2.7) with $h = \|\cdot\|^2/2$; the third parameter $\tilde\gamma = \gamma\circ\tau$ (2.10c) only enters through the ideal scaling (2.2b) that reduces (2.5) to (2.7).
