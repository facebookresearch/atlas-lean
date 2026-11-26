# The gradient update of a convex smooth function is non-expansive

Let $f$ be convex and differentiable on a real Hilbert space, with $\beta$-Lipschitz gradient ($\beta > 0$), and let $0 \le \alpha \le 2/\beta$. Then the gradient update $G(w) = w - \alpha \nabla f(w)$ is $1$-expansive: for all $v, w$,

$$
\lVert G(v) - G(w) \rVert \le \lVert v - w \rVert .
$$

Proof: expanding the square and using [co-coercivity](inner-gradient-sub-ge.md),

$$
\lVert G(v) - G(w)\rVert^2 = \lVert v - w\rVert^2 - 2\alpha \langle \nabla f(v) - \nabla f(w), v - w\rangle + \alpha^2 \lVert \nabla f(v) - \nabla f(w)\rVert^2 \le \lVert v - w\rVert^2 - \alpha\Big(\frac{2}{\beta} - \alpha\Big) \lVert \nabla f(v) - \nabla f(w)\rVert^2 .
$$

Without convexity only the [$(1 + \alpha\beta)$ bound](norm-gradient-step-sub-le-one-add-mul.md) holds.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.7.2 (proof in Appendix A).
