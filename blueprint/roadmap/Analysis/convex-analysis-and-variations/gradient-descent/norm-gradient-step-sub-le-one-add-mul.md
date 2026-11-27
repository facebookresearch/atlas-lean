# The gradient update is $(1 + \alpha\beta)$-expansive

Let $f$ have $\beta$-Lipschitz gradient on a real Hilbert space and let $\alpha \ge 0$. Then the gradient update $G(w) = w - \alpha \nabla f(w)$ satisfies, for all $v, w$,

$$
\lVert G(v) - G(w) \rVert \le (1 + \alpha\beta)\, \lVert v - w \rVert .
$$

Proof: the triangle inequality and $\lVert \nabla f(v) - \nabla f(w)\rVert \le \beta \lVert v - w\rVert$. No convexity is needed; this is the bound used for non-convex losses.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.7.1 (proof in Appendix A).
