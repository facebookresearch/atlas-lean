# Co-coercivity of the gradient

Let $f$ be convex and differentiable on a real Hilbert space, with $\beta$-Lipschitz gradient ($\beta > 0$). Then for all $v, w$,

$$
\frac{1}{\beta}\, \lVert \nabla f(v) - \nabla f(w) \rVert^2 \le \langle \nabla f(v) - \nabla f(w),\, v - w \rangle .
$$

Proof: with $g = \nabla f(y) - \nabla f(x)$ and $z = y - g/\beta$, the [first-order condition for strong convexity](add-inner-add-le-of-strong-convex-on.md) with modulus $0$ at $x$ gives $f(z) \ge f(x) + \langle \nabla f(x), z - x\rangle$, and the [descent lemma](gradient-descent-descent-lemma.md) at $y$ gives $f(z) \le f(y) - \lVert g\rVert^2/\beta + \lVert g\rVert^2/(2\beta)$. Together, $f(y) \ge f(x) + \langle \nabla f(x), y - x\rangle + \lVert \nabla f(y) - \nabla f(x)\rVert^2/(2\beta)$; adding this to the same inequality with $x$ and $y$ exchanged gives co-coercivity.

Co-coercivity strengthens the monotonicity of the gradient of a convex function, and it is what makes [the gradient update non-expansive](norm-gradient-step-sub-le.md) for steps up to $2/\beta$.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Appendix A, inequality (A.1) in the proof of Lemma 3.7.2, where it is stated without proof.
