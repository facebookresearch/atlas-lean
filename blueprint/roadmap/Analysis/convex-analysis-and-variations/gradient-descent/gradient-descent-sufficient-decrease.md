# Sufficient decrease of a gradient step

Let $E$ be a real Hilbert space, let $L > 0$, let $f \colon E \to \mathbb{R}$ be differentiable with $L$-Lipschitz gradient, and let $0 < \eta \le 1/L$. Then for every $x \in E$,

$$f\big(x - \eta \nabla f(x)\big) \le f(x) - \frac{\eta}{2} \|\nabla f(x)\|^2.$$

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.3.1, eq. (9.17) and the step $t = 1/M$ in the analysis for exact line search.
- Cf. Y. Nesterov, *Introductory Lectures on Convex Optimization: A Basic Course*, Kluwer, 2004, Ch. 1 (the gradient method).
