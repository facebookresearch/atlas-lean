# Descent lemma

Let $E$ be a real Hilbert space, let $L \ge 0$, and let $f \colon E \to \mathbb{R}$ be differentiable with $L$-Lipschitz gradient. Then for all $x, d \in E$,

$$f(x + d) \le f(x) + \langle \nabla f(x), d \rangle + \frac{L}{2} \|d\|^2.$$

## Sources

- Cf. Y. Nesterov, *Introductory Lectures on Convex Optimization: A Basic Course*, Kluwer, 2004, Ch. 1 (functions with Lipschitz gradient).
- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.1.2, eq. (9.13) (there under the Hessian bound $\nabla^2 f \preceq M I$).
