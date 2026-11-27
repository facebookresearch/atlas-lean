# Taylor remainder for a map with Lipschitz derivative

Let $E$ and $F$ be real normed spaces and let $G \colon E \to F$ be Fréchet differentiable at every point, with derivative $DG$ satisfying $\|DG(y) - DG(y')\| \le L \|y - y'\|$ for all $y, y'$. Then for all $x, d \in E$,

$$\|G(x + d) - G(x) - DG(x)\, d\| \le \frac{L}{2} \|d\|^2.$$

Applied to $G = \nabla f$, this bounds the error of the first-order model of the gradient by the Lipschitz constant of the Hessian.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.5.3 (the integral estimate in "Quadratically convergent phase").
- Cf. Y. Nesterov, *Introductory Lectures on Convex Optimization: A Basic Course*, Kluwer, 2004, Ch. 1 (functions with Lipschitz Hessian).
