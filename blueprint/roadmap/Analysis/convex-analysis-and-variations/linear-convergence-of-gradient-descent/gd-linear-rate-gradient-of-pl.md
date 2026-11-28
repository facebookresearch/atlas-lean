# Linear convergence of gradient descent under the Polyak–Łojasiewicz inequality

Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$ differentiable with $L$-Lipschitz gradient, where $0 < \mu \le L$. Suppose $x^*$ is a global minimizer of $f$ and $f$ satisfies the Polyak–Łojasiewicz inequality $2\mu\,(f(x) - f(x^*)) \le \|\nabla f(x)\|^2$ for all $x$. Then the gradient descent iterates $x_{k+1} = x_k - \frac{1}{L} \nabla f(x_k)$ from any $x_0$ satisfy

$$f(x_k) - f(x^*) \le \Big(1 - \frac{\mu}{L}\Big)^k \big(f(x_0) - f(x^*)\big).$$
