# Linear convergence of gradient descent under the Polyak–Łojasiewicz inequality

Let $f : \mathbb{R}^n \to \mathbb{R}$ be differentiable with $L$-Lipschitz gradient, $L > 0$, let $f^* = \min f$ be attained, and suppose the Polyak–Łojasiewicz inequality $\frac12\|\nabla f(x)\|^2 \ge \mu(f(x) - f^*)$ holds for every $x$ with some $\mu > 0$. Then gradient descent $x_{k+1} = x_k - \frac1L\nabla f(x_k)$ satisfies $f(x_k) - f^* \le (1 - \mu/L)^k(f(x_0) - f^*)$ for every $k$. Convexity is not assumed.

Proof. If $f$ is constant both sides are $0$. Otherwise some gradient is nonzero, and the descent lemma at that point, $f^* \le f(x) - \frac{1}{2L}\|\nabla f(x)\|^2$, combined with the inequality gives $\mu \le L$. The descent lemma with step $-\nabla f(x_k)/L$ gives $f(x_{k+1}) \le f(x_k) - \frac{1}{2L}\|\nabla f(x_k)\|^2 \le f(x_k) - \frac{\mu}{L}(f(x_k) - f^*)$; subtract $f^*$ and iterate.

## Proof depends on

- [Descent lemma](gradient-descent-descent-lemma.md): descent lemma.

## Sources

- H. Karimi, J. Nutini and M. Schmidt, "Linear convergence of gradient and proximal-gradient methods under the Polyak–Łojasiewicz condition", ECML PKDD 2016, <https://arxiv.org/abs/1608.04636>, inequality (3) and Theorem 1
