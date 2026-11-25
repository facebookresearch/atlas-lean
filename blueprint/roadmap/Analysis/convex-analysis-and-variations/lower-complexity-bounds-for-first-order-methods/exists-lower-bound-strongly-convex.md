# Lower complexity bound for smooth strongly convex minimisation

Let $\mu > 0$ and $Q > 1$. For every $x_0 \in \ell^2$ there are a $\mu$-strongly convex $C^\infty$ function $f$ on the Hilbert space $\ell^2$ of square-summable real sequences, with $\mu Q$-Lipschitz gradient, and a minimiser $x^* \neq x_0$ of $f$ such that every sequence $(x_j)$ with $x_j \in x_0 + \operatorname{span}\{\nabla f(x_0), \dots, \nabla f(x_{j-1})\}$ for all $j$ satisfies, for every $k$,

$$
\|x_k - x^*\|^2 \ge \Big(\frac{\sqrt{Q} - 1}{\sqrt{Q} + 1}\Big)^{2k} \|x_0 - x^*\|^2
\qquad\text{and}\qquad
f(x_k) - f(x^*) \ge \frac{\mu}{2}\Big(\frac{\sqrt{Q} - 1}{\sqrt{Q} + 1}\Big)^{2k} \|x_0 - x^*\|^2 .
$$

Here $Q = L/\mu$ is the condition number. The source works in $\mathbb{R}^\infty$, which it identifies with $\ell^2$; the worst function is a quadratic with tridiagonal Hessian whose minimiser is $(x^*)^{(i)} = q^i$, $q = (\sqrt{Q} - 1)/(\sqrt{Q} + 1)$ (for $x_0 = 0$). The bound shows that $\Omega(\sqrt{Q}\log(1/\varepsilon))$ iterations are necessary, which the [accelerated method for strongly convex functions](../accelerated-gradient-methods/accelerated-strongly-convex-rate.md) attains up to a constant factor.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.1.4: Theorem 2.1.12 (class $S^{\infty,1}_{\mu,\mu Q_f}(R^\infty)$).
