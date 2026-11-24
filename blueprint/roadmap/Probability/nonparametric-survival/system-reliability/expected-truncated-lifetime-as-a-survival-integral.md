# Expected truncated lifetime as a survival integral

Let $L$ be a nonnegative random variable and $T > 0$. Then $E[\min(L, T)] = \int_0^T P(L > t)\,dt$, and $E[L] = \int_0^\infty P(L > t)\,dt$ in $[0, \infty]$.

Proof. $\min(L, T) = \int_0^T \mathbf 1\{L > t\}\,dt$ pointwise; take expectations and exchange expectation and integral by Tonelli's theorem for the nonnegative integrand. Letting $T \to \infty$ with monotone convergence gives the second formula.
