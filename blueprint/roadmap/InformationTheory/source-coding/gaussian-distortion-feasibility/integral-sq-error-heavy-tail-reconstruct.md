# Integral sq error heavy Tail Reconstruction

Let $\mu$ be the heavy-tailed reconstruction, the image of $\mathcal{N}(0, 1)$ under $x \mapsto \left(x, x - e^{x^2/4}\right)$. The square error $(x - y)^2$ is not $\mu$-integrable, so under the convention that the real integral of a non-integrable function is $0$,

$$\int (x - y)^2 \, d\mu(x, y) = 0.$$

This would pass the test $\int (x - \hat{x})^2 \, d\mu \le D$ for every $D \ge 0$, so the real integral alone is not a feasibility test.
