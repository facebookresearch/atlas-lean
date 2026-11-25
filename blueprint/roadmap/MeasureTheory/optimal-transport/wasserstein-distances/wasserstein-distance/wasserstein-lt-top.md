# The Wasserstein distance is finite on measures with finite $p$-th moments

Let $X$ be a second-countable pseudo-extended metric space whose σ-algebra contains the open sets,
let $p \ge 1$ and $x_0 \in X$. If $\mu$ and $\nu$ are probability measures with finite $p$-th
moments, $\int d(x_0, x)^p \, d\mu(x) < \infty$ and $\int d(x_0, y)^p \, d\nu(y) < \infty$, then
$W_p(\mu, \nu) < \infty$.

Proof: by the triangle inequality and $(A + B)^p \le 2^{p-1}(A^p + B^p)$, the
[product coupling](is-coupling-prod.md) has cost at most
$2^{p-1}\bigl(\int d(x_0, x)^p \, d\mu + \int d(x_0, y)^p \, d\nu\bigr)$.

So $W_p$ is a finite metric on the Wasserstein space $P_p(X)$ of probability measures with finite
$p$-th moment (Villani, Definition 6.4); the space itself is not introduced as a type here.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Definition 6.4 and the proof that $W_p$ is finite on $P_p$.
