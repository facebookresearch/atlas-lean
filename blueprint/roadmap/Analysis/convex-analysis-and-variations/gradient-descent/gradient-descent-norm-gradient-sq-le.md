# Gradient norm bound for smooth lower-bounded functions

Let $f : E \to \mathbb{R}$ be
differentiable on a real Hilbert space $E$, with $L$-Lipschitz gradient for $L \ge 0$.
If $f_{\mathrm{lower}} \le f(y)$ for every $y \in E$, then for every $x \in E$,
$\|\nabla f(x)\|^2 \le 2L (f(x) - f_{\mathrm{lower}})$.

The proof only uses that $f_{\mathrm{lower}}$ is a global lower bound, so it need not be the
infimum. Neither convexity nor an attained minimum is required.

## Sources

- A. Khaled and P. Richtárik, [*Better Theory for SGD in the Nonconvex World*](https://arxiv.org/abs/2002.03329v3), §4.5, Lemma 1, eq. (14), and §10.1 (proof), where the lower bound is the infimum.
