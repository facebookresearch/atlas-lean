# Integer matrices with a Pisa eigenvector

Let $j, m \ge 1$ be integers, let
$\tau_{j,m} = (j + \sqrt{j^2 + 4m})/2$, and let $M$ be a $2 \times 2$ integer matrix.
(a) If $j^2 + 4m$ is not a perfect square, then $(\tau_{j,m}, 1)^T$ is a right eigenvector of $M$
over $\mathbb{R}$ if and only if $M$ has rows $(t + sj, ms)$ and $(s, t)$ for some integers $s, t$.
(b) If $j^2 + 4m = r^2$ with $r$ a natural number, then $(\tau_{j,m}, 1)^T$ is a right
eigenvector of $M$ over $\mathbb{R}$ if and only if $M$ has rows $(s, t)$ and $(u, v)$ with
$u(j+r)^2 + 2(v-s)(j+r) - 4t = 0$.

In (b) $r$ is the nonnegative root, as the paper's proof uses $\tau_{j,m} = (j + r)/2$. For the
negative root the printed statement fails: for $j = 1$, $m = 2$, $r = -3$, the matrix $M$ with
rows $(0, 0)$ and $(1, 1)$ satisfies $u(j+r)^2 + 2(v-s)(j+r) - 4t = 4 - 4 - 0 = 0$, but
$\tau_{1,2} = 2$ and $M (2, 1)^T = (0, 3)^T$ is not a multiple of $(2, 1)^T$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 63 (`jis-2025-25.1.5-thm-63`).
