# Well-distributed sequences

A sequence $(x_m)_{m \in \mathbb{N}}$ of real numbers is
well-distributed if for every $\varepsilon > 0$ there is a $K$ such that for all $k \ge K$, all
$n \in \mathbb{N}$ and all real numbers $a, b$ with $0 \le a \le b \le 1$, the number $N$ of
indices $m$ with $n < m \le n + k$ and $x_m \in [a, b)$ satisfies $|N - (b - a)k| < \varepsilon k$.

No condition $x_m \in [0, 1)$ is imposed, so finite changes to a sequence do not affect this
property.

## Sources

- EP-997 (Erdős Problem #997) [Erdős Problems].
