# Lower bound on the volume of a staircase region

Let $t$ be a natural number and let
$c, n$ be real numbers with $c \ge 0$ and $ct \le n$. Let $X \subseteq \mathbb{R}^t$ be the set of
points $y = (y_0, \dots, y_{t-1})$ such that $y_i < n - ic$ for every $i$, $y_{i+1} + c < y_i$ for
every $i < t - 1$, and $y_{t-1} > 0$ if $t \ge 1$. Then the $t$-dimensional Lebesgue measure of
$X$ is at least $(n/t - c)^t$, where $n/t$ is read as $0$ when $t = 0$.

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 4.8 (`integers-2024-A1-lem-4-8`), the explicit bound.
