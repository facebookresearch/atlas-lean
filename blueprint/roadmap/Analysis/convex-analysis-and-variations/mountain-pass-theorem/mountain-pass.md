# Mountain pass theorem

Let $E$ be a real Banach space and let $f : E \to \mathbb{R}$ be
continuously differentiable and satisfy the Palais–Smale condition. Let $a, b \in E$ and let
$\varepsilon, r$ be real numbers such that $a$ and $b$ are separated by a mountain range of $f$
at height $\varepsilon$ and radius $r$: $f(a) = 0$, $\varepsilon > 0$, $r > 0$,
$f(y) \ge \varepsilon$ for every $y$ with $\|y - a\| = r$, $\|b - a\| > r$ and $f(b) \le 0$.
Then the mountain pass level $c$ of $f$ between $a$ and $b$ satisfies $c \ge \varepsilon$, and
$f$ has a critical point $x$ with $f(x) = c$.

## Sources

- A. Ambrosetti and P.H. Rabinowitz, 'Dual variational methods in critical point theory and applications', J. Funct. Anal. 14 (1973) 349–381. Listed as §119 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `mountain_pass`.
