# Drift-condition moment bound at time $s \ge 0$ after at most $n$ jumps

Let $S$ be a countable set with a σ-algebra in which every singleton is measurable, $P$ a jump
kernel on $S$ (a probability mass function $P(x, \cdot)$ on $S$ for each $x \in S$), and
$\mathbb{P}_P$ the [input law](input-measure.md). Let $q : S \to \mathbb{R}$ with $q(x) > 0$ for
every $x \in S$, $c \ge 0$ and $V : S \to [0, \infty)$ satisfy the one-step drift condition

$$q(x) \sum_{y \in S} P(x, y)\, V(y) \le \bigl(q(x) + c\bigr)\, V(x) \qquad
\text{for every } x \in S;$$

each sum is then finite, and the condition reads $\mathcal{L} V \le c\, V$ for the generator
$\mathcal{L} V(x) = q(x) \bigl( \sum_y P(x, y) V(y) - V(x) \bigr)$. Then for every
$n \in \mathbb{N}$, $x \in S$ and $s \ge 0$, the
[state $X^{(n)}_s$ at time $s$ of the chain started at $x$ and stopped after $n$ jumps](state-at.md)
satisfies

$$\int V\bigl(X^{(n)}_s(x, \omega)\bigr) \, d\mathbb{P}_P(\omega) \le e^{c s}\, V(x),$$

a lower Lebesgue integral with values in $[0, \infty]$: the expectation of $V(X^{(n)}_s)$.
