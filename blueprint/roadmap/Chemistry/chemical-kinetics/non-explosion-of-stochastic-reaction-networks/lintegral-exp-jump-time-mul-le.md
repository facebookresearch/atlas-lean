# Under a drift condition, a discounted moment bound for the jump chain

Let $S$ be a countable set with a σ-algebra in which every singleton is measurable, $P$ a jump
kernel on $S$ (a probability mass function $P(x, \cdot)$ on $S$ for each $x \in S$), and
$\mathbb{P}_P$ the [input law](input-measure.md). Let $q : S \to \mathbb{R}$ with $q(x) > 0$ for
every $x \in S$, $c \ge 0$ and $V : S \to [0, \infty]$ satisfy the one-step drift condition

$$q(x) \sum_{y \in S} P(x, y)\, V(y) \le \bigl(q(x) + c\bigr)\, V(x) \qquad
\text{for every } x \in S$$

in $[0, \infty]$. Then for every $n \in \mathbb{N}$ and $x \in S$,

$$\int e^{-c T_n(x, \omega)}\, V\bigl(Y_n(x, \omega)\bigr) \, d\mathbb{P}_P(\omega) \le V(x),$$

a lower Lebesgue integral with values in $[0, \infty]$, where $Y_n$ is the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
and $T_n$ the [jump time](jump-time.md) of the chain started at $x$. This is the case
$A = \emptyset$ of the
[mean bound for the stopped discounted process](lintegral-discounted-stop-le.md). Where $V(x)$ and
$\sum_y P(x, y) V(y)$ are finite, the drift condition at $x$ reads $\mathcal{L} V(x) \le c\, V(x)$
for the generator $\mathcal{L} V(x) = q(x) \bigl( \sum_y P(x, y) V(y) - V(x) \bigr)$.
