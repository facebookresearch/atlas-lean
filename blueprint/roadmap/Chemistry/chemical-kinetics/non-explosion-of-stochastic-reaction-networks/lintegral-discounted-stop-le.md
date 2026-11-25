# A drift condition off $A$ bounds the stopped process's mean by $V(x)$

Let $S$ be a countable set with a σ-algebra in which every singleton is measurable, $P$ a jump
kernel on $S$ (a probability mass function $P(x, \cdot)$ on $S$ for each $x \in S$), and
$\mathbb{P}_P$ the [input law](input-measure.md). Let $q : S \to \mathbb{R}$ with $q(x) > 0$ for
every $x \in S$, $c \ge 0$, $V : S \to [0, \infty]$ and $A \subseteq S$, and suppose the one-step
drift condition

$$q(x) \sum_{y \in S} P(x, y)\, V(y) \le \bigl(q(x) + c\bigr)\, V(x) \qquad
\text{for every } x \notin A,$$

in $[0, \infty]$. Then for every $n \in \mathbb{N}$ and $x \in S$ the
[stopped discounted process](discounted-stop.md)
$D_n(x, \omega) = e^{-c T_{n \wedge \sigma}} V(Y_{n \wedge \sigma})$ satisfies

$$\int D_n(x, \omega) \, d\mathbb{P}_P(\omega) \le V(x),$$

a lower Lebesgue integral with values in $[0, \infty]$, so no integrability is needed. Here $Y_k$ is
the [jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
and $T_k$ are the [jump times](jump-time.md) started at $x$, and $\sigma$ is the first entrance time
of $Y$ into $A$.

Where $V(x)$ and $\sum_y P(x, y) V(y)$ are finite, the drift condition at $x$ reads
$\mathcal{L} V(x) \le c\, V(x)$ for the generator
$\mathcal{L} V(x) = q(x) \bigl( \sum_y P(x, y) V(y) - V(x) \bigr)$ of the chain with exit rates $q$
and jump kernel $P$. The proof conditions on the first step, where
$\mathbb{E}\bigl[e^{-c E_0 / q(x)}\bigr] = q(x) / (q(x) + c)$ cancels the factor $(q(x) + c) / q(x)$
of the drift condition.
