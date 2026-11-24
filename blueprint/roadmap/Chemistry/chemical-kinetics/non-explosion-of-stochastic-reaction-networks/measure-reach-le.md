# Under a drift condition, a bound on reaching $\{V \ge m\}$ by time $t$

Let $S$ be a countable set with a σ-algebra in which every singleton is measurable, $P$ a jump
kernel on $S$ (a probability mass function $P(x, \cdot)$ on $S$ for each $x \in S$), and
$\mathbb{P}_P$ the [input law](input-measure.md). Let $q : S \to \mathbb{R}$ with $q(x) > 0$ for
every $x \in S$, $c \ge 0$ and $V : S \to [0, \infty)$ satisfy the one-step drift condition

$$q(x) \sum_{y \in S} P(x, y)\, V(y) \le \bigl(q(x) + c\bigr)\, V(x) \qquad
\text{for every } x \in S.$$

Let $m > 0$, $t \in \mathbb{R}$ and $x_0 \in S$, with
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y_k = Y_k(x_0, \omega)$ and [jump times](jump-time.md) $T_k = T_k(x_0, \omega)$. The event that the
chain enters $\{V \ge m\}$ by time $t$,

$$R = \bigl\{\omega : \text{for some } k,\ V(Y_k) \ge m,\ V(Y_j) < m \text{ for every } j < k
\text{ and } T_k \le t\bigr\},$$

in which the first entrance into $\{V \ge m\}$ happens at a jump time at most $t$, satisfies

$$\mathbb{P}_P(R) \le \frac{e^{c t}\, V(x_0)}{m}.$$

The proof applies Markov's inequality to the [stopped discounted process](discounted-stop.md) with
$A = \{V \ge m\}$, whose mean is [at most $V(x_0)$](lintegral-discounted-stop-le.md).
