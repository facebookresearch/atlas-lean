# Non-explosion of the jump–hold chain under a Foster–Lyapunov condition

Let $S$ be a countable set with a σ-algebra in which every singleton is measurable, $P$ a jump
kernel on $S$ (a probability mass function $P(x, \cdot)$ on $S$ for each $x \in S$), and
$\mathbb{P}_P$ the [input law](input-measure.md). Let $q : S \to \mathbb{R}$ with $q(x) > 0$ for
every $x \in S$, $c \ge 0$ and $V : S \to [0, \infty)$, and suppose:

- the one-step drift condition $q(x) \sum_{y \in S} P(x, y)\, V(y) \le (q(x) + c)\, V(x)$ holds for
  every $x \in S$; each sum is then finite, and the condition reads $\mathcal{L} V \le c\, V$ for
  the generator $\mathcal{L} V(x) = q(x) ( \sum_y P(x, y) V(y) - V(x) )$;
- the rates are bounded on the sublevel sets of $V$: for every $m \ge 0$ there is a real $K$ with
  $q(x) \le K$ whenever $V(x) < m$.

Then for every starting state $x_0 \in S$, for $\mathbb{P}_P$-almost every step sequence $\omega$
the [jump times](jump-time.md) $T_n(x_0, \omega)$ tend to $\infty$ as $n \to \infty$: the jump–hold
chain with exit rates $q$ and jump kernel $P$ does not explode (Foster–Lyapunov criterion; Meyn and
Tweedie 1993, Theorem 2.1).

The proof: fix $t$ and $m > 0$, and let $K$ bound the rates on $\{V < m\}$. Almost surely the clocks
are nonnegative and their partial sums [tend to $\infty$](ae-tendsto-sum-clock.md). For such
$\omega$, if $T_n \le t$ for every $n$ and the chain never entered $\{V \ge m\}$, then
$T_n \ge (E_0 + \dots + E_{n-1}) / \max(K, 1) \to \infty$, a contradiction; so the chain
[enters $\{V \ge m\}$ by time $t$](measure-reach-le.md), which has probability at most
$e^{c t} V(x_0) / m$. Letting $m \to \infty$ shows that $T_n \le t$ for every $n$ has probability
$0$.
