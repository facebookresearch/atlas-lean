# Moment bound at a time $t \ge 0$ under a Foster–Lyapunov condition

Let $S$ be a countable set with a σ-algebra in which every singleton is measurable, $P$ a jump
kernel on $S$ (a probability mass function $P(x, \cdot)$ on $S$ for each $x \in S$), and
$\mathbb{P}_P$ the [input law](input-measure.md). Let $q : S \to \mathbb{R}$ with $q(x) > 0$ for
every $x \in S$, $c \ge 0$ and $V : S \to [0, \infty)$, and suppose, as for
[non-explosion](ae-tendsto-jump-time-at-top.md):

- the one-step drift condition $q(x) \sum_{y \in S} P(x, y)\, V(y) \le (q(x) + c)\, V(x)$ holds for
  every $x \in S$; each sum is then finite, and the condition reads $\mathcal{L} V \le c\, V$ for
  the generator $\mathcal{L} V(x) = q(x) ( \sum_y P(x, y) V(y) - V(x) )$;
- the rates are bounded on the sublevel sets of $V$: for every $m \ge 0$ there is a real $K$ with
  $q(x) \le K$ whenever $V(x) < m$.

Then for every $x_0 \in S$ and every time $t \ge 0$, the [path](path.md) $X_t(x_0, \omega)$ of the
chain started at $x_0$ satisfies

$$\int V\bigl(X_t(x_0, \omega)\bigr) \, d\mathbb{P}_P(\omega) \le e^{c t}\, V(x_0),$$

a lower Lebesgue integral with values in $[0, \infty]$, so that
$\mathbb{E}_P\bigl[V(X_t)\bigr] \le e^{c t} V(x_0)$ (Meyn and Tweedie 1993, Theorem 2.1(iii)). Since
the chain does not explode, almost surely $X_t = X^{(n)}_t$ for all large $n$, and Fatou's lemma
passes the [bound for the chain stopped after $n$ jumps](lintegral-state-at-le.md) to the limit.
