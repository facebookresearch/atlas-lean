# Drift criterion for non-explosion of a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species and a finite set of reactions, [generator](generator.md) $L$ and
[total propensity](total-rate.md) $\lambda$. Let $V : \mathbb{N}^S \to [0, \infty)$ and $a, b \ge 0$
satisfy:

- the drift bound $L V(x) \le a\, V(x) + b$ at every state $x$;
- for every real $m$ there is a $K$ with $\lambda(x) \le K$ for all states $x$ with $V(x) < m$:
  the total propensity is bounded on each sublevel set $\{V < m\}$.

Then for every initial state $x_0 \in \mathbb{N}^S$, almost surely under the
[law of the steps](input-measure-2.md) (a probability measure), the [jump times](jump-time-2.md)
$T_n$ of the chain started at $x_0$, fictitious jumps at absorbing states included, tend to
$\infty$ as $n \to \infty$. Explosion, infinitely many jumps in a bounded time interval, has
probability $0$ (Foster–Lyapunov criterion; Meyn–Tweedie 1993, Theorem 2.1; Gupta–Briat–Khammash
2014).
