# Non-explosion with a coercive Lyapunov function

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species, a finite set of reactions and [generator](generator.md) $L$. Let
$V : \mathbb{N}^S \to [0, \infty)$ and $a, b \ge 0$ satisfy, at every state $x$, the drift bound
$L V(x) \le a\, V(x) + b$ and the coercivity bound $\sum_{s \in S} x_s \le V(x)$. Then for every
initial state $x_0 \in \mathbb{N}^S$, almost surely under the [law of the steps](input-measure-2.md),
the [jump times](jump-time-2.md) of the chain started at $x_0$ tend to $\infty$: the chain does not
explode.

Coercivity makes the total propensity
[bounded on each sublevel set of $V$](bdd-rate-of-coercive.md), so this is a special case of the
[drift criterion for non-explosion](ae-tendsto-jump-time-at-top-2.md).
