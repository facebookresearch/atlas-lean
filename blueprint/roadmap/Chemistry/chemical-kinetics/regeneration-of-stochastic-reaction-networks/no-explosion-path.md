# Jump times tending to infinity bound molecule counts up to each time

Let $M$ be a [stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) with finite sets $S$ of
species and $\rho$ of reactions, $x \in \mathbb{N}^S$, and $\mathbb{P}$ the
[law of the steps](../non-explosion-of-stochastic-reaction-networks/input-measure-2.md) of its jump–hold chain. If almost surely the
[jump times](../non-explosion-of-stochastic-reaction-networks/jump-time-2.md) $T_n$ of the chain started at $x$ tend to $\infty$, then
its [path](../non-explosion-of-stochastic-reaction-networks/path-2.md) $X$ does not explode in the sense of
[non-explosion of a path process](../ergodic-theorem-for-complex-balanced-reaction-ne/no-explosion.md): almost surely, for every real
$t$, the total molecule count $\sum_{i \in S} X_s(i)$ is bounded above for $s \in [0, t]$ (the
interval is empty when $t < 0$). Before time $t$ only the finitely many states $Y_0, \dots, Y_{n-1}$
of the jump chain occur, where $T_n > t$.
