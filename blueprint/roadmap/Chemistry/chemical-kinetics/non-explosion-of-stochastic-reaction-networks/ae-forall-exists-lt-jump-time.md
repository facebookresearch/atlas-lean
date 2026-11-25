# Under the drift criterion, the jump times are almost surely unbounded

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species and a finite set of reactions, [generator](generator.md) $L$ and
[total propensity](total-rate.md) $\lambda$. Let $V : \mathbb{N}^S \to [0, \infty)$ and $a, b \ge 0$
satisfy the drift bound $L V(x) \le a\, V(x) + b$ at every state $x$, and suppose that for every
real $m$ there is a $K$ with $\lambda(x) \le K$ for all states $x$ with $V(x) < m$. Then for every
initial state $x_0 \in \mathbb{N}^S$, almost surely under the [law of the steps](input-measure-2.md),
every real time $t$ is exceeded by some [jump time](jump-time-2.md) of the chain started at $x_0$:
$t < T_n$ for some $n$. So, almost surely, the [path](path-2.md) at every time $t$ is the state
reached after finitely many jumps, not the junk value $x_0$ that the path takes after an
explosion.
