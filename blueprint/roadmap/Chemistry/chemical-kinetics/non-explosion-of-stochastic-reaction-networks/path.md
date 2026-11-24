# Path of the jump–hold chain

Let $S$ be a set, $q : S \to \mathbb{R}$, $x \in S$ and $\omega$ a step sequence, with
[jump times](jump-time.md) $T_n = T_n(x, \omega)$ and
[states at time $s$ of the chain stopped after $n$ jumps](state-at.md)
$X^{(n)}_s = X^{(n)}_s(x, \omega)$. The path at a time $s \in \mathbb{R}$ is

$$X_s(x, \omega) = \begin{cases} X^{(N)}_s & \text{if } s < T_n \text{ for some } n,
\text{ where } N \text{ is the least such } n, \\
x & \text{if } T_n \le s \text{ for every } n. \end{cases}$$

Since $T_0 = 0$, $X_s = x$ at every time $s < 0$
([path before time $0$](../regeneration-of-stochastic-reaction-networks/path-of-neg.md)). For
positive rates and nonnegative clocks, $X_s = Y_k$ when $T_k \le s < T_{k+1}$, where $Y_k$ is the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
([path between jump times](path-eq-ctmc-jump-chain.md)); the second case then means that $s$ is at
or after the explosion time $\sup_n T_n$, where the value $x$ is a convention.

For a fixed $s$, the second case has probability $0$ under the [input law](input-measure.md) of a
jump kernel $P$ whenever the chain [does not explode](ae-tendsto-jump-time-at-top.md): for example
when $S$ is countable with measurable singletons, $q > 0$, and some $V : S \to [0, \infty)$
satisfies the one-step drift condition $q(x) \sum_y P(x, y) V(y) \le (q(x) + c) V(x)$ at every $x$,
for some $c \ge 0$, with $q$ bounded above on each sublevel set $\{V < m\}$.
