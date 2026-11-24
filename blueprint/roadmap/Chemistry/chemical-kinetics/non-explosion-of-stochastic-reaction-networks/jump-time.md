# Jump times of the jump–hold chain

Let $S$ be a set, $q : S \to \mathbb{R}$, $x \in S$ and $\omega = ((\xi_k, E_k))_{k \in \mathbb{N}}$
a step sequence, with [holding times](holding-time.md) $H_k = E_k / q(Y_k)$, where $Y_k$ is the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$; with the convention $a / 0 = 0$, a state with $q(Y_k) = 0$ contributes $H_k = 0$.
The $n$-th jump time is the real number

$$T_n(x, \omega) = H_0 + H_1 + \dots + H_{n-1}, \qquad T_0 = 0 .$$

For positive rates and nonnegative clocks the holding times are nonnegative, so the jump times are
[nonnegative](jump-time-nonneg.md) and nondecreasing in $n$, and $T_n$ is the time of the $n$-th
jump.
