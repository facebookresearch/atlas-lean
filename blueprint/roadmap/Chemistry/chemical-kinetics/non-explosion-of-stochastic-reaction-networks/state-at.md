# State at time $s$ of the jump–hold chain stopped after $n$ jumps

Let $S$ be a set and $q : S \to \mathbb{R}$. For $n \in \mathbb{N}$, a state $x \in S$, a time
$s \in \mathbb{R}$ and a step sequence $\omega = ((\xi_k, E_k))_{k \in \mathbb{N}}$, the state
$X^{(n)}_s(x, \omega) \in S$ is defined by recursion on the first step:

$$X^{(0)}_s(x, \omega) = x, \qquad
X^{(n+1)}_s(x, \omega) = \begin{cases} x & \text{if } s < E_0 / q(x), \\
X^{(n)}_{s - E_0 / q(x)}\bigl(\xi_0(x), \theta_1 \omega\bigr) & \text{otherwise,} \end{cases}$$

where $\theta_1 \omega = (\omega_1, \omega_2, \dots)$ is the
[shift](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
of $\omega$ by one step. With the convention $a / 0 = 0$, the first holding time $E_0 / q(x)$ is $0$
when $q(x) = 0$, so at a time $s \ge 0$ such a state is left at once:
$X^{(n+1)}_s(x, \omega) = X^{(n)}_s(\xi_0(x), \theta_1 \omega)$.

For positive rates and nonnegative clocks this is the chain started at $x$ and stopped after $n$
jumps. With the [jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y_k$ and the [jump times](jump-time.md) $T_k$ started at $x$, at a time $s \ge 0$ the state is
$Y_k$ when $T_k \le s < T_{k+1}$ for some $k < n$
([between jump times](state-at-eq-ctmc-jump-chain.md)), and $Y_n$ when $T_n \le s$. At a time
$s < 0$ it is $x$.
