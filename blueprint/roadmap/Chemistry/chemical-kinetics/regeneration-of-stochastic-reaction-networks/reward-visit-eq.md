# Rewards up to successive visits telescope into the cycle rewards

Let $\sigma$ be a set, $q, g : \sigma \to \mathbb{R}$ any functions, $x_0, x \in \sigma$, and
$\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$ any step sequence. For the jump chain $Y$ started at
$x$ let $R(m) = \sum_{i < m} g(Y_i) E_i / q(Y_i)$ be the [reward](reward.md) collected by $g$
in the first $m$ steps (with $E / 0 = 0$), $\tau_k$ the step of the [$k$-th visit](visit.md)
to $x_0$, and $C_k = R(\tau_{k+1}) - R(\tau_k)$ the [reward of the $k$-th cycle](cycle-sum.md),
where a missing visit, $\tau_k = \infty$, counts as step $0$. Then for every
$n \in \mathbb{N}$

$$R(\tau_n) = R(\tau_0) + \sum_{k < n} C_k.$$

The identity is a telescoping sum; it holds for every step sequence, whether or not the visits
happen.
