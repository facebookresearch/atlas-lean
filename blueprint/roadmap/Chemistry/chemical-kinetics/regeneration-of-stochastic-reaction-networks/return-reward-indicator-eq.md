# On a return to $x_0$, the excursion spends one holding time at $x_0$

Let $\sigma$ be a set, $q : \sigma \to \mathbb{R}$, $x_0 \in \sigma$, and let
$\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$ be any step sequence ($\xi_n : \sigma \to \sigma$,
$E_n \in \mathbb{R}$); no probability is involved. Let $Y$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md) started at $x_0$, $Y_0 = x_0$,
$Y_{n+1} = \xi_n(Y_n)$, and suppose that it returns to $x_0$: $Y_n = x_0$ for some $n \ge 1$.
Let $\tau_1$ be the first such $n$ (the [visit](visit.md) numbered $1$). Then the
[reward](return-reward.md) of the indicator $\mathbf{1}_{\{x_0\}}$ over the first excursion is
the first holding time:

$$\sum_{i < \tau_1} \mathbf{1}_{\{x_0\}}(Y_i)\, \frac{E_i}{q(Y_i)} = \frac{E_0}{q(x_0)},$$

because only step $0$ of the excursion is at $x_0$. With the convention $E / 0 = 0$ both sides
are $0$ when $q(x_0) = 0$; for the chain, with $q(x_0) > 0$ and nonnegative clocks, the left side
is the time spent at $x_0$ before the first return. Without a return the left side, a reward
over $0$ steps, is $0$.
