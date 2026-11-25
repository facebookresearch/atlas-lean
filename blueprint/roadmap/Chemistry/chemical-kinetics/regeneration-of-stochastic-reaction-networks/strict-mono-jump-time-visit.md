# With every visit, positive rates and clocks make visit times increase

Let $\sigma$ be a set, $q : \sigma \to \mathbb{R}$ with $q(y) > 0$ for every $y$,
$x_0, x \in \sigma$, and $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$ a step sequence
($\xi_n : \sigma \to \sigma$) whose clocks are all positive, $E_n > 0$ for every $n$. Let $Y$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$, $T_m = \sum_{i < m} E_i / q(Y_i)$ its
[jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md), and $\tau_n$ the step
of the [$n$-th visit](visit.md) (counting from $0$) to $x_0$. If every visit happens,
$\tau_n < \infty$ for every $n$, then the times of the successive visits strictly increase:

$$T_{\tau_0} < T_{\tau_1} < T_{\tau_2} < \cdots.$$

No probability is involved. A missing visit would count as step $0$, so the hypothesis that all
visits happen cannot be dropped.
