# Holding times of the jump–hold chain

Let $S$ be a set, $q : S \to \mathbb{R}$ a function (the exit rates), $x \in S$ and
$\omega = ((\xi_k, E_k))_{k \in \mathbb{N}}$ a step sequence, with $\xi_k : S \to S$ and
$E_k \in \mathbb{R}$, and let $Y_k = Y_k(x, \omega)$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$: $Y_0 = x$, $Y_{k+1} = \xi_k(Y_k)$. The $n$-th holding time is the real number

$$H_n(x, \omega) = \frac{E_n}{q(Y_n)} .$$

It is meant for positive rates and nonnegative clocks, where it is the time the chain spends in
$Y_n$; under the [input law](input-measure.md) the clocks are
[almost surely nonnegative](ae-clock-nonneg.md). The formula is used as it stands for every real $q$
and $E_n$: with the convention $a / 0 = 0$, $H_n = 0$ when $q(Y_n) = 0$, and $H_n < 0$ when $E_n$
and $q(Y_n)$ have opposite signs.
