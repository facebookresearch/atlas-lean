# First-step decomposition of the jump chain

Let $S$ be a set, $x \in S$ and $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$ a step sequence, with
$\xi_n : S \to S$ and $E_n \in \mathbb{R}$, and let $Y_j(x, \omega)$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$. For every $j \in \mathbb{N}$,

$$Y_{j+1}(x, \omega) = Y_j\bigl(\xi_0(x), \theta_1 \omega\bigr),$$

where $\theta_1 \omega = (\omega_1, \omega_2, \dots)$ is the
[shift](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
of $\omega$ by one step: one step later, the jump chain is the jump chain of the shifted steps
started at the first jump $\xi_0(x)$. Since $Y_1(x, \omega) = \xi_0(x)$, this is the case $n = 1$
of the identity $Y_m(Y_n(x, \omega), \theta_n \omega) = Y_{n+m}(x, \omega)$ for the
[jump chain of the shifted steps](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain-shift.md).
