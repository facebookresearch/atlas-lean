# Law of the i.i.d. step sequence driving the jump–hold chain

Let $S$ be a set with a σ-algebra, $P$ a jump kernel on $S$ (a probability mass function
$P(x, \cdot)$ on $S$ for each $x \in S$), and $\mu_P$ the [law of one step](step-measure.md)
$(\xi, E)$, under which the coordinates $\xi(x) \sim P(x, \cdot)$ are independent and the clock
$E \sim \operatorname{Exp}(1)$ is independent of them. The input law is the infinite product measure

$$\mathbb{P}_P = \bigotimes_{n \in \mathbb{N}} \mu_P$$

on step sequences $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$, with $\xi_n : S \to S$ and
$E_n \in \mathbb{R}$, for the product σ-algebra. It is a probability measure under which the steps
$(\xi_n, E_n)$ are independent, each with law $\mu_P$. These steps drive the jump–hold chain: its
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$ is $Y_0 = x$, $Y_{n+1} = \xi_n(Y_n)$, and its [holding times](holding-time.md) are
$E_n / q(Y_n)$ for exit rates $q$.
