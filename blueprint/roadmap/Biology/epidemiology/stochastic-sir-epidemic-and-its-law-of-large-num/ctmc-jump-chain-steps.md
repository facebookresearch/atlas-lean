# The read-off steps have the clock chain's states as jump chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$, $x \in \iota$, $c$ a
[clock configuration](clock-config.md), $g$ any sequence of auxiliary steps, and $\omega$ the
[steps read off the clock chain](steps.md) started at $x$ with clocks $c$ and auxiliary steps $g$.
For every $n \in \mathbb{N}$, the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
of $\omega$ from $x$ is the state after $n$ jumps:

$$Y_n(x, \omega) = x_n,$$

where $(x_n, c_n)$ are the [state and clocks after $n$ jumps](config.md) from $(x, c)$.
