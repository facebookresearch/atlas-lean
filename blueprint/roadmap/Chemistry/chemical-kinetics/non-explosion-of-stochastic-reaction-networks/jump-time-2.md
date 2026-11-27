# Jump times of a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set of reactions and [holding rate](hold-rate.md) $q$ (the total propensity, or $1$ at
absorbing states). For a starting state $x_0 \in \mathbb{N}^S$ and a step sequence
$\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$, with maps $\xi_n : \mathbb{N}^S \to \mathbb{N}^S$ and
clocks $E_n \in \mathbb{R}$, let $Y_0 = x_0$, $Y_{n+1} = \xi_n(Y_n)$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md).
The $n$-th jump time is the [jump time of the jump–hold chain](jump-time.md) with rates $q$:

$$T_n = \sum_{k=0}^{n-1} \frac{E_k}{q(Y_k)}, \qquad \text{so } T_0 = 0.$$

The jump times count the fictitious jumps $x \mapsto x$ at absorbing states. The formula holds for
every step sequence: if some clocks are negative, $T_n$ need not increase with $n$. With finitely
many species, under the [law of the steps](input-measure-2.md) the clocks are almost surely
nonnegative.
