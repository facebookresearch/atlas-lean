# Law of the steps driving a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species and a finite set of reactions, and let $P$ be its [jump kernel](jump-pmf.md). The law of
the steps driving its jump–hold chain is the [input law of the jump–hold chain](input-measure.md)
with kernel $P$ on the countable state space $\mathbb{N}^S$, in which every set is measurable. It
is the probability measure on step sequences $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$, with
maps $\xi_n : \mathbb{N}^S \to \mathbb{N}^S$ and clocks $E_n \in \mathbb{R}$, under which the steps
$(\xi_n, E_n)$ are independent and identically distributed, each $\xi_n$ has independent
coordinates $\xi_n(x)$ with law $P(x, \cdot)$, and $E_n$ is an exponential clock of rate $1$
independent of $\xi_n$.
