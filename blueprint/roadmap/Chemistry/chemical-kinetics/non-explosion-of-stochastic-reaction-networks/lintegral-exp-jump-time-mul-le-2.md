# Discounted Lyapunov moment bound for a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species and a finite set of reactions, and [generator](generator.md) $L$. Let
$V : \mathbb{N}^S \to [0, \infty)$ and $c \ge 0$ satisfy $L V(x) \le c\, V(x)$ at every state $x$.
Let the step sequence $\omega$ have the [law of the steps](input-measure-2.md) $\mathbb{P}$, a
probability measure, and for a starting state $x_0 \in \mathbb{N}^S$ let $Y_n$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
and $T_n$ the [jump times](jump-time-2.md) started at $x_0$. Then for every $x_0$ and every number
$n \in \mathbb{N}$ of jumps (fictitious jumps at absorbing states included),

$$\mathbb{E}\bigl[e^{-c T_n}\, V(Y_n)\bigr] \le V(x_0),$$

where $\mathbb{E}$ is the lower Lebesgue integral with respect to $\mathbb{P}$ of the nonnegative
integrand, a value in $[0, \infty]$.
