# Path of a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set of reactions and [holding rate](hold-rate.md) $q$. For a starting state
$x_0 \in \mathbb{N}^S$, a step sequence $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$ and a time
$t \in \mathbb{R}$, the path $X_t$ of $N$ is the [path of the jump–hold chain](path.md) with holding
rates $q$ started at $x_0$. With $Y_0 = x_0$, $Y_{n+1} = \xi_n(Y_n)$ the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
and $T_n$ the [jump times](jump-time-2.md):

- $X_t = x_0$ for $t < 0$;
- if all clocks $E_n$ are nonnegative, $X_t = Y_k$ for $T_k \le t < T_{k+1}$;
- if $T_n \le t$ for every $n$ (explosion at or before time $t$), $X_t = x_0$, a value with no
  meaning in the model.

The last case has probability $0$ under the [law of the steps](input-measure-2.md) when $S$ is
finite and some $V : \mathbb{N}^S \to [0, \infty)$ satisfies $L V \le a V + b$ for the
[generator](generator.md) $L$ and some $a, b \ge 0$, with the [total propensity](total-rate.md)
bounded on each sublevel set $\{V < m\}$
([the jump times are then almost surely unbounded](ae-forall-exists-lt-jump-time.md)).
