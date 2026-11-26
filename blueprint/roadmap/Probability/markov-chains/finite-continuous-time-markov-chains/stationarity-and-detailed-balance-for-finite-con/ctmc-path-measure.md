# Path law of a finite continuous-time Markov chain with a random start

Let $Q$ be a rate matrix on a finite state set $S$ with its discrete measurable structure. For each state $i$, let $\mathbb P_i$ be the pushforward of the [driving step law](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md) by the [path started at $i$](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md). The path space is the set of functions $[0,\infty)\to S$ with its product σ-algebra.

For real weights $\pi_i$, the mixture is $\mathbb P_\pi=\sum_i\max(\pi_i,0)\,\mathbb P_i$: the nonnegative measure coefficient in Lean is `ENNReal.ofReal (π i)`. If $\pi$ is a probability vector, the coefficients are $\pi_i$ and the mixture is a probability measure. If also $\pi Q=0$, the [stationarity theorem](stationary-initial-law-gives-a-stationary-process.md) identifies the one-time marginals and proves invariance of the finite-dimensional laws under time shifts.
