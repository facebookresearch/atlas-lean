# Bridge weights sum to the backward variable

For a hidden Markov model with a finite set
of states $S$ and weights in a semiring, observations $x_0, x_1, \dots$, all $k, t \in \mathbb{N}$
and every state $s \in S$, the sum over all states $u \in S$ of the bridge weight from state $s$
at time $t$ to state $u$ at time $t + k$ equals the backward variable $\beta_{k,t}(s)$, the
weight of the observations $x_{t+1}, \dots, x_{t+k}$ given the state $s$ at time $t$.
