# Forward-backward identity

For a hidden Markov model with a finite set of states $S$ and
weights in a semiring, observations $x_0, x_1, \dots$, times $t, k \in \mathbb{N}$ and a state
$s \in S$, the joint weight of the observations $x_0, \dots, x_{t+k}$ and the state $s$ at time
$t$ equals $\alpha_t(s)\,\beta_{k,t}(s)$, the forward variable $\alpha_t(s)$ (the weight of
$x_0, \dots, x_t$ with the state at time $t$ equal to $s$) times the backward variable
$\beta_{k,t}(s)$ (the weight of $x_{t+1}, \dots, x_{t+k}$ given the state $s$ at time $t$).
