# Paths through two fixed states

For a hidden Markov model with a finite set of states $S$
and weights in a semiring, observations $x_0, x_1, \dots$, all $k, t \in \mathbb{N}$ and states
$s, u \in S$, the sum of the path weights $p_{t+k}(z)$ over all state paths
$z = (z_0, \dots, z_{t+k})$ in $S$ with $z_t = s$ and $z_{t+k} = u$ equals
$\alpha_t(s)\, b_{k,t}(s, u)$. Here $p_{t+k}(z)$ is the joint weight of the path $z$ and the
observations $x_0, \dots, x_{t+k}$, $\alpha_t(s)$ is the forward variable and $b_{k,t}(s, u)$ is
the bridge weight from state $s$ at time $t$ to state $u$ at time $t + k$.
