# Forward variables of a chain CRF

For a chain conditional random field with a finite set
of states, weights in a semiring, unary potentials $u_t(s)$ and transition potentials
$\tau_t(s', s)$ given the observation stream $x$, the forward variables are defined by
$\alpha_0(s) = u_0(s)$ and
$\alpha_{t+1}(s) = \left(\sum_{s'} \alpha_t(s')\, \tau_t(s', s)\right) u_{t+1}(s)$, the sum running
over all states $s'$.

The forward variable $\alpha_t(s)$ is the total weight of the label paths of length $t + 1$ ending
in $s$.
