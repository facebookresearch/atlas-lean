# Optimal policies with a terminal value

For a finite MDP with stochastic transitions, a nonempty finite set of actions, a discount
$\gamma \ge 0$ and a terminal value $g$, some nonstationary policy (one decision rule for each
number of remaining steps) has terminal-value return equal to the $k$-step value-iteration value
from $g$ at every horizon $k$ and state, and no policy's terminal-value return exceeds that value.
No $\gamma < 1$ is needed, since the horizon is finite.
