# Terminal-value return of a policy

Terminal-value return of a nonstationary policy $\pi$, where $\pi_k(s)$ is the action taken with $k$
steps remaining in state $s$, for a terminal value $g$: $W_0 = g$ and
$W_{k+1}(s) = r(s, a) + \gamma \sum_{s'} P(s, a, s')\, W_k(s')$ at the policy's action
$a = \pi_{k+1}(s)$. The transition weights $P(s, a, s')$ and the discount $\gamma$ are arbitrary
reals. For stochastic transitions, a finite nonempty set of actions and $\gamma \ge 0$, the optimal
terminal-value return is the value-iteration value from $g$.
