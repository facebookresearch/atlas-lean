# Successor equation for the terminal-value return

With $k + 1$ steps remaining, the terminal-value return of a policy $\pi$ in state $s$ is
$r(s, a) + \gamma \sum_{s'} P(s, a, s')\, W_k(s')$ at the action $a = \pi_{k+1}(s)$, where $W_k$ is
the return with $k$ steps remaining.
