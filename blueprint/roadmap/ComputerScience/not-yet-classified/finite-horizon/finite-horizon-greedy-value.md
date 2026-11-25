# Backward recursion attains the finite-horizon value

For a Markov decision process with finitely many states, a finite nonempty action set and any discount $\gamma$, let $V_0 = 0$ and $V_{k+1}$ be one Bellman optimality update of $V_k$. The policy that, with $k + 1$ steps remaining, acts greedily with respect to $V_k$ has expected discounted $k$-step return equal to $V_k(s)$, for every horizon $k$ and state $s$.
