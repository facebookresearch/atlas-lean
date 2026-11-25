# Undiscounted Bellman operators are affine

For a Markov decision process with finitely many states and real rewards, and a deterministic stationary policy $\mu$, the undiscounted ($\gamma = 1$) Bellman operator of $\mu$ is affine: $T_\mu J = r_\mu + P_\mu J$, where $r_\mu(s) = r(s, \mu(s))$ and $P_\mu$ is the [transition matrix](transition-matrix.md) of $\mu$.
