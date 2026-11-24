# Completeness of type inference for closed expressions

If an expression $e$ has a
monotype $\tau'$ in the empty context, then type inference succeeds on $e$ and returns a
monotype $\tau$ of which $\tau'$ is a substitution instance: $\tau' = r(\tau)$ for some type
substitution $r$.
