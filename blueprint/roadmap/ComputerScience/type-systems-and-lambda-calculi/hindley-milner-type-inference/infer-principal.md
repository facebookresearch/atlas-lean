# Principal types

Let $e$ be a closed expression for which type inference returns the type $\tau$. Then $e$ has type $\tau$ in the empty context, and every type $\tau'$ of $e$ in the empty context is a substitution instance of $\tau$: $\tau' = r(\tau)$ for some substitution $r$ of types for type variables.
