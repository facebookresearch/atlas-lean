# Completeness of Algorithm W

Let $\Gamma$ be a typing context and $n$ a natural number
such that every free type variable of $\Gamma$ is less than $n$. If, for some type substitution
$u$, an expression $e$ has a monotype $\tau'$ in the context $u(\Gamma)$, then Algorithm W
succeeds on $\Gamma$ and $e$ with counter $n$, returning a substitution $s$, a monotype $\tau$
and a new counter $n'$, and there is a type substitution $r$ such that $u(x) = r(s(x))$ for
every type variable $x < n$, and $\tau' = r(\tau)$.

This is the completeness theorem of Damas and Milner.
