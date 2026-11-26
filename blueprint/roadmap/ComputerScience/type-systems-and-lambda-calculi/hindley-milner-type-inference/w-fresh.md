# Freshness invariants of Algorithm W

Let $\Gamma$ be a typing context and $n$ a
natural number such that every free type variable of $\Gamma$ is less than $n$. If Algorithm W
succeeds on $\Gamma$ and an expression $e$ with counter $n$, returning a substitution $s$, a
monotype $\tau$ and a new counter $n'$, then $n \le n'$, every type variable of $\tau$ is less
than $n'$, and for every type variable $x < n$ every type variable of $s(x)$ is less than
$n'$.
