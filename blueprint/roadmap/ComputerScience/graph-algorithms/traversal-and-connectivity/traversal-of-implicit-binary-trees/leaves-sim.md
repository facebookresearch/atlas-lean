# Invariant-restricted step transport of the frontier

Let $\sigma'$ be a branching step on states $S'$, $\sigma$ a branching step on states $S$,
$f : S' \to S$ a map and $I$ a property of states in $S'$. Assume that for every $s \in S'$ with
$I(s)$, $f(s)$ is terminal for $\sigma$ exactly when $s$ is terminal for $\sigma'$, and if $s$
branches into $(l, h)$ then $f(s)$ branches into $(f(l), f(h))$; and that whenever $I(s)$ holds
and $s$ branches into $(l, h)$, both $I(l)$ and $I(h)$ hold. Then for every depth $k$ and every
$s \in S'$ with $I(s)$:

1. the list of images under $f$ of the frontier of $s$ for $\sigma'$ cut at depth $k$ is the
   frontier of $f(s)$ for $\sigma$ cut at depth $k$;
2. every state $x$ in the frontier of $s$ for $\sigma'$ cut at depth $k$ satisfies $I(x)$.
