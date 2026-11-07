# Soundness of Algorithm W

Let $\Gamma$ be a typing context, $e$ an expression and $n$ a
natural number. If Algorithm W, run on $\Gamma$ and $e$ with fresh-variable counter $n$,
succeeds and returns a substitution $s$, a monotype $\tau$ and a counter $n'$, then $e$ has
type $\tau$ in the context $s\Gamma$ obtained by applying $s$ to every type scheme of
$\Gamma$.
