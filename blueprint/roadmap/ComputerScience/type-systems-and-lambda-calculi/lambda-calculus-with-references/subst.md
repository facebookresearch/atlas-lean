# Parallel substitution preserves typing

Let $\Gamma$ and $\Delta$ be variable contexts,
$S$ a store typing, and $\sigma$ a substitution sending each variable index to a term, such
that whenever $\Gamma$ assigns type $A$ to variable $x$, the term $\sigma(x)$ has type $A$ under
$\Delta$ and $S$. If a term $t$ has type $T$ under $\Gamma$ and $S$, then the term obtained from
$t$ by applying $\sigma$ has type $T$ under $\Delta$ and $S$.
