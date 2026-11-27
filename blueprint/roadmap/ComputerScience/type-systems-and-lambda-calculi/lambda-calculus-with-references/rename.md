# Renaming preserves typing

Let $\Gamma$ and $\Delta$ be variable contexts, $S$ a store
typing, and $\rho : \mathbb{N} \to \mathbb{N}$ a renaming of variable indices such that whenever
$\Gamma$ assigns type $A$ to variable $x$, $\Delta$ assigns type $A$ to variable $\rho(x)$. If a
term $t$ has type $T$ under $\Gamma$ and $S$, then the term obtained from $t$ by renaming its
variables by $\rho$ has type $T$ under $\Delta$ and $S$.
