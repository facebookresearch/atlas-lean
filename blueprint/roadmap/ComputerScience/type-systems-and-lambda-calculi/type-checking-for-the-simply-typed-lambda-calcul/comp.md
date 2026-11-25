# Agreement of renamings is preserved by composition

Let $\rho$ be a typed renaming
from context $\Gamma$ to $\Delta$, let $\sigma$ be a typed renaming from $\Delta$ to $\Xi$,
and let $r, s : \mathbb{N} \to \mathbb{N}$. If $\rho$ agrees with $r$ and $\sigma$ agrees with
$s$, then the composite renaming that applies $\rho$ and then $\sigma$ agrees with
$s \circ r$.
