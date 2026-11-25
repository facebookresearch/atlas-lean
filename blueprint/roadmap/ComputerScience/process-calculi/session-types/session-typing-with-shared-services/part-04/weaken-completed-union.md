# Weakening runtime typing by a disjoint completed context

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$, $\Theta$ ownership contexts
with disjoint domains and $p$ a process. Suppose every capability of $\Theta$ has head
$\mathrm{end}$, every endpoint of $\Theta$ has a name scoped at depth $n$ and $\Theta$ is separated
from $\Gamma$. If $\Gamma; \Delta \vdash_n p$, then $\Gamma; \Delta \cup \Theta \vdash_n p$.
