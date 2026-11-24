# Typed service templates retype at any well-formed completed context

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$, $\Theta$ ownership contexts
and $p$ a service template for $\Gamma$ with $\Gamma; \Delta \vdash_n p$. If every capability of
$\Theta$ has head $\mathrm{end}$, every endpoint of $\Theta$ has a name scoped at depth $n$ and
$\Theta$ is separated from $\Gamma$, then $\Gamma; \Theta \vdash_n p$.
