# Flat closure conversion preserves scoping

Let $t$ be a raw term, $m$ a natural number
and $\mathrm{acc}$ a map from natural numbers to target terms. If $\mathrm{acc}(i)$ is scoped in
$m$ for every free variable $i$ of $t$, then the flat conversion of $t$ with accessors
$\mathrm{acc}$ is scoped in $m$. In particular every code body it contains is scoped in $1$, so
refers only to its parameter.
