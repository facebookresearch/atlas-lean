# Converted terms are well scoped

Let $m$ and $n$ be natural numbers and $t$ a source term
whose list of free indices at binder depth $n$ is empty, that is, $t$ is scoped in $n$ variables.
If $\mathit{acc}$ is a family of target terms indexed by the natural numbers such that
$\mathit{acc}(i)$ is scoped in $m$ for every $i < n$, then the conversion of $t$ in a scope of
$n$ variables with accessors $\mathit{acc}$ is scoped in $m$; in particular, every code body it
contains is scoped in $1$.
