# Fixing the top variable of an ordered node

Let $t$ be a node testing the variable $v$
with low child $\ell$ and high child $h$, and suppose $t$ is ordered from some $n \in \mathbb{N}$.
For every assignment $\sigma$ of Boolean values to the variables and every Boolean $b$, the value
of $t$ under $\sigma[v \mapsto b]$ (the assignment $\sigma$ with $v$ set to $b$) is the value of
$h$ under $\sigma$ if $b$ is true, and the value of $\ell$ under $\sigma$ if $b$ is false.
