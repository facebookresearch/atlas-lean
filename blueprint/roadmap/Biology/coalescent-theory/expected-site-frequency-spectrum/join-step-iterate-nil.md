# Iterating the join step keeps the value at the empty list

For every natural number $j$ and every real function $g$ on lists of natural numbers,

$$(J^{j} g)(\varnothing) = g(\varnothing),$$

where $\varnothing$ is the empty list and $J$ is the [transition operator of random joining](join-step.md).
Indeed the empty list has fewer than two entries, so $(Jh)(\varnothing) = h(\varnothing)$ for every
$h$.
