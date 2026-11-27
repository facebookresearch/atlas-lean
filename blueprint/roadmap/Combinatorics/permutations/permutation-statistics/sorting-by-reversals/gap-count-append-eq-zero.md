# No gaps in a concatenation means none in the parts or at the junction

For nonempty lists of integers $\ell$ and $\ell'$, let $a$ be the last entry of $\ell$ and $b$
the first entry of $\ell'$. If the [gap count](gap-count.md) of the concatenation $\ell\,\ell'$
is $0$, then $g(\ell) = 0$, $g(\ell') = 0$ and the [gap indicator](is-gap.md) $\gamma(a, b)$ is
$0$, that is, $|b - a| = 1$. This follows from $g(\ell\,\ell') = g(\ell) + g(\ell') + \gamma(a, b)$.
