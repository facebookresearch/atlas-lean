# Fixed pseudocount: scaling by t ≠ 1 keeps the CLR iff counts are equal

Let $\iota$ be a finite set of parts, $c > 0$ a fixed pseudocount, $t > 0$ with $t \ne 1$, and
$n = (n_i)_{i \in \iota}$ counts with $n_i \ge 0$ for every $i$. Rescaling the counts by $t$
but not the pseudocount leaves the [CLR transform](clr.md) of the
[pseudocount composition](with-pseudocount.md) unchanged,

$$\operatorname{clr}(t n + c) = \operatorname{clr}(n + c),$$

if and only if all counts are equal: $n_i = n_j$ for all parts $i, j$. Here
$n + c = (n_i + c)_{i \in \iota}$ and $t n + c = (t n_i + c)_{i \in \iota}$. So with a fixed
pseudocount the CLR of counts is not scale invariant in general. The condition $t \ne 1$ is
needed: for $t = 1$ both sides agree for all counts.
