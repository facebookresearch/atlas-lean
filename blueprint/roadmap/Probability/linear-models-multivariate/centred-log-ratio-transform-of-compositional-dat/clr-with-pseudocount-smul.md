# Rescaling counts and pseudocount together leaves the CLR unchanged

Let $\iota$ be a finite set of parts, $c > 0$ a pseudocount, $t > 0$ and
$n = (n_i)_{i \in \iota}$ counts with $n_i \ge 0$ for every $i$. Rescaling both the counts and
the pseudocount by $t$ does not change the [CLR transform](clr.md) of the
[pseudocount composition](with-pseudocount.md):

$$\operatorname{clr}(t n + t c) = \operatorname{clr}(n + c),$$

where $n + c = (n_i + c)_{i \in \iota}$ and $t n + t c = (t n_i + t c)_{i \in \iota}$.
