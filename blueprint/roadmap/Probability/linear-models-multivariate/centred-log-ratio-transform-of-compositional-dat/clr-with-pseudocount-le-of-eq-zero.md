# Under a pseudocount, a zero count gets the minimal CLR coordinate

Let $\iota$ be a finite set of parts, $c > 0$ a pseudocount and $n = (n_k)_{k \in \iota}$
counts with $n_k \ge 0$ for every $k$, and write $n + c = (n_k + c)_{k \in \iota}$ for the
[pseudocount composition](with-pseudocount.md). If $n_i = 0$ for a part $i$, then
$\operatorname{clr}(n + c)_i \le \operatorname{clr}(n + c)_j$ for every part $j$, where
$\operatorname{clr}$ is the [CLR transform](clr.md). So under the pseudocount rule a zero count
receives the smallest CLR coordinate of the sample; all zero counts share it.
