# Good-suffix table of Boyer–Moore preprocessing

Let $p = p_0 \cdots p_{m-1}$ be a
pattern over the alphabet $\{0, \dots, \sigma - 1\}$, let $G$ be the good-suffix table computed
by the Boyer–Moore preprocessing of $p$, and let $i < m$. Call a positive integer $e$ an
admissible shift at $i$ if $p_{t - e} = p_t$ for every $t < m$ with $i < t$ and $e \le t$, and
$p_{i - e} \ne p_i$ whenever $e \le i$. Then $1 \le G_i \le m$ and $G_i$ is the least
admissible shift at $i$.

After a mismatch at position $i$, shifting by $G_i$ keeps the matched suffix
$p_{i+1} \cdots p_{m-1}$ aligned where it overlaps and, when $G_i \le i$, places the symbol
$p_{i - G_i} \ne p_i$ under the mismatched position.
