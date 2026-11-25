# A reversal inside a list leaves an appended last entry in place

For a list of integers $X$ of length $m$, an integer $c$ and natural numbers $i \le j < m$, the
[reversal](rev-block.md) of positions $i$ to $j$ of the list $X$ followed by $c$ is
$\operatorname{rev}_{i,j}(X)$ followed by $c$: a reversal that stays inside $X$ does not move an
entry appended after it.
