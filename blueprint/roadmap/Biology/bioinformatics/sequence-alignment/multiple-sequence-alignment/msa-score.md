# Sum-of-pairs score

Fix a score $\sigma(a, b) \in \mathbb{Z}$ for each pair of letters
$a, b$ and a gap score $g \in \mathbb{Z}$. For two entries $x, y$, each a letter or a gap, let
$s(x, y) = \sigma(x, y)$ if both are letters, $s(x, y) = g$ if exactly one is a gap, and
$s(x, y) = 0$ if both are gaps. The sum-of-pairs score of a multiple alignment $A$ of $k$
sequences is the sum, over the columns $c$ of $A$, of $\sum_{0 \le i < j < k} s(c_i, c_j)$,
where $c_i$ is the entry of $c$ in row $i$.
