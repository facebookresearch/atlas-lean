# Sum-of-pairs score of a column

Let $\sigma$ assign an integer score to each pair of
letters and let $g$ be an integer gap score. For a column $c$ of a multiple alignment of $k$
sequences, which gives each row $r < k$ either a letter or a gap $c_r$, the sum-of-pairs score of
$c$ is $\sum_{i < j < k} s(c_i, c_j)$, where $s$ is the pairwise column score: $\sigma(a, b)$ for
letters $a$ and $b$, $g$ for a letter against a gap, and $0$ for two gaps.
