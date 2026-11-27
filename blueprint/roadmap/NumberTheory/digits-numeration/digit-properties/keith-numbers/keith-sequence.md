# Keith sequence

Given a list $d = (d_0, \dots, d_{k-1})$ of natural numbers, the Keith
sequence of $d$ is the sequence $(a_m)_{m \ge 0}$ with $a_m = d_m$ for $m < k$ and
$a_m = \sum_{i=m-k}^{m-1} a_i$ for $m \ge k$: after the initial entries, each term is the sum of
the preceding $k$ terms.
