# Higher reflexive stabilizations

For a list of natural-number weights
$q = (q_1, \dots, q_n)$ and a natural number $m$, the $m$th reflexive stabilization of $q$ is the
list $\mathrm{rs}(q, m) = (1^k, q_1, \dots, q_n)$ obtained by prepending $k$ entries equal to $1$,
where $k = \mathrm{rsn}(q) + (m - 1) \operatorname{lcm}(q)$. Here $\mathrm{rsn}(q)$ is the
reflexive stabilization number of $q$, $\operatorname{lcm}(q)$ is the least common multiple of
the weights (equal to $1$ for the empty list), and the subtraction $m - 1$ is truncated at $0$,
so $\mathrm{rs}(q, 0) = \mathrm{rs}(q, 1)$.

## Sources

- Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 10.
