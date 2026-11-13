# Number of representations as a sum of three squares

For a natural number $n$, $r_3(n)$
is the number of ordered triples $(x, y, z)$ of integers in the interval $[-n, n]$ with
$x^2 + y^2 + z^2 = n$. Every integer solution of $x^2 + y^2 + z^2 = n$ lies in this interval
(also for $n = 0$), so $r_3(n)$ is the number of all ordered integer solutions.

## Sources

- Primary source: E. T. Mortenson, arXiv:1702.01627v2, `Mortenson-AC-Gauss-arxiv-v2.tex` lines 127-131 defining `rₛ` by `Rₛ(q) = ∑ₙ rₛ(n) (-q) ^ n = (∑_{m ∈ ℤ} (-1) ^ m q ^ (m ^ 2)) ^ s` (ordered signed integer tuples). Ranked source arXiv:2307.05244 `main.tex` lines 78-82 identifies the equation `x ^ 2 + y ^ 2 + z ^ 2 = n`.
