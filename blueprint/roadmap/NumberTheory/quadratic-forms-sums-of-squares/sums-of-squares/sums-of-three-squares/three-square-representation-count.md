# Number of representations as a sum of three squares

For a natural number $n$, $r_3(n)$
is the number of ordered triples $(x, y, z)$ of integers in the interval $[-n, n]$ with
$x^2 + y^2 + z^2 = n$. Every integer solution of $x^2 + y^2 + z^2 = n$ lies in this interval
(also for $n = 0$), so $r_3(n)$ is the number of all ordered integer solutions.

## Sources

- Primary source: E. T. Mortenson, arXiv:1702.01627v2, `Mortenson-AC-Gauss-arxiv-v2.tex` lines 127-131 (span SHA-256 `2f2704bfc2f61e5fc50b27df3e14542a0ef19ddd4c7580c7f589f23d38ccff12`, file SHA-256 `13bccb58b9397a2bf3fb713779f0d76623513aec5c0f313a3cf95cf8466b5cf3`) defining `rₛ` by `Rₛ(q) = ∑ₙ rₛ(n) (-q) ^ n = (∑_{m ∈ ℤ} (-1) ^ m q ^ (m ^ 2)) ^ s` (ordered signed integer tuples). Ranked source arXiv:2307.05244 `main.tex` lines 78-82 (span SHA-256 `08a4b80a1e84386e7dc97f8d87e1a4f84945d55022722618d59beca2382f9942`) identifies the equation `x ^ 2 + y ^ 2 + z ^ 2 = n`.
