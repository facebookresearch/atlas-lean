# Every code is list decodable up to the Johnson radius

Let $C$ be a code of length $n$ whose distinct codewords are at Hamming distance at least
$d \le n$, and let $e \le n$ satisfy $n(n-d) < (n-e)^2$, that is $e < n - \sqrt{n(n-d)}$. Then $C$
is [list decodable](is-list-decodable.md) from $e$ errors with list size $n d$.

In relative terms: a code of relative distance $\delta$ is list decodable with polynomial list
size from any fraction of errors below $1 - \sqrt{1 - \delta}$, whatever the alphabet. This is the
strict case of Theorem 7.3.3 of Guruswami, Rudra and Sudan, with list size $n d$ instead of
$q n d$. Their Theorem 7.3.1 gives the larger alphabet-dependent radius
$J_q(\delta) = (1 - 1/q)(1 - \sqrt{1 - q\delta/(q-1)})$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorems 7.3.1 and 7.3.3.
