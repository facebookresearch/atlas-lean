# Johnson bound, list size $n d$

Under the hypotheses of the [Johnson bound](johnson-bound.md) ($e \le n$, $d \le n$, words pairwise
at distance at least $d$, all within distance $e$ of $y$, and $n(n-d) < (n-e)^2$), the set has at
most $n d$ words: the denominator $(n-e)^2 - n(n-d)$ is a positive integer and the numerator
$n (d - e)$ is at most $n d$.

Guruswami, Rudra and Sudan (Theorem 7.3.3) state the list size $q n d$; the bound $n d$ is
smaller. Their Exercise 7.5 gives the still smaller list size $n$ for radius at most
$n - \sqrt{n(n-d)} - 1$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 7.3.3.
