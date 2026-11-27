# Harmonic bound in the largest set size for greedy set cover

Let $F$ be a list of finite
sets each with at most $d$ elements, $U$ a finite set, and $H(n) = 1 + \frac12 + \dots + \frac1n$
the $n$-th harmonic number. For every list $C^*$ of members of $F$ that together cover $U$, the
list of sets returned by the greedy set cover algorithm on $F$ and $U$ has length at most
$|C^*| \cdot H(d)$, where $|C^*|$ is the length of $C^*$.

## Sources

- CLRS, third edition, Theorem 35.4.
