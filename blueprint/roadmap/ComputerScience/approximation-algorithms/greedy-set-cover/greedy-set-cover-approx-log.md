# Greedy set cover is a logarithmic approximation

Let $F$ be a list of finite sets and $U$
a finite set. For every list $C^*$ of members of $F$ that together cover $U$, the list of sets
returned by the greedy set cover algorithm on $F$ and $U$ has length at most
$|C^*| \cdot (\ln |U| + 1)$, where $|C^*|$ is the length of $C^*$ and $\ln 0 = 0$.

## Sources

- CLRS, third edition, Corollary 35.5, via Mathlib's `harmonic_le_one_add_log`.
