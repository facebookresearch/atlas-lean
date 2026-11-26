# Harmonic bound in the universe size for greedy set cover

Let $F$ be a list of finite
sets, $U$ a finite set, and $H(n) = 1 + \frac12 + \dots + \frac1n$ the $n$-th harmonic number. For
every list $C^*$ of members of $F$ that together cover $U$, the list of sets returned by the
greedy set cover algorithm on $F$ and $U$ has length at most $|C^*| \cdot H(|U|)$, where $|C^*|$
is the length of $C^*$.

## Sources

- CLRS, third edition, Corollary 35.5, in the stronger harmonic form.
