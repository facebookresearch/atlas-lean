# Recurrence for the capacity distribution on Catalan words

Write $a(n, i)$ for the
capacity distribution of the Catalan words of length $n$ ending in $i$, $b(n, i)$ for that of
those Catalan words of length $n$ ending in $i$ whose largest letter is $i$, and $c(m, j)$ for the
area distribution of the set $\mathcal{C}_{m,j}$ of words of length $m$ over $\{1, \dots, j\}$
ending in $j$ in which each letter is at most one more than the letter before it. For
$1 < i < n$, in the Laurent polynomial ring $\mathbb{Z}[q, q^{-1}]$,

$$
a(n,i) = b(n-1,i-1) + \sum_{j=i}^{n-1} a(n-1,j) +
\sum_{m=1}^{n-i-1} \sum_{j=i}^{n-m-1} q^{mi} \, a(n-m-1,j) \, c(m,i-1;1/q),
$$

where $c(m, i-1; 1/q)$ is the image of $c(m, i-1)$ under $q \mapsto q^{-1}$.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2.
