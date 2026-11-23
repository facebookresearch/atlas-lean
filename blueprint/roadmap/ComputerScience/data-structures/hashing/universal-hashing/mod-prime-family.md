# Mod-prime family of distinct functions

For $p > 0$ and $m > 0$, the mod-prime family
is the finite set of all functions $h_{a,b}$ from $\mathbb{Z}/p\mathbb{Z}$ to
$\{0, 1, \dots, m - 1\}$ with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \ne 0$, where
$h_{a,b}$ is the mod-prime hash function with index $(a, b)$.

When $p$ is prime, universality holds for the indexed family of mod-prime hash functions, with
its $p(p - 1)$ indices counted separately; this set of distinct functions can be smaller, since
distinct index pairs may give the same function after the final reduction modulo $m$.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 11.3.3, which counts the family as having $p(p - 1)$
  members, one for each index $(a, b)$.
