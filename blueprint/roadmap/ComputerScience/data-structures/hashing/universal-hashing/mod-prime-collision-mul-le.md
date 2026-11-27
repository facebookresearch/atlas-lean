# Collision bound for the mod-prime hash functions

Let $p$ be a prime and $m > 0$, and
for $a, b \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$ let
$h_{a,b}(x) = ((ax + b) \bmod p) \bmod m$ be the mod-prime hash function. For distinct keys
$x \ne y$ in $\mathbb{Z}/p\mathbb{Z}$, the number of index pairs $(a, b)$ with $a \ne 0$ and
$h_{a,b}(x) = h_{a,b}(y)$, multiplied by $m$, is at most $p(p - 1)$, the total number of
index pairs.

This is the counting step of the universality of the mod-prime family. The bijection
$(a, b) \mapsto (ax + b, ay + b)$ identifies the colliding index pairs with the pairs $(r, s)$
of distinct residues modulo $p$ whose representatives in $\{0, \dots, p - 1\}$ are congruent
modulo $m$.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 11.3.3, proof of Theorem 11.5 (the counting step).
