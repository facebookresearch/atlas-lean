# Mod-prime family of distinct functions

For $p > 0$ and $m > 0$, the mod-prime family
is the finite set of all functions $h_{a,b}$ from $\mathbb{Z}/p\mathbb{Z}$ to
$\{0, 1, \dots, m - 1\}$ with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \ne 0$, where
$h_{a,b}$ is the mod-prime hash function with index $(a, b)$.

Universality is proved for the indexed family of mod-prime hash functions, matching the
$p(p - 1)$ count of indices in CLRS; this set of distinct functions can be smaller, since
distinct index pairs may give the same function after the final reduction modulo $m$.
