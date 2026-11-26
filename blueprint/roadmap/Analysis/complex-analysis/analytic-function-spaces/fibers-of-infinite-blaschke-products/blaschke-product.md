# Blaschke products

For $c \in \mathbb{C}$, $m \in \mathbb{N}$ and $a : \mathbb{N} \to \mathbb{C}$,

$$
B(z) = c \, z^m \prod_{n} b_{a_n}(z),
$$

with $b_{a_n}$ the [Blaschke factors](blaschke-factor.md) and the product an unconditional infinite product (taken to be $1$ where it does not converge unconditionally).

This is a Blaschke product in the classical sense for the valid data of an [infinite Blaschke product](is-infinite-blaschke-data.md): $|c| = 1$, every $a_n$ nonzero and in the open unit disc, and $\sum_n (1 - |a_n|) < \infty$. Then the product converges on the disc, $B$ has a zero of exact order $m$ at the origin, and its other zeros are the $a_n$, with multiplicity. Outside these data the formula need not describe a Blaschke product: $c = 0$ gives the identically zero function rather than a zero of exact order $m$ at the origin, and $a_n = 0$ gives a zero factor.
