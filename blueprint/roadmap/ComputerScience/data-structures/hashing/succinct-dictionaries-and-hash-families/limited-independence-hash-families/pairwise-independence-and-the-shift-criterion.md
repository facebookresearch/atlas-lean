# Pairwise independence, universality and the shift criterion

Let $Y$ be a finite set and $h : \iota \times X \to Y$ a pairwise independent family with uniform seed. Then $h$ is $1/|Y|$-universal, and if $Y$ is an additive group it is $1/|Y|$-almost $\Delta$-universal.

Conversely (*shift criterion*), let $Y$ be a finite additive group, $g : \kappa \times X \to Y$ any family with key $k$ uniform on a finite set $\kappa$, and define $h_{(k,v)}(x) = g_k(x) + v$ with $v$ uniform on $Y$ independent of $k$. If for all $x_1 \ne x_2$ the difference $g_k(x_1) - g_k(x_2)$ is uniform on $Y$ (that is, $g$ is $1/|Y|$-almost $\Delta$-universal), then $h$ is pairwise independent. In particular this holds when $\kappa$ is a finite additive group and $k \mapsto g_k(x_1) - g_k(x_2)$ is a surjective additive homomorphism $\kappa \to Y$ for every $x_1 \ne x_2$.

## Proof sketch

For distinct inputs the pair $(h_i(x), h_i(x'))$ is uniform on $Y \times Y$, so any relation $h_i(x) = \phi(h_i(x'))$ holds with probability exactly $1/|Y|$; take $\phi$ the identity or a translation. For the converse, the map $(k, v) \mapsto (g_k(x_1) - g_k(x_2),\, g_k(x_2) + v)$ pushes the uniform law forward to a product of uniform laws, and $(h(x_1), h(x_2))$ is a bijective image of this pair.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](almost-delta-universal-hash-family.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Universal hash family](../../universal-hashing/is-universal.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
