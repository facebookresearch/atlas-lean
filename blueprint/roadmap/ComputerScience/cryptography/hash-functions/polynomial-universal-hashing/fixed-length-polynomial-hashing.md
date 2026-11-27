# Collision and difference bounds for fixed-length polynomial hashing

Let $F$ be a finite field and $n \ge 1$. For a key $k \in F$ and a coefficient vector $x = (x_0, \dots, x_{n-1}) \in F^n$ let $H(k, x) = x_0 k^{n-1} + x_1 k^{n-2} + \cdots + x_{n-1}$ (Horner evaluation from zero). For $k$ uniform on $F$ and all distinct $x \ne x'$ in $F^n$,

$$
\Pr_k[H(k,x) = H(k,x')] \le \frac{n-1}{|F|}, \qquad \Pr_k[k\,H(k,x) - k\,H(k,x') = d] \le \frac{n}{|F|} \text{ for every } d \in F .
$$

So $H$ is an $(n-1)/|F|$-universal hash function and $k \cdot H$ is $n/|F|$-almost $\Delta$-universal. More generally, if $k$ is uniform on a finite set $S$ injected into $F$, then $H$ is $(n-1)/|S|$-universal.

## Proof sketch

$H(k,x) - H(k,x')$ is a nonzero polynomial in $k$ of degree at most $n-1$, with at most $n-1$ roots. For the difference bound, $k(H(k,x) - H(k,x')) - d$ is a nonzero polynomial of degree at most $n$ (its non-constant part is nonzero), with at most $n$ roots.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/almost-delta-universal-hash-family.md)
- [Bounded universal hash functions](../bounded-universal-hash-functions.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
