# Polynomial hashing over GF(2^q) is k-wise independent

Let $\mathbb{F} = \mathbb{F}_{2^q}$, let $k \ge 1$, $U \le 2^q$ and $M \le q$. For coefficients $a_0, \dots, a_{k-1} \in \mathbb{F}$ drawn uniformly and independently, define $h_a : [U] \to [2^M]$ by evaluating $p_a(x) = \sum_{i<k} a_i x^i$ at the field element encoded by $x$ and keeping the low $M$ bits of the result. Then $\{h_a\}$ is $k$-wise independent. With $q$ chosen as in the trinomial field construction and precomputed carry-less multiplication tables on chunks of $b$ bits, $h_a(x)$ is evaluated on the Word RAM by Horner's rule in $O(k)$ field operations, each multiplication costing $O((q / b)^2)$ instructions.

## Proof sketch

For distinct $x_1, \dots, x_t$ with $t \le k$ the linear map $a \mapsto (p_a(x_1), \dots, p_a(x_t))$ from $\mathbb{F}^k$ onto $\mathbb{F}^t$ is surjective (Vandermonde, or Lagrange interpolation), hence has fibers of equal size, so the values are independent and uniform on $\mathbb{F}$; projecting each to $M$ bits preserves independence and uniformity.

## Depends on

- [k-wise independent hash family](k-wise-independent-hash-family.md)
- [The trinomials x^(2·3^t) + x^(3^t) + 1 are irreducible over GF(2)](irreducible-trinomials-over-gf2.md)
- [Carry-less multiplication by Four-Russians tables](carry-less-multiplication-by-tables.md)

## Proof depends on

- [Polynomials of degree below k form a k-wise independent family](../limited-independence-hash-families/polynomial-k-wise-independent-hashing.md)

## Sources

- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981, Section 1 (polynomials of degree below $n$ over a finite field, and keeping the last bits of the value when the field size is a power of two).
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012, Construction 3.32 and Proposition 3.33.
