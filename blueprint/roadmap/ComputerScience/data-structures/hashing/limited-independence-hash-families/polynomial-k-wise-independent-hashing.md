# Polynomials of degree below k form a k-wise independent family

Let $F$ be a finite field and $k \ge 1$. For a seed $c = (c_0, \dots, c_{k-1}) \in F^k$ let $h_c(x) = \sum_{j<k} c_j x^j$ for $x \in F$. With $c$ uniform on $F^k$, the family $\{h_c\}$ is $k$-wise independent from $F$ to $F$. For $k = 2$ these are the affine maps $x \mapsto c_0 + c_1 x$.

## Proof sketch

For distinct points $x_1, \dots, x_t$ with $t \le k$, evaluation $c \mapsto (h_c(x_1), \dots, h_c(x_t))$ is an additive map $F^k \to F^t$, surjective by Lagrange interpolation. A surjective additive homomorphism pushes the uniform law forward to the uniform law, so every value vector is attained by exactly $|F|^{k-t}$ seeds.

## Depends on

- [k-wise independent hash families](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
