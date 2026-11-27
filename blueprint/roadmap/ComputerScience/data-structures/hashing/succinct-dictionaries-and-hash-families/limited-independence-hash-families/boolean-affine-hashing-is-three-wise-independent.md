# Boolean affine hashing is three-wise independent

For all $k, n \ge 0$, the family of maps $x \mapsto Ax + b$ from $\{0,1\}^n$ to $\{0,1\}^k$ over $\mathbb{F}_2$, with $A$ a uniform $k \times n$ Boolean matrix and $b$ a uniform vector in $\{0,1\}^k$, is three-wise independent. The same holds after composing with the projection onto the first $r$ output coordinates.

## Proof sketch

For distinct $x_1, x_2, x_3$, the vectors $u = x_2 - x_1$ and $v = x_3 - x_1$ are nonzero and distinct, hence linearly independent over $\mathbb{F}_2$, since the only scalars are $0$ and $1$. Thus each row $a$ of $A$ maps to $(a \cdot u, a \cdot v)$ uniformly, rows are independent, and the uniform offset $b$ makes $(Ax_1 + b, Au, Av)$ uniform.

## Depends on

- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing, 2020.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
