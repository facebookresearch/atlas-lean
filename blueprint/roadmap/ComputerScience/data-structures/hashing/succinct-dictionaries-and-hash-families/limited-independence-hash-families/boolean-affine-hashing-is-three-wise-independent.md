# Boolean affine hashing is three-wise independent

For all positive integers $n$ and $k$, the family of maps $x \mapsto Ax + b$ from $\{0,1\}^n$ to $\{0,1\}^k$ over $\mathbb{F}_2$, with $A$ a uniform $k \times n$ Boolean matrix and $b$ a uniform vector in $\{0,1\}^k$, is three-wise independent: for all distinct $x_1, x_2, x_3 \in \{0,1\}^n$ and all $\alpha_1, \alpha_2, \alpha_3 \in \{0,1\}^k$, $\Pr[Ax_i + b = \alpha_i \text{ for } i = 1, 2, 3] = 2^{-3k}$. Each output coordinate is a random XOR constraint $a_{i,0} \oplus \bigoplus_{j=1}^{n} a_{i,j} x_j$ with independent uniform coefficients; this is the family $H_{xor}(n, k)$ of Ivrii, Malik, Meel and Vardi, and for a single coordinate it is Lemma 2 of Gomes, Sabharwal and Selman.

## Proof sketch

For distinct $x_1, x_2, x_3$, the vectors $u = x_2 - x_1$ and $v = x_3 - x_1$ are nonzero and distinct, hence linearly independent over $\mathbb{F}_2$, since the only scalars are $0$ and $1$. Thus each row $a$ of $A$ maps to $(a \cdot u, a \cdot v)$ uniformly, rows are independent, and the uniform offset $b$ makes $(Ax_1 + b, Au, Av)$ uniform. Derived, not stated separately by the sources: composing with the projection onto the first $r \le k$ output coordinates gives the same family with $r$ rows, so it is again three-wise independent, and the cases $n = 0$ or $k = 0$ are trivial.

## Depends on

- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- C. P. Gomes, A. Sabharwal and B. Selman, "Near-Uniform Sampling of Combinatorial Spaces Using XOR Constraints", Advances in Neural Information Processing Systems 19 (NIPS 2006), MIT Press, 2007 (Section 3.2, Lemma 2).
- A. Ivrii, S. Malik, K. S. Meel and M. Y. Vardi, "On Computing Minimal Independent Support and Its Applications to Sampling and Counting", Principles and Practice of Constraint Programming (CP 2015), LNCS 9255, Springer, 2015 (Section 2: the family $H_{xor}(n, m)$ is 3-universal, with $r$-universality defined as $r$-wise independence).
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (pairwise independence of affine hashing).
