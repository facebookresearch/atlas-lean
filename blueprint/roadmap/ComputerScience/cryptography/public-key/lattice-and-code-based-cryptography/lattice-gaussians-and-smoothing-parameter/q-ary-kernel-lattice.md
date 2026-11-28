# The q-ary kernel lattice and short integer solutions

For a matrix $A \in \mathbb{Z}_q^{n \times m}$, the *$q$-ary kernel lattice* is $\Lambda_q^{\perp}(A) = \{x \in \mathbb{Z}^m : Ax \equiv 0 \pmod q\}$, a full-rank lattice containing $q\mathbb{Z}^m$ with determinant at most $q^n$. The Euclidean *short integer solution* problem $\ell_2\text{-}\mathrm{SIS}_{n,m,q,\beta}$, as defined by Micciancio and Regev (Definition 5.1) and Peikert (Definition 4.1.1), asks, for uniform $A$, for a nonzero $x \in \Lambda_q^{\perp}(A)$ with $\|x\|_2 \le \beta$; if $\ell_2\text{-}\mathrm{SIS}_{n,m,q,\beta}$ is hard, then $x \mapsto Ax \bmod q$ is collision resistant on integer vectors of Euclidean norm at most $\beta/2$, since a collision $x \ne x'$ gives the solution $x - x'$.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Shortest vector, independent vectors and guaranteed distance decoding problems](svp-sivp-givp-and-gdd.md)
- [The short integer solution problem in the Euclidean norm](../lattice-problems/sis-euclidean-norm.md)

## Sources

- M. Ajtai, "Generating Hard Instances of Lattice Problems", Proceedings of the 28th Annual ACM Symposium on Theory of Computing (STOC), 1996.
- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
- C. Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science 10(4), 2016.
