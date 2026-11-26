# Small integer solutions of linear systems (Siegel-type bounds)

Let $A\in\mathbb{Z}^{p\times q}$ with $p<q$ and all entries of absolute value at most $\alpha$. Then $Ax=0$ has a nonzero integer solution whose entries are bounded by an explicit function of $p$, $q$ and $\alpha$ (for instance by the largest absolute value of a $p\times p$ minor, at most $p^{p/2}\alpha^p$ by Hadamard's inequality). Moreover, if an integer system $Ax=b$, $x\ge0$ has a nonnegative integer solution, it has one whose entries are bounded by a polynomial-size (in bit length) explicit bound depending only on $A$ and $b$.

## Proof sketch

Choose a maximal nonsingular square submatrix and use Cramer's rule to produce a kernel vector whose entries are minors. For nonnegative solutions, move along kernel directions to a basic solution (with at most $\operatorname{rank}A$ nonzero coordinates), whose entries are ratios of minors, and then reduce modulo the lattice of small kernel vectors.

## Depends on

- [Farkas' lemma over linearly ordered fields](farkas-lemma-over-ordered-fields.md)
- [Hadamard's determinant inequality](../../positive-definite-matrices/hadamard-s-inequality-and-determinant-bounds-for/hadamard-s-determinant-inequality/hadamard-determinant-inequality.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- Ji\vrí Matou\vsek, Bernd G\"artner, "Understanding and Using Linear Programming", Springer, 2007.
