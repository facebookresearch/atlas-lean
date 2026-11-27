# Moore determinants in characteristic two as finite differences

For $k \ge 1$ and $u_1,\dots,u_k$ in a field of characteristic two, the Moore matrix is $\bigl(u_l^{2^{m}}\bigr)_{1\le l\le k,\,0\le m<k}$. Its determinant equals its permanent and satisfies, for every base point $a$,

$$
\sum_{c\in\mathbb{F}_2^{k}}\Bigl(a+\sum_lc_lu_l\Bigr)^{2^k-1}=\det\bigl(u_l^{2^m}\bigr),
$$

i.e. it is the $k$-th finite difference of $x\mapsto x^{2^k-1}$. In particular it vanishes iff $u_1,\dots,u_k$ are linearly dependent over $\mathbb{F}_2$.

## Proof sketch

$x^{2^k-1}=\prod_{m<k}x^{2^m}$ is a product of $k$ additive maps; a $k$-fold finite difference of a product of $k$ additive functions is the sum over bijections between the difference directions and the factors, which in characteristic two is the permanent, hence the determinant, of the Moore matrix.

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- R. Lidl and H. Niederreiter, "Finite Fields", Encyclopedia of Mathematics and its Applications 20, Cambridge University Press, 1997, Lemma 3.51: the Moore determinant vanishes iff the $u_l$ are linearly dependent over the prime field.
