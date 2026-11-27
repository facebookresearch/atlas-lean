# Folded Wronskian criterion for linear independence

Let $\gamma \in \mathbb{F}_q^{*}$ have order greater than $k$ and let $f_1, \dots, f_r \in \mathbb{F}_q[x]$ have degree less than $k$. Then $f_1, \dots, f_r$ are linearly independent over $\mathbb{F}_q$ if and only if the *folded Wronskian*

$$
W_\gamma(f_1, \dots, f_r)(x) = \det\big[ f_j(\gamma^{i} x) \big]_{0 \le i < r,\ 1 \le j \le r}
$$

is a nonzero polynomial. The analogous statement with derivatives $f_j^{(i)}$ (the classical Wronskian) holds when $\mathrm{char}\,\mathbb{F} \ge k$.

## Proof sketch

A linear dependence among the $f_j$ is a dependence among the columns at every $x$, so the determinant vanishes. Conversely, if $W_\gamma \equiv 0$, the operator $f(x) \mapsto f(\gamma x)$ acting on the span has the property that some nontrivial combination is annihilated by a difference operator of order $< r$; diagonalizing this operator on monomials, whose eigenvalues $\gamma^{e}$ for $e < k$ are distinct by the order assumption, shows that the span has dimension less than $r$.

## Proof depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)

## Sources

- Venkatesan Guruswami, Swastik Kopparty, "Explicit subspace designs", Combinatorica 36(2) (2016), FOCS (2013).
- Shashank Srivastava, "Improved list size for folded Reed-Solomon codes", SODA (2025); arXiv:2410.09031.
