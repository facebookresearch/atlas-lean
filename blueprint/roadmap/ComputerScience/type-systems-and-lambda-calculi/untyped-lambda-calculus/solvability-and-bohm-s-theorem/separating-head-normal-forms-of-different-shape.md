# Separating head normal forms of different shape

Write $\mathbf{0} = \lambda x\, y.\, y$ and $\mathbf{1} = \lambda x\, y.\, x$. For untyped λ-terms $t$ and $u$, if

1. $t = x\, t_1 \cdots t_p$ and $u = y\, u_1 \cdots u_q$ with $x \ne y$ or $p \ne q$, or
2. $t = \lambda x_1 \dots x_m\, x.\, x\, t_1 \cdots t_p$ and $u = \lambda x_1 \dots x_n\, x.\, x\, u_1 \cdots u_q$ with $m \ne n$ or $p \ne q$,

then there is a [Böhm transformation](bohm-transformations.md) $F$ with $F(t) =_\beta \mathbf{0}$ and $F(u) =_\beta \mathbf{1}$. For example, in the first case with $x \ne y$ one substitutes
$\lambda z_1 \dots z_p.\, \mathbf{0}$ for $x$ and $\lambda z_1 \dots z_q.\, \mathbf{1}$ for $y$; with $x = y$ and $p < q$ one first substitutes the [applicator](applicators-make-normal-terms-normalizable.md) $\alpha_q$ for $x$.

## Depends on

- [Böhm transformations](bohm-transformations.md)
- [Applicators keep normal terms normalizable](applicators-make-normal-terms-normalizable.md)

## Proof depends on

- [Applicators keep normal terms normalizable](applicators-make-normal-terms-normalizable.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 5, Lemma 5.10 and its proof.
