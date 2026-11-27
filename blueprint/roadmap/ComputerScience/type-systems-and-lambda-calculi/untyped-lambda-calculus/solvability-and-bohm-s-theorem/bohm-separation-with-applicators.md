# Böhm separation with applicators

Let $x_1, \dots, x_k$ be distinct variables and $t$, $t'$ β-normal terms that are not βη-convertible. Then for all distinct integers $n_1, \dots, n_k$ that are large enough:

1. there is a [Böhm transformation](bohm-transformations.md) $F$ with $F(t[\alpha_{n_1}/x_1, \dots, \alpha_{n_k}/x_k]) =_\beta \mathbf{0}$ and $F(t'[\alpha_{n_1}/x_1, \dots, \alpha_{n_k}/x_k]) =_\beta \mathbf{1}$, where $\alpha_n$ are
   the [applicators](applicators-make-normal-terms-normalizable.md);
2. in particular $t[\alpha_{n_1}/x_1, \dots, \alpha_{n_k}/x_k]$ and $t'[\alpha_{n_1}/x_1, \dots, \alpha_{n_k}/x_k]$ are not βη-convertible, since $\mathbf{0}$ and $\mathbf{1}$ are distinct βη-normal forms, which by
   the Church–Rosser theorem for βη are not βη-convertible.

Consequently, for β-normalizable $t$, $t'$: if $t[\alpha_n/x] =_{\beta\eta} t'[\alpha_n/x]$ for infinitely many $n$, or $t\, \alpha_n =_{\beta\eta} t'\, \alpha_n$ for infinitely many $n$, then $t =_{\beta\eta} t'$.
[Böhm's theorem](bohm-s-theorem.md) is the case of closed terms, with $k = 0$.

## Depends on

- [Böhm transformations](bohm-transformations.md)
- [Applicators keep normal terms normalizable](applicators-make-normal-terms-normalizable.md)

## Proof depends on

- [Separating head normal forms of different shape](separating-head-normal-forms-of-different-shape.md)
- [Church–Rosser theorem for βη-reduction](../beta-reduction-and-confluence/church-rosser-theorem-for-beta-eta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 5, Theorem 5.6, Proposition 5.8 and Corollary 5.9.
