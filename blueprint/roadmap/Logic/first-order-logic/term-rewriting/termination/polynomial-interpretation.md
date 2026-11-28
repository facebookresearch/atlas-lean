# Polynomial interpretation

A *polynomial interpretation* of a [ranked signature](../../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md) $\Sigma$ assigns to each function symbol $f$ of arity $n$ a polynomial $P_f(X_1, \dots, X_n)$ with natural-number coefficients such that $P_f$ is a constant $\ge 1$ when $n = 0$, and, when $n \ge 1$, every $X_i$ occurs in some monomial with exponent at least $1$ and nonzero coefficient. It interprets $f$ over $U = \{n \in \mathbb N \mid n \ge 1\}$ by $f_{\mathcal A}(a_1, \dots, a_n) = P_f(a_1, \dots, a_n)$, which maps $U^n$ into $U$ and is strictly monotone in every argument. A term $t$ with variables $x_1, \dots, x_n$ yields a polynomial $P_t$, and for polynomials $P > Q$ means $P(a_1, \dots, a_n) > Q(a_1, \dots, a_n)$ for all $a_i \in U$.

For example, with $P_b = 3$, $P_f(X) = X^2$ and $P_g(X_1, X_2, X_3) = X_1 + X_2 X_3$, the term $g(f(b), f(x), y)$ has $P = 9 + X^2 Y$.

## Depends on

- [Ranked terms](../../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, polynomial orderings, requirements 1 and 2, p. 116, and the example, p. 117.
