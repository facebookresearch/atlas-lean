# Applicators keep normal terms normalizable

For $n \ge 0$ let $\alpha_n = \lambda z_1 \dots z_n\, z.\, z\, z_1 \cdots z_n$, the *applicator* of order $n$ (so $\alpha_0 = \lambda z.\, z$). Let $t$ be a β-normal term and $x_1, \dots, x_k$
variables. Then $t[\alpha_{n_1}/x_1, \dots, \alpha_{n_k}/x_k]$ is β-normalizable whenever $n_1, \dots, n_k$ are large enough. The bound matters: for $\delta = \lambda y.\, y\, y$ and
$t = x\, \delta\, \delta$, the term $t[\alpha_0/x]$ is not normalizable.

The proof is by induction on $t$: if $t = y\, t_1 \cdots t_p$ with $y = x_i$, then once $n_i \ge p$ the head application of $\alpha_{n_i}$ reduces to the normal form
$\lambda x_{p+1} \dots x_{n_i}\, x.\, x\, u_1 \cdots u_p\, x_{p+1} \cdots x_{n_i}$, where $u_j$ is the normal form of the substituted $t_j$.

## Depends on

- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

- [Head normal forms and solvable terms](head-normal-forms-and-solvable-terms.md): a normal term not beginning with λ has the form $y\, t_1 \cdots t_p$

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 5, the definition of applicators, Proposition 5.1 and the remark after it.
