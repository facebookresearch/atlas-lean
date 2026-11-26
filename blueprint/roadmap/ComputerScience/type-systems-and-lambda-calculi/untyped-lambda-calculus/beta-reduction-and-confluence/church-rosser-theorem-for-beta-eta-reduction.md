# Church–Rosser theorem for βη-reduction

[βη-reduction](eta-reduction-and-beta-eta-conversion.md) is confluent: if $t_0 \twoheadrightarrow_{\beta\eta} t_1$ and $t_0 \twoheadrightarrow_{\beta\eta} t_2$, then $t_1 \twoheadrightarrow_{\beta\eta} t_3$ and $t_2 \twoheadrightarrow_{\beta\eta} t_3$ for some
term $t_3$. Consequently $t =_{\beta\eta} t'$ holds exactly when $t$ and $t'$ have a common βη-reduct, and a term has at most one βη-normal form.

The proof follows the one for β: the parallel relation adds the rule "if $t \Rightarrow t'$ then $\lambda x.\, t\, x \Rightarrow t'$ when $x$ is not free in $t$", is substitutive, has the
diamond property, and has βη-reduction as its transitive closure.

## Depends on

- [η-reduction and βη-conversion](eta-reduction-and-beta-eta-conversion.md)

## Proof depends on

- [Church–Rosser theorem for β-reduction](church-rosser-theorem-for-beta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Theorem 1.32, with Lemmas 1.33–1.34 and Proposition 1.35.
