# The η-rule is not sound in the graph model

For a free variable $x$, the η-redex $\lambda y.\, x\,y$ and $x$ have different denotations under a suitable valuation of $x$. The reason is that $\operatorname{graph}(\operatorname{app}(u, \cdot)) \ne u$ for some $u$. Scott's conversion theorem lists only the rules α, β and ξ as valid in $P(\omega)$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 2.2 and the remarks after its proof).

## Background

- [The graph model is not extensional](../../../Order/fixed-points-domain-theory/scott-s-graph-model/exists-graph-app-ne.md): the set-level fact.
- [Scott's inverse-limit theorem](../../../Order/fixed-points-domain-theory/scott-s-inverse-limit-theorem.md): a model in which η holds.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
