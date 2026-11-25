# Soundness of full β-reduction in the graph model

One step of full β-reduction, contracting a redex anywhere in a term, including under λ, preserves the denotation in $P(\omega)$ under every valuation of free and bound variables. This is the β rule of Scott's conversion theorem together with the instance of the rule ξ that full β-reduction needs (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 2.2). Scott's ξ is the equivalence $\forall x.\, \tau = \sigma \iff \lambda x.\tau = \lambda x.\sigma$; what is used here is its left-to-right direction (equal bodies give equal abstractions), applied to reduction under λ. The rule α is built into the locally nameless syntax.

## Informally uses

- [Scott's continuity theorem for the graph model](scott-continuous-denote.md): Scott's proof cites Theorem 2.1.
- [Scott's graph theorem, part (i)](../../../Order/fixed-points-domain-theory/scott-s-graph-model/app-graph.md): and the graph theorem.

## Background

- [Soundness of a β-contraction in the graph model](denote-eq-of-beta.md): the base case.
- [The η-rule is not sound in the graph model](exists-denote-eta-ne.md): η is not among the valid rules.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
