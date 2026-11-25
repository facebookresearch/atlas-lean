# Scott's continuity theorem for the graph model

For every term $M$ and valuation $\rho$ of its free variables, the denotation $bs \mapsto [\![M]\!]_{\rho, bs}$ is a Scott-continuous function of the values of the bound variables (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 2.1, there for all terms of the language LAMBDA). The proof is by induction on $M$. For abstraction it uses that $\operatorname{graph}$ commutes with pointwise unions; for application it uses joint continuity of $\operatorname{app}$.

## Background

- [Application in `P(ω)` is jointly Scott-continuous](../../../Order/fixed-points-domain-theory/scott-s-graph-model/scott-continuous-app.md): the application case.
- [The graph of a pointwise union](../../../Order/fixed-points-domain-theory/scott-s-graph-model/graph-s-sup.md): the abstraction case, the counterpart of the lemma in Scott's proof that λ-abstraction preserves continuity.
- [Denotations are Scott-continuous in the free variables](scott-continuous-denote-fvar.md): the same theorem for the free variables.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
