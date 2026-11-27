# Denotation of an untyped λ-term in the graph model

Consider the untyped λ-terms in locally nameless form: free variables are names, bound variables are de Bruijn indices. Let $\rho$ value the free variables and $bs$ the bound variables in $P(\omega)$. The denotation $[\![M]\!]_{\rho, bs} \subseteq \mathbb{N}$ is defined by recursion on $M$:
- a bound variable $i$ denotes $bs(i)$, and a free variable $x$ denotes $\rho(x)$;
- an application $M\,N$ denotes $\operatorname{app}([\![M]\!], [\![N]\!])$;
- an abstraction $\lambda.M$ denotes $\operatorname{graph}(v \mapsto [\![M]\!]_{\rho, v \cdot bs})$.

This is the semantics of application and λ-abstraction in Scott's language LAMBDA (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, §2), restricted to the pure λ-calculus.

## Background

- [Application in the graph model](../../../Order/fixed-points-domain-theory/scott-s-graph-model/app.md): the meaning of application.
- [Graph of a function on `P(ω)`](../../../Order/fixed-points-domain-theory/scott-s-graph-model/graph.md): the meaning of abstraction.
- [Extending a bound-variable environment](cons-env.md): the valuation under a binder.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
