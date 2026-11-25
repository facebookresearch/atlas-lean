# Models of the untyped lambda calculus

A model of the untyped λ-calculus interprets every term as an element of one domain $D$, in which application is a binary operation and λ-abstraction turns a function denoted by a term into an element. For the interpretation to respect β-conversion, every function denoted by a term must be recovered by applying its abstraction. Scott's insight was to use only Scott-continuous functions, for which this is possible (D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §4; *Data types as lattices*, SIAM J. Comput. 5 (1976), §2).

This topic interprets the untyped λ-terms, in locally nameless form (free variables are names, bound variables are de Bruijn indices), in Scott's graph model $P(\omega)$. Abstraction takes the graph of the continuous function that the body denotes, and application is the graph-model application. Every term denotes a continuous function of its variables (Scott's Theorem 2.1). Full β-reduction, including reduction under λ, preserves denotations (the β and ξ parts of Theorem 2.2). The paradoxical combinator $Y$ denotes the least-fixed-point operator (Theorem 2.5). The model is not trivial, since $\lambda x.\lambda y.x$ and $\lambda x.\lambda y.y$ get different denotations. It is not extensional: the η-rule fails in $P(\omega)$. By contrast, η holds in Scott's inverse-limit model $D_\infty \cong [D_\infty \to D_\infty]$.

## The interpretation

- [Extending a bound-variable environment](cons-env.md)
- [Denotation of an untyped λ-term in the graph model](denote.md)
- [Scott's continuity theorem for the graph model](scott-continuous-denote.md)
- [Denotations are Scott-continuous in the free variables](scott-continuous-denote-fvar.md)
- [β at the level of denotations](app-denote-abs.md)
- [Denotations depend only on the bound variables in scope](denote-congr-of-lc-at.md)
- [Locally closed terms ignore the bound-variable environment](denote-congr-of-lc.md)
- [Substitution lemma for opening](denote-open-rec.md)

## Soundness of β-reduction

- [Soundness of a β-contraction in the graph model](denote-eq-of-beta.md)
- [Soundness of full β-reduction in the graph model](denote-eq-of-full-beta.md)
- [Soundness of multi-step full β-reduction in the graph model](denote-eq-of-refl-trans-gen-full-beta.md)

## Recursion

- [The paradoxical combinator $Y$](y.md)
- [Scott's first recursion theorem](app-denote-y.md)

## What the model does and does not identify

- [The graph model separates $\lambda x.\lambda y.x$ from $\lambda x.\lambda y.y$](denote-k-ne-denote-kstar.md)
- [The η-rule is not sound in the graph model](exists-denote-eta-ne.md)

## Related topics

- [Scott's graph model](../../../Order/fixed-points-domain-theory/scott-s-graph-model/README.md): the domain $P(\omega)$, its application and graph operations, and the graph theorem.
- [Scott's inverse-limit theorem](../../../Order/fixed-points-domain-theory/scott-s-inverse-limit-theorem.md): the extensional model $D_\infty$.
- [PCF and computational adequacy](../pcf-and-computational-adequacy/README.md): Scott's domains for a typed language with recursion.
- [The untyped β-conversion term model](../../type-systems-and-lambda-calculi/system-f/the-existing-untyped-beta-conversion-term-model/README.md): the syntactic model of the untyped calculus, terms modulo β-conversion.
