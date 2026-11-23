# Fundamental theorem of relational parametricity for System F

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $t \in \mathrm{Tm}_{n,m}$ and $A \in \mathrm{Ty}_n$ with $\Gamma \vdash t : A$ ([typing](../the-five-typing-rules-of-pure-system-f/typing.md)). Let $\rho$ assign a [β-invariant relation](../binary-beta-invariant-relations/rel.md) to each type variable, and let $\sigma$, $\tau$ assign terms of the [untyped term model](../the-existing-untyped-beta-conversion-term-model/model.md) to the term variables with $[\![\Gamma(i)]\!]_\rho(\sigma(i), \tau(i))$ for every $i < m$ ([relational interpretation](../impredicative-binary-interpretation-of-system-f/interpret.md)). Then $[\![A]\!]_\rho(t\{\sigma\}, t\{\tau\})$, where $t\{\sigma\}$ is the [closing](../system-f-erasure-and-closing-environments/close.md) of $t$ by $\sigma$.

This is an adaptation of Reynolds' abstraction theorem (1983, Sections 3 and 8) to a syntactic model, the β-invariant relations on erased terms, following Wadler's formulation with related environments (1989, Section 6).

## Sources

- J. C. Reynolds, *Types, abstraction and parametric polymorphism*, in R. E. A. Mason (ed.), Information Processing 83, Proceedings of the IFIP 9th World Computer Congress, North-Holland, 1983, 513–523.
- P. Wadler, *Theorems for free!*, Proceedings of the Fourth International Conference on Functional Programming Languages and Computer Architecture (FPCA '89), ACM, 1989, 347–359.
