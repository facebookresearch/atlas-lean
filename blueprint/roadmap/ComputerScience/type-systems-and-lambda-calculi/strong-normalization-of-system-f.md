# Strong normalization of System F

In Girard's System F, the second-order polymorphic lambda calculus with type abstraction $\Lambda X.\, t$ and type application $t\, U$ besides abstraction and application, let one-step reduction be the closure under all term and type contexts, including under binders, of the two rules $(\lambda x^U.\, t)\, u \rightsquigarrow t[u/x]$ and $(\Lambda X.\, t)\, U \rightsquigarrow t[U/X]$. Every well-typed term of System F is strongly normalizing, that is, has no infinite reduction sequence, and its normal form is unique. Strong normalization is proved with reducibility candidates, and uniqueness of the normal form follows from confluence: every term is reducible under every substitution of reducibility candidates for type variables and of reducible terms for term variables.

## Expansion

This page becomes ready once these prerequisites are stated:

- System F terms, typing and one-step reduction (statement prerequisite)
- Confluence (the Church–Rosser property) of System F reduction, which with strong normalization gives the uniqueness of normal forms (proof prerequisite)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 14, "Strong normalisation for F", Sections 14.1–14.3, <https://www.paultaylor.eu/stable/prot.pdf>
