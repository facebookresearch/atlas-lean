# Strong normalization of System F

In Girard's System F, the second-order polymorphic lambda calculus with type abstraction $\Lambda X.\, t$ and type application $t\, U$ besides abstraction and application, let one-step reduction be the closure under all term and type contexts, including under binders, of the two rules $(\lambda x^U.\, t)\, u \rightsquigarrow t[u/x]$ and $(\Lambda X.\, t)\, U \rightsquigarrow t[U/X]$. Every well-typed term of System F is strongly normalizing, that is, has no infinite reduction sequence, and its normal form is unique. Strong normalization is proved with reducibility candidates: every term $t$ with $\Gamma \vdash t : A$ is reducible at $A$ under every substitution of reducibility candidates for the type variables and of terms reducible at the types $\Gamma(x)$ for the term variables $x$ of $\Gamma$. Uniqueness of the normal form follows from confluence.

## Depends on

- [Scoped terms of pure System F](system-f/scoped-pure-system-f/tm.md)
- [Extrinsic typing of pure System F terms](system-f/the-five-typing-rules-of-pure-system-f/typing.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- One-step reduction of System F terms, closed under all term and type contexts (statement prerequisite)
- Confluence (the Church–Rosser property) of System F reduction, which with strong normalization gives the uniqueness of normal forms (proof prerequisite)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 14, "Strong normalisation for F", Sections 14.1–14.3, <https://www.paultaylor.eu/stable/prot.pdf>
