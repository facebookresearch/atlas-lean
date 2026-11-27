# The GTLC extends static and dynamic typing

Let $\vdash_S$ and $\Downarrow_S$ be typing and evaluation of the simply typed λ-calculus, and $\Downarrow_D$ evaluation of the dynamically typed λ-calculus (DTLC).

1. **Static.** For a fully annotated term $e$ of the [GTLC](the-gradually-typed-lambda-calculus.md) and a static type $T$: $\vdash_S e : T$ if and only if $\vdash e : T$, and
   $e \Downarrow_S v$ if and only if $e \Downarrow v'$ for a value $v'$ whose cast erasure, the term with every cast removed, is $v$. Cast insertion puts only identity casts $T_1 \Rightarrow^\ell T_1$ into a fully
   annotated static term, and an identity cast at a function type is not removed until the function is applied: with $A = \mathrm{int} \to \mathrm{int}$,
   $(\lambda f{:}A.\, f)\, (\lambda x{:}\mathrm{int}.\, x)$ evaluates in the STLC to $\lambda x{:}\mathrm{int}.\, x$ and in the GTLC to that function wrapped in identity casts.
2. **Dynamic.** Let $\lceil e \rceil$ embed a DTLC term into the GTLC by annotating every bound variable with $?$ and casting every constant and every abstraction to $?$. Then $\vdash \lceil e \rceil : ?$.

The source states the static evaluation equivalence with the same value letter on both sides; erasing the identity casts makes explicit how the values compare. It
also states that $e \Downarrow_D r$ if and only if $\lceil e \rceil \Downarrow r$, again with one result letter. Results of the two languages do not compare by erasure:
the embedded identity $\lambda x.\, x$ evaluates to the value $(\lambda x{:}?.\, x) : (? \to ?) \Rightarrow ?$, whose erasure is not the embedding of $\lambda x.\, x$. That equivalence
needs a relation between DTLC values and tagged cast-calculus values, so it is listed among the missing prerequisites below.

## Depends on

- [The gradually typed λ-calculus](the-gradually-typed-lambda-calculus.md)
- [The cast calculus and cast insertion](cast-calculus-and-cast-insertion.md)

## Expansion

This page becomes ready once:

- The simply typed λ-calculus with base types $\mathrm{int}$ and $\mathrm{bool}$ and their constants, with its typing $\vdash_S$ and big-step evaluation $\Downarrow_S$ (statement prerequisite; not yet stated)
- The dynamically typed λ-calculus with constants and its big-step evaluation $\Downarrow_D$, including its errors (statement prerequisite; not yet stated)
- The embedding $\lceil \cdot \rceil$ of dynamically typed terms into the GTLC, which casts every constant and every abstraction to $?$; the source casts only the constants, which leaves $\lambda x{:}?.\, x$ at type $? \to ?$ (statement prerequisite; not yet stated)
- A relation between DTLC results and cast-calculus results, relating a constant $k$ of base type $B$ to its injection $k : B \Rightarrow ?$, a function value to an injected function value whose body is related to the embedding of its body, and an error to blame, and the dynamic evaluation equivalence of the source's Theorem 2 stated with it (statement prerequisite; not yet stated)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 4.1, Theorem 1 (equivalence to the simply typed λ-calculus for fully annotated terms) and Theorem 2 (embedding of the DTLC).
