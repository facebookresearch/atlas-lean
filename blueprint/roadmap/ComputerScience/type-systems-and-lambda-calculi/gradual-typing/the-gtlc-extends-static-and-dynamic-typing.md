# The GTLC extends static and dynamic typing

Let $\vdash_S$ and $\Downarrow_S$ be typing and evaluation of the simply typed λ-calculus, and $\Downarrow_D$ evaluation of the dynamically typed λ-calculus (DTLC).

1. **Static.** For a fully annotated term $e$ of the [GTLC](the-gradually-typed-lambda-calculus.md) and a static type $T$: $\vdash_S e : T$ if and only if $\vdash e : T$, and
   $e \Downarrow_S v$ if and only if $e \Downarrow v$.
2. **Dynamic.** Let $\lceil e \rceil$ embed a DTLC term into the GTLC by casting every constant to $?$. Then $\vdash \lceil e \rceil : ?$, and $e \Downarrow_D r$ if and only if
   $\lceil e \rceil \Downarrow r$.

## Depends on

- [The gradually typed λ-calculus](the-gradually-typed-lambda-calculus.md)
- [The cast calculus and cast insertion](cast-calculus-and-cast-insertion.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 4.1, Theorem 1 (equivalence to the simply typed λ-calculus for fully annotated terms) and Theorem 2 (embedding of the DTLC).
