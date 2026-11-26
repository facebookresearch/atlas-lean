# Type safety of the GTLC

If $\vdash e : T$ in the [GTLC](the-gradually-typed-lambda-calculus.md), then one of the following holds for the [evaluation](cast-calculus-and-cast-insertion.md) of $e$:

- $e \Downarrow v$ for a value $v$ of the cast calculus with $\vdash_C v : T$ in the cast calculus's typing;
- $e \Downarrow \mathrm{blame}_T\, \ell$ for some label $\ell$, a trapped cast error;
- $e \Uparrow$, evaluation diverges.

So well-typed GTLC programs never reach an untrapped error, although trapped cast errors may occur.

## Depends on

- [The gradually typed λ-calculus](the-gradually-typed-lambda-calculus.md)
- [The cast calculus and cast insertion](cast-calculus-and-cast-insertion.md)

## Proof depends on

- [Syntactic type soundness](../../type-soundness/syntactic-type-soundness.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 4.2, Theorem 3 (type safety of the GTLC, after Siek and Taha).
