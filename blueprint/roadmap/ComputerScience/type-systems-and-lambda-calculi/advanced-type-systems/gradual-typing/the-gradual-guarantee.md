# The gradual guarantee

Suppose $e \sqsubseteq e'$ in [term precision](precision-of-gradual-types-and-terms.md) and $\vdash e : T$ in the [GTLC](the-gradually-typed-lambda-calculus.md).

1. **Static.** $\vdash e' : T'$ for some $T'$ with $T \sqsubseteq T'$.
2. **Dynamic, toward less precision.** If $e \Downarrow v$ then $e' \Downarrow v'$ for some $v'$ with $v \sqsubseteq v'$ in cast-calculus precision; if $e \Uparrow$ then $e' \Uparrow$.
3. **Dynamic, toward more precision.** If $e' \Downarrow v'$ then $e \Downarrow v$ with $v \sqsubseteq v'$, or $e \Downarrow \mathrm{blame}_T\, \ell$ for some $\ell$; if $e' \Uparrow$ then $e \Uparrow$ or
   $e \Downarrow \mathrm{blame}_T\, \ell$ for some $\ell$.

Removing type annotations therefore preserves typability and behaviour; and adding annotations to a well-typed program, if the result is still well typed,
can change its behaviour only by introducing trapped cast errors (adding an annotation can also make the program ill typed).

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)
- [The cast calculus and cast insertion](cast-calculus-and-cast-insertion.md)

## Proof depends on

- [Cast insertion preserves precision](cast-insertion-preserves-precision.md)
- [Simulation of more precise programs](simulation-of-more-precise-programs.md)
- [Catch-up to a value on the left](catchup-to-value-on-the-left.md)
- [Type safety of the GTLC](type-safety-of-the-gtlc.md): a well-typed program evaluates to a value, to blame or diverges

## Expansion

This page becomes ready once:

- A simulation result that preserves divergence: if $f_1 \sqsubseteq f_1'$ and $f_1$ reduces forever, then so does $f_1'$, ruling out infinitely many consecutive steps of $f_1$ matched by zero steps of $f_1'$ (proof prerequisite for the divergence clause of part 2 and the first clause of part 3; not yet stated, and the source's argument after Lemma 11 does not supply it)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 4.3, Theorem 5 (gradual guarantee), proved in Section 6 through Lemma 6 (cast insertion preserves precision) and Lemma 7 (simulation of more precise programs), with Lemmas 8–11.
