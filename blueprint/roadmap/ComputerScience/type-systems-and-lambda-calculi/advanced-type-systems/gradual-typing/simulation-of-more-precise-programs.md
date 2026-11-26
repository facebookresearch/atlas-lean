# Simulation of more precise programs

In the [cast calculus](cast-calculus-and-cast-insertion.md), suppose $f_1 \sqsubseteq f_1'$ in [cast-calculus precision](precision-of-gradual-types-and-terms.md), $\vdash f_1 : T$ and $\vdash f_1' : T'$. If $f_1 \longmapsto f_2$,
then $f_1' \longmapsto^* f_2'$ for some $f_2'$ with $f_2 \sqsubseteq f_2'$. So less precise programs simulate more precise ones step by step; by induction on the number of steps
this gives part 2 of [the gradual guarantee](the-gradual-guarantee.md), and part 3 follows from part 2 and determinism of reduction.

The proof is by induction on the derivation of $f_1 \sqsubseteq f_1'$ followed by case analysis of the step $f_1 \longmapsto f_2$; extra casts on the left are handled within it.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Proof depends on

- [Extra cast on the right](extra-cast-on-the-right.md)
- [Catch-up to a value on the left](catchup-to-value-on-the-left.md)
- [Simulation of function application](simulation-of-function-application.md)
- [Simulation of unwrapping](simulation-of-unwrapping.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 7 (simulation of more precise programs) and the derivation of parts 2 and 3 of the gradual guarantee after Lemma 11.
