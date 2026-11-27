# Catch-up to a value on the left

In the [cast calculus](cast-calculus-and-cast-insertion.md), suppose $\vdash v : T$ for a value $v$, $\vdash f' : T'$, and $v \sqsubseteq f'$ in [cast-calculus precision](precision-of-gradual-types-and-terms.md).
Then $f' \longmapsto^* v'$ for some value $v'$ with $v \sqsubseteq v'$. The proof is by induction on the derivation of $v \sqsubseteq f'$.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Proof depends on

- [Extra cast on the right](extra-cast-on-the-right.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 9 (catchup to value on the left).
