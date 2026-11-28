# Some equational theory has decidable elementary unification but undecidable matching

The decidability of equational unification depends on the kind of problem: for some equational theory elementary unification is decidable, while matching and unification with constants are undecidable.

**Theorem (Bürckert).** There is an equational theory $E$ such that elementary $E$-unification is decidable, but matching modulo $E$ and $E$-unification with constants are undecidable (see [E-unification problems](equational-unification-problems.md)).

Since matching modulo $E$ reduces to $E$-unification with constants, by replacing the variables of the right-hand side with fresh constants, the undecidability of matching implies that of unification with constants.

## Depends on

- [E-unification problems](equational-unification-problems.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The copy read states the theorem without proof, citing Bürckert; the construction of the theory is not reproduced here. The result shows that matching need not be easier than unification once the signature is taken into account: elementary problems contain only the symbols of the theory, whereas matching problems in effect contain free constants. The source adds that the instantiation ordering used for complete sets of $E$-matchers must be defined with care.

## Sources

- H.-J. Bürckert, "Matching — a special case of unification?", *Journal of Symbolic Computation* 8(5):523–536, 1989, doi:10.1016/S0747-7171(89)80057-4 (original source, cited beside the copy read).
- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.2.2 ("The signature matters") and Section 7 (matching), which state the theorem.
