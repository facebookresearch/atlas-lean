# The three-variable guarded fragment with one functional relation is undecidable

Already with three variables, the guarded fragment becomes undecidable when one binary relation is required to be functional.

**Theorem (Grädel).** Satisfiability for the three-variable [guarded fragment](guarded-fragment.md) $\mathrm{GF}^3$ extended by one functional relation, a distinguished binary relation symbol that must denote a partial function, is undecidable.

By contrast, the two-variable guarded fragment extended by number restrictions, which generalize functionality, remains decidable (Kazakov gives a polynomial translation of it into $\mathrm{GF}$).

## Depends on

- [Guarded fragment of first-order logic](guarded-fragment.md)

## Proof depends on

None.

## Expansion

The copy read states the result without proof, citing Grädel; the reduction in the original paper is not reproduced here. Functionality and transitivity are the two features of expressive modal and description logics that lie outside the guarded fragment; for transitivity, see [the two-variable guarded fragment with two transitive relations](gf2-with-two-transitive-relations-is.md).

## Sources

- E. Grädel, "On the restraining power of guards", *Journal of Symbolic Logic* 64(4):1719–1742, 1999, doi:10.2307/2586808 (original source, cited beside the copy read).
- Y. Kazakov, "A polynomial translation from the two-variable guarded fragment with number restrictions to the guarded fragment", in *Logics in Artificial Intelligence (JELIA 2004)*, Lecture Notes in Computer Science 3229, Springer, 2004, pp. 372–384, doi:10.1007/978-3-540-30227-8_32; read in the author's open-access copy at <http://www.cs.ox.ac.uk/people/yevgeny.kazakov/publications/confs/Kaz04GF2N.pdf>: Section 1, which states the undecidability.
