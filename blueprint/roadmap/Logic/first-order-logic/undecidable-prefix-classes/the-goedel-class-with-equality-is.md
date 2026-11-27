# The Gödel class with equality is undecidable

Adding equality makes the Gödel prefix undecidable: satisfiability is undecidable for prenex sentences with prefix ∀∀∃ and equality over monadic relations and one binary relation, and with prefixes ∃*∀∀∃ and ∀∀∃* and equality over a single binary relation.

**Theorem (Goldfarb).** The [prefix-vocabulary classes](prefix-vocabulary-classes.md) $[\forall^2\exists, (\omega, 1), (0)]_=$, $[\exists^*\forall^2\exists, (0, 1), (0)]_=$ and $[\forall^2\exists^*, (0, 1), (0)]_=$ are undecidable.

Without equality the Gödel class $[\exists^*\forall^2\exists^*, \mathrm{all}, (0)]$ is decidable (Gödel 1932, Kalmár 1933, Schütte 1934). So the decidable boundary of the Gödel prefix depends on equality.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

Gödel wrote that his decision procedure for the class $\exists^*\forall^2\exists^*$ should also work in the presence of equality; Goldfarb's theorem shows that it does not. Of the three maximal decidable classes without equality and function symbols, the other two, the prefix class $\exists^*\forall^*$ and the class of sentences with only unary predicates, stay decidable with equality.

## Sources

- W. D. Goldfarb, "The unsolvability of the Gödel class with identity", *The Journal of Symbolic Logic* 49(4):1237–1252, 1984, doi:[10.2307/2274274](https://doi.org/10.2307/2274274) (original source, cited beside the copies read).
- Y. Gurevich, "On the classical decision problem", *Bulletin of the EATCS* 42:140–150, 1990 (reprinted in G. Rozenberg and A. Salomaa (eds.), *Current Trends in Theoretical Computer Science: Essays and Tutorials*, World Scientific, 1993, pp. 254–265), a survey read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/91.pdf>: the first and third classes ($\forall^2\exists$ sentences with equality, one binary predicate and arbitrarily many unary predicates; $\forall^2\exists^*$ sentences with equality and one binary predicate), and the history of Gödel's claim.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: classes (14), (15) and (16) on the slide "The complete classification: undecidable cases B: Classes with functions or equality" and class (2) on the slide "The complete classification: decidable cases". The second class, $[\exists^*\forall^2\exists, (0, 1), (0)]_=$, rests on this slide (class (15)) beside the original paper.
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
