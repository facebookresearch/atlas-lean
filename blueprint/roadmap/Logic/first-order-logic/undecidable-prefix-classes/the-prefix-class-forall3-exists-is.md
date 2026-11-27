# The prefix classes ∀³∃, ∃*∀∃∀ and ∃*∀³∃ are undecidable

Satisfiability is undecidable for prenex sentences without equality and function symbols with prefix ∀∀∀∃ over monadic relations and one binary relation, and with the prefixes ∃*∀∃∀ and ∃*∀∀∀∃ over a single binary relation.

**Theorem (Surányi).** The [prefix-vocabulary classes](prefix-vocabulary-classes.md) $[\forall^3\exists, (\omega, 1), (0)]$, $[\exists^*\forall\exists\forall, (0, 1), (0)]$ and $[\exists^*\forall^3\exists, (0, 1), (0)]$ are undecidable.

In the first class the sentences may use any number of monadic relation symbols and one binary relation symbol; in the other two only one binary relation symbol, preceded by any block of existential quantifiers. None of the classes allows equality or function symbols.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

Satisfiability of arbitrary first-order sentences is undecidable, and the class is shown undecidable by effectively transforming arbitrary sentences, or a known undecidable class, into sentences of the class while preserving satisfiability. The classification places the class among its undecidable cases, together with the decidable boundary it borders.

## Sources

- J. Surányi, *Reduktionstheorie des Entscheidungsproblems im Prädikatenkalkül der ersten Stufe*, Verlag der Ungarischen Akademie der Wissenschaften, Budapest, 1959 (book; reviewed in *The Journal of Symbolic Logic* 25(3):274–276, 1960, doi:[10.2307/2964712](https://doi.org/10.2307/2964712)), cited beside the copies read.
- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorem 6, classes $\Phi_2 = \Phi(\forall^3\exists, (\infty, 1), \emptyset)$, $\Phi_7 = \Phi(\exists^\infty\forall\exists\forall, (0, 1), \emptyset)$ and $\Phi_5 = \Phi(\exists^\infty\forall^3\exists, (0, 1), \emptyset)$ among the nine minimal undecidable classes without equality.
- Y. Gurevich, "On the classical decision problem", *Bulletin of the EATCS* 42:140–150, 1990 (reprinted in G. Rozenberg and A. Salomaa (eds.), *Current Trends in Theoretical Computer Science: Essays and Tutorials*, World Scientific, 1993, pp. 254–265), a survey read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/91.pdf>: Surányi's theorem that the ∀³∃ sentences form a reduction class, and the list of the nine minimal undecidable prefix-signature classes.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: classes (2), (8) and (9) on the slide "The complete classification: undecidable cases A: Pure predicate logic (without functions, without =)".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
