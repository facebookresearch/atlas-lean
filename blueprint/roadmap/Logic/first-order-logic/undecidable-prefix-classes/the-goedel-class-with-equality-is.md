# The Gödel class with equality is undecidable

Adding equality makes the Gödel prefix undecidable: satisfiability is undecidable for prenex sentences with prefix ∀∀∃ and equality over monadic relations and one binary relation, and with prefixes ∃*∀∀∃ and ∀∀∃* and equality over a single binary relation.

**Theorem (Goldfarb).** The [prefix-vocabulary classes](prefix-vocabulary-classes.md) $[\forall^2\exists, (\omega, 1), (0)]_=$, $[\exists^*\forall^2\exists, (0, 1), (0)]_=$ and $[\forall^2\exists^*, (0, 1), (0)]_=$ are undecidable; indeed they are conservative reduction classes, into which all first-order sentences are effectively translated preserving both satisfiability and finite satisfiability (Theorem 4.0.1 of Börger, Grädel and Gurevich).

Without equality the Gödel class $[\exists^*\forall^2\exists^*, \mathrm{all}, (0)]$ is decidable (Gödel 1932, Kalmár 1933, Schütte 1934). So the decidable boundary of the Gödel prefix depends on equality.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The prefix class ∀∃∀ with one binary relation is undecidable](the-prefix-class-forall-exists-forall-is.md)

## Expansion

The proof of Goldfarb's theorem, as presented in Section 4.3 of Börger, Grädel and Gurevich, first gives an infinity axiom NUM in $[\forall^2\exists^*, (\omega, \omega), (0)]_=$ whose models contain infinitely many elements linked by a successor relation, and uses these elements as numbers to reduce the Kahr–Moore–Wang class $[\forall\exists\forall, (0, \omega), (0)]$ (Section 4.3.1). It then uses only one existential quantifier (Section 4.3.2), encodes the binary predicates of the given formula by monadic ones through pairing and makes the reduction conservative (Section 4.3.3), and encodes the auxiliary binary predicates of NUM by a single one (Section 4.3.4). The second and third classes follow from the first (Exercises 4.3.3 and 4.3.4). A good expansion links pages for the infinity axiom NUM and for these encoding steps. Gödel wrote that his decision procedure for the class $\exists^*\forall^2\exists^*$ should also work in the presence of equality; Goldfarb's theorem shows that it does not. Of the three maximal decidable classes without equality and function symbols, the other two, the prefix class $\exists^*\forall^*$ and the class of sentences with only unary predicates, stay decidable with equality.

## Sources

- W. D. Goldfarb, "The unsolvability of the Gödel class with identity", *The Journal of Symbolic Logic* 49(4):1237–1252, 1984, doi:[10.2307/2274274](https://doi.org/10.2307/2274274) (original source, cited beside the copies read).
- Y. Gurevich, "On the classical decision problem", *Bulletin of the EATCS* 42:140–150, 1990 (reprinted in G. Rozenberg and A. Salomaa (eds.), *Current Trends in Theoretical Computer Science: Essays and Tutorials*, World Scientific, 1993, pp. 254–265), a survey read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/91.pdf>: the first and third classes ($\forall^2\exists$ sentences with equality, one binary predicate and arbitrarily many unary predicates; $\forall^2\exists^*$ sentences with equality and one binary predicate), and the history of Gödel's claim.
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, read in the authors' copy at <https://web.eecs.umich.edu/~gurevich/Books/00.pdf>: Table 1.1 (classes (14)–(16)) and Table 1.2 (class (2)), Theorem 4.0.1, and Section 4.3 (Theorem 4.3.1 and Exercises 4.3.3 and 4.3.4).
