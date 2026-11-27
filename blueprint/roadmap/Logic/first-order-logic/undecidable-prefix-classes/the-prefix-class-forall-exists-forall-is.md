# The prefix class ∀∃∀ with one binary relation is undecidable

Satisfiability is undecidable for prenex sentences with prefix ∀∃∀, without equality and function symbols, using any number of monadic relation symbols and a single binary relation symbol.

**Theorem (Kahr).** The [prefix-vocabulary class](prefix-vocabulary-classes.md) $[\forall\exists\forall, (\omega, 1), (0)]$ is undecidable: no algorithm decides satisfiability of sentences $\forall x \exists y \forall z\, \varphi$ with $\varphi$ quantifier-free, built from monadic relation symbols and one binary relation symbol, without equality and function symbols.

Kahr, Moore and Wang had reduced the decision problem to the ∀∃∀ case; the classification attributes the version with a single binary relation to Kahr (1962). Prefixes with one universal quantifier fall in the decidable class $[\exists^*\forall\exists^*, \mathrm{all}, \mathrm{all}]$, so a second universal quantifier is needed.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

Büchi described Turing machines by ∀∃∀∃ sentences, which made the ∀∃∀∃ prefix class a reduction class; in the same year Kahr, Moore and Wang sharpened this to the ∀∃∀ prefix. A reduction class is one into which arbitrary sentences are effectively translated with satisfiability preserved, so its satisfiability problem is undecidable. Kahr's refinement keeps the prefix and restricts the vocabulary to one binary relation besides monadic ones.

## Sources

- A. S. Kahr, E. F. Moore and H. Wang, "Entscheidungsproblem reduced to the ∀∃∀ case", *Proceedings of the National Academy of Sciences of the USA* 48(3):365–377, 1962, doi:[10.1073/pnas.48.3.365](https://doi.org/10.1073/pnas.48.3.365) (the reduction to the ∀∃∀ case, cited beside the copies read).
- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorem 6, class $\Phi_1 = \Phi(\forall\exists\forall, (\infty, 1), \emptyset)$ among the nine minimal undecidable classes without equality.
- Y. Gurevich, "On the classical decision problem", *Bulletin of the EATCS* 42:140–150, 1990 (reprinted in G. Rozenberg and A. Salomaa (eds.), *Current Trends in Theoretical Computer Science: Essays and Tutorials*, World Scientific, 1993, pp. 254–265), a survey read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/91.pdf>: the account of Büchi's ∀∃∀∃ reduction and the Kahr–Moore–Wang theorem, and the two classes obtained from the minimal undecidable prefix classes ∀∃∀ and ∀³∃ by allowing one binary predicate and arbitrarily many unary predicates.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: class (1) on the slide "The complete classification: undecidable cases A: Pure predicate logic (without functions, without =)".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
