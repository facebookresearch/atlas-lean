# The prefix class ∀∃∀ with one binary relation is undecidable

Satisfiability is undecidable for prenex sentences with prefix ∀∃∀, without equality and function symbols, using any number of monadic relation symbols and a single binary relation symbol.

**Theorem (Kahr; Kahr, Moore and Wang).** The [prefix-vocabulary class](prefix-vocabulary-classes.md) $[\forall\exists\forall, (\omega, 1), (0)]$ is undecidable: no algorithm decides satisfiability of sentences $\forall x \exists y \forall z\, \varphi$ with $\varphi$ quantifier-free, built from monadic relation symbols and one binary relation symbol, without equality and function symbols. Indeed it is a conservative reduction class, into which all first-order sentences are effectively translated preserving both satisfiability and finite satisfiability (Theorem 3.1.1 of Börger, Grädel and Gurevich), and so is the Kahr–Moore–Wang class $[\forall\exists\forall, (0, \omega), (0)]$ of $\forall\exists\forall$ sentences over any number of binary relation symbols and no others (Theorem 3.1.9 there, credited to Kahr, Moore and Wang and to Gurevich and Koryakov).

Kahr, Moore and Wang had reduced the decision problem to the ∀∃∀ case; the classification attributes the version with a single binary relation to Kahr (1962). Prefixes with one universal quantifier fall in the decidable class $[\exists^*\forall\exists^*, \mathrm{all}, \mathrm{all}]$, so a second universal quantifier is needed.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Büchi described Turing machines by ∀∃∀∃ sentences, which made the ∀∃∀∃ prefix class a reduction class; in the same year Kahr, Moore and Wang sharpened this to the ∀∃∀ prefix. A reduction class is one into which arbitrary sentences are effectively translated with satisfiability preserved, so its satisfiability problem is undecidable. Kahr's refinement keeps the prefix and restricts the vocabulary to one binary relation besides monadic ones. Wang introduced domino problems to prove this class unsolvable. In the proof of Börger, Grädel and Gurevich (Section 3.1), each domino system $D$ yields a sentence $\psi_D$ of the Kahr–Moore–Wang class, with one binary predicate per domino, that has a model with universe $\mathbb N$ when $D$ tiles $\mathbb N \times \mathbb N$, is unsatisfiable when it does not, and has a finite model when $D$ admits a periodic tiling (Theorem 3.1.9 via Corollary 3.1.8). So satisfiability of $\psi_D$ is equivalent to tiling $\mathbb N \times \mathbb N$, and by compactness to tiling the plane, which gives undecidability. Section 3.1.3 then interprets these formulas in coloured graphs and describes the graphs in a normal form by a formula of Kahr's class. A good expansion links pages for the recursive inseparability of the periodically tileable from the non-tileable domino systems used for conservativity (Corollary 3.1.8) and for the graph interpretation of Section 3.1.3.

## Sources

- A. S. Kahr, E. F. Moore and H. Wang, "Entscheidungsproblem reduced to the ∀∃∀ case", *Proceedings of the National Academy of Sciences of the USA* 48(3):365–377, 1962, doi:[10.1073/pnas.48.3.365](https://doi.org/10.1073/pnas.48.3.365) (the reduction to the ∀∃∀ case, cited beside the copies read).
- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorem 6, class $\Phi_1 = \Phi(\forall\exists\forall, (\infty, 1), \emptyset)$ among the nine minimal undecidable classes without equality.
- Y. Gurevich, "On the classical decision problem", *Bulletin of the EATCS* 42:140–150, 1990 (reprinted in G. Rozenberg and A. Salomaa (eds.), *Current Trends in Theoretical Computer Science: Essays and Tutorials*, World Scientific, 1993, pp. 254–265), a survey read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/91.pdf>: the account of Büchi's ∀∃∀∃ reduction and the Kahr–Moore–Wang theorem, and the two classes obtained from the minimal undecidable prefix classes ∀∃∀ and ∀³∃ by allowing one binary predicate and arbitrarily many unary predicates.
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, read in the authors' copy at <https://web.eecs.umich.edu/~gurevich/Books/00.pdf>: Table 1.1, Theorem 3.0.1, and Section 3.1 (Theorem 3.1.1, the domino problems of Section 3.1.1, Corollary 3.1.8, Theorem 3.1.9 and Section 3.1.3).
