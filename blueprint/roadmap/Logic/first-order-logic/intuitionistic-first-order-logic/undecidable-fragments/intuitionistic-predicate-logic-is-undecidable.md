# Provability in intuitionistic predicate logic is undecidable

There is no algorithm that decides which relational first-order formulas, without constants, function symbols or equality, are provable intuitionistically; this already holds for formulas built with $\forall$ and $\to$ alone.

**Theorem.** No algorithm decides, for a formula $\varphi$ of the relational language of [$\mathbf{QInt}$](quantified-intuitionistic-logic-qint.md), without constants, function symbols or equality, whether $\varphi \in \mathbf{QInt}$. The undecidability holds already for the fragment with $\forall$ and $\to$ as the only logical symbols, in particular without negation and falsity.

For relational languages, membership in $\mathbf{QInt}$ coincides with intuitionistic provability ([Kripke completeness](../kripke-soundness-and-completeness-of-iqc.md)). Over signatures with function symbols, undecidability of intuitionistic provability also follows from Church's theorem by a double negation translation (Theorem 9.3.7 of the source).

## Depends on

- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Intuitionistic provability of Δ₂ formulas in the Mints hierarchy is undecidable](intuitionistic-provability-of-delta-2-formulas.md)

## Expansion

Both clauses follow from the undecidability of provability for $\Delta_2$ formulas of the Mints hierarchy, which are function-free $(\forall,\to)$ formulas of $\mathbf{QInt}$'s language; membership in $\Delta_2$ is decidable. The source states the result for the $\forall, \to$ fragment without function symbols as established in the remark following Corollary 9.3.8, without proof there. Its Kolmogorov route, extending the translation by $t(\forall x\,\varphi) = \neg\neg\forall x\, t(\varphi)$ and $t(\exists x\,\varphi) = \neg\neg\exists x\, t(\varphi)$ so that $\varphi$ is a classical theorem iff $t(\varphi)$ is an intuitionistic one, transfers Church's theorem only to signatures that the classical result uses, such as the language of arithmetic with its constant and function symbols.

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, Studies in Logic and the Foundations of Mathematics 149, Elsevier, 2006, doi:10.1016/S0049-237X(06)X8001-1 (book version of the lecture notes read, cited beside them); read in the open-access lecture notes (1998/1999) at <https://port70.net/%7Ensz/articles/other/sorensen_urzyczyn_curry_howard_lecture_1999.pdf>: Section 9.3, Theorem 9.3.7 (the Kolmogorov translation), Corollary 9.3.8 and the remark following it.
