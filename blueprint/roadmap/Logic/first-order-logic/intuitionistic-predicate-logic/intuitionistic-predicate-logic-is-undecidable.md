# Provability in intuitionistic predicate logic is undecidable

There is no algorithm that decides whether a formula of first-order logic is provable intuitionistically; this already holds for formulas built with $\forall$ and $\to$ alone, without function symbols.

**Theorem.** Provability in first-order intuitionistic logic is undecidable: no algorithm decides, for a first-order formula $\varphi$, whether $\varphi$ is a theorem of intuitionistic predicate logic, that is, whether it belongs to [$\mathbf{QInt}$](quantified-intuitionistic-logic-qint.md). The undecidability holds already for the fragment with $\forall$ and $\to$ as the only logical symbols and no function symbols, in particular without negation and falsity.

For relational languages, intuitionistic provability coincides with truth in all intuitionistic Kripke models ([Kripke completeness](../intuitionistic-first-order-logic/kripke-soundness-and-completeness-of-iqc.md)), so the set of first-order formulas valid in all intuitionistic Kripke models is undecidable too.

## Depends on

- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

The full logic is handled by a double negation translation: extending Kolmogorov's translation to first-order logic by $t(\forall x\,\varphi) = \neg\neg\forall x\, t(\varphi)$ and $t(\exists x\,\varphi) = \neg\neg\exists x\, t(\varphi)$, a formula $\varphi$ is a classical theorem iff $t(\varphi)$ is an intuitionistic theorem, so the undecidability of classical first-order logic (Church) transfers. The source states the stronger result for the $\forall, \to$ fragment, with no function symbols, as established in the remark following Corollary 9.3.8, without proof there.

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, Studies in Logic and the Foundations of Mathematics 149, Elsevier, 2006, doi:10.1016/S0049-237X(06)X8001-1 (book version of the lecture notes read, cited beside them); read in the open-access lecture notes (1998/1999) at <https://port70.net/%7Ensz/articles/other/sorensen_urzyczyn_curry_howard_lecture_1999.pdf>: Section 9.3, Theorem 9.3.7 (the Kolmogorov translation), Corollary 9.3.8 and the remark following it.
