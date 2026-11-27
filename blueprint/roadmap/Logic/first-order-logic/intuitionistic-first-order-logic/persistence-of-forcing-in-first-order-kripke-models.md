# Persistence of forcing in first-order Kripke models

In a [Kripke model for first-order logic](kripke-models-for-iqc.md), if $c \le c'$ and $c, \vec{a} \Vdash \varphi$, then $c', \vec{a} \Vdash \varphi$; the elements $\vec{a}$ of $\mathcal{A}_c$ lie in $\mathcal{A}_{c'}$ since domains expand.

**Proof.** By induction on $\varphi$. Atomic formulas persist because $\mathcal{A}_c \subseteq \mathcal{A}_{c'}$, an existential witness in $\mathcal{A}_c$ lies in $\mathcal{A}_{c'}$, and the clauses for $\to$ and $\forall$ quantify over all states above, which for $c'$ are among those above $c$.

## Depends on

- [Kripke models for intuitionistic first-order logic](kripke-models-for-iqc.md)

## Sources

- N. Bezhanishvili and D. de Jongh, *Intuitionistic logic*, lecture notes, Institute for Logic, Language and Computation, Universiteit van Amsterdam, ILLC Prepublication Series PP-2006-25, 2006, <https://eprints.illc.uva.nl/id/eprint/200/1/PP-2006-25.text.pdf>, Section 3.3, p. 16: Kripke models for the predicate calculus, with expanding domains each a submodel of the next, and the statement that persistency transfers to formulas (Exercise 4).
- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 9.4: Definition 9.4.7, the Kripke models and forcing used here; the induction, as in the propositional case of Section 2.5, is written out here.
