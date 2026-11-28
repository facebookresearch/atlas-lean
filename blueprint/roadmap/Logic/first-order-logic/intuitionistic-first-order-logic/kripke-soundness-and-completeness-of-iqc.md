# Kripke soundness and completeness of intuitionistic first-order logic

For every finite set $\Gamma$ of formulas and formula $\varphi$ of first-order logic, possibly with free variables, $\Gamma \vdash \varphi$ in [natural deduction for IQC](natural-deduction-for-intuitionistic-first-order-logic.md) if and only if $\Gamma \Vdash \varphi$ in [Kripke models with expanding domains](kripke-models-for-iqc.md): every state $c$ and vector $\vec{a}$ of elements of $\mathcal{A}_c$, for the free variables of $\Gamma$ and $\varphi$, that force all members of $\Gamma$ force $\varphi$.

**Proof idea.** Soundness is an induction on derivations that uses [persistence of forcing](persistence-of-forcing-in-first-order-kripke-models.md) for the introduction rules of $\to$ and $\forall$. The source obtains completeness from completeness of IQC for complete Heyting algebra valued structures and the equivalence of that semantics with Kripke semantics, both stated there without proof.

## Depends on

- [Natural deduction for intuitionistic first-order logic](natural-deduction-for-intuitionistic-first-order-logic.md)
- [Kripke models for intuitionistic first-order logic](kripke-models-for-iqc.md)

## Proof depends on

- [Persistence of forcing in first-order Kripke models](persistence-of-forcing-in-first-order-kripke-models.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 9.4: Theorem 9.4.5 (derivability coincides with validity in complete Heyting algebra valued structures) and Theorem 9.4.8 (that validity coincides with Kripke forcing), stated there without proof with references for the proofs.
- J. Moschovakis, *Intuitionistic logic*, Stanford Encyclopedia of Philosophy, substantive revision 16 December 2022, Section 5.1, <https://plato.stanford.edu/entries/logic-intuitionistic/>: soundness and completeness of IQC for Kripke structures with expanding domains.

## Expansion

This page becomes ready once the prerequisites of completeness are stated, each as a proof prerequisite: completeness of intuitionistic first-order logic for complete Heyting algebra valued structures together with the equivalence of that semantics with Kripke forcing (Sørensen–Urzyczyn, Theorems 9.4.5 and 9.4.8, stated there without proof), or a direct proof by a canonical Kripke model of prime theories with witnesses for existential formulas.
