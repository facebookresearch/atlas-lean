# Strong normalization of λP

In the presentation of [λP](the-calculus-lambda-p.md) without λ-abstractions in constructors, every typable term is strongly β-normalizing, by erasing dependencies.
For the full system of the λ-cube, strong normalization is a case of the [metatheory of pure type systems](../pure-type-systems-and-the-calculus-of.md), and β-reduction is
[confluent on all pseudo-terms](../../calculus-of-constructions/beta-reduction-on-pure-type-system-pseudo-terms.md), typable or not.

The proof for the restricted presentation erases dependencies. Map constructors to simple types by $\overline{\alpha} = \alpha$, $\overline{(\forall x{:}\tau)\sigma} = \overline{\tau} \to \overline{\sigma}$ and
$\overline{\varphi\, M} = \overline{\varphi}$, and translate constructors and terms of λP into simply typed terms by a map $(\cdot)^\bullet$ that keeps the terms occurring
inside types as arguments of fresh variables, so that they are not lost. If $\Gamma \vdash M : \tau$ in λP then $M^\bullet$ has type $\overline{\tau}$ in an extension of
$\overline{\Gamma}$, and every β-step $M \to_\beta M_1$ is matched by at least one step $M^\bullet \to_\beta^+ M_1^\bullet$; an infinite reduction from $M$ would give one in the
simply typed λ-calculus.

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)

## Background

- [Pure type systems and the calculus of constructions](../pure-type-systems-and-the-calculus-of.md): strong normalization for every system of the λ-cube
- [Beta reduction on pure type system pseudo-terms is confluent](../../calculus-of-constructions/beta-reduction-on-pure-type-system-pseudo-terms.md)

## Expansion

This page becomes ready once:

- Strong normalization of full β-reduction in the simply typed λ-calculus (proof prerequisite; not yet stated as a page)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definitions 10.3.1 and 10.3.2, Lemma 10.3.3, Corollary 10.3.4 (strong normalization), for the presentation of Remark 10.1.2.
