# Uniform termination and repeated inevitability of lossy counter machines are Π⁰₁-complete

Termination of a lossy counter machine from a given configuration is decidable, but deciding whether it terminates from every configuration is $\Pi^0_1$-complete, and so is deciding whether every infinite run from a given configuration visits a given semilinear set infinitely often.

**Problems (Schnoebelen).** For a lossy counter machine $M$ with configurations $\mathit{Conf}$:

- *Uniform termination:* given $M$, does $M$ terminate from every configuration $\sigma \in \mathit{Conf}$, that is, are all runs from every configuration finite?
- *Repeated inevitability:* given $M$, an initial configuration $\sigma_0$ and a semilinear set $X \subseteq \mathit{Conf}$, does every infinite run from $\sigma_0$ visit $X$ infinitely many times (the ECTL formula $A F^\infty X$)? Finite runs are not considered here, so the zero-step run does not refute the property; the property fails exactly when some reachable loop avoids $X$.

A set of configurations is *semilinear* if it is a finite union of sets $\{\langle \ell, \vec{a} + k_1 \vec{b}_1 + \dots + k_m \vec{b}_m \rangle : k_1, \dots, k_m \in \mathbb{N}\}$; such sets are given as input by Presburger formulas or by bases and increments.

**Theorem (Schnoebelen).** Uniform termination and repeated inevitability are $\Pi^0_1$-complete for lossy counter machines.

Consequently the set of configurations from which $M$ must terminate, although downward closed and with decidable membership, cannot be computed (Corollary 4.6): no algorithm produces, uniformly from $M$, a finite representation of it.

## Depends on

- [Lossy counter machines](lossy-counter-machines.md)
- [Π_n sets](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Semilinear sets are the sets definable in Presburger arithmetic](../../../petri-nets/decision-procedures/semilinear-sets-are-the-presburger-definable-sets.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

*Membership.* By Dickson's lemma and monotonicity, a lossy counter machine has an infinite run from $\sigma$ exactly when it has a loop $\sigma \to^\ast \sigma' \to^+ \sigma'$, so the complement of uniform termination is the $\Sigma^0_1$ property $\exists \sigma : \sigma \to^+ \sigma$; similarly, repeated inevitability fails exactly when some reachable loop avoids $X$.

*Hardness.* A Minsky machine $M$ is put "on a budget": an extra counter $B$ is decremented whenever another counter is incremented and conversely, so the total of all counters is constant, and a lossy run of the budgeted machine is a reliable run exactly when this total does not drop. Then $M$ has a loop $\langle \ell, \vec{a} \rangle \to^+_{\mathrm{std}} \langle \ell, \vec{a} \rangle$ if and only if the budgeted machine has a lossy loop $\langle \ell, B, \vec{a} \rangle \to^+ \langle \ell, B, \vec{a} \rangle$ for some budget $B$. Whether a Minsky machine has a loop from some configuration is $\Sigma^0_1$-complete, so uniform termination is $\Pi^0_1$-hard (Corollary 7.2 of the source).

## Sources

- Philippe Schnoebelen, "Lossy Counter Machines Decidability Cheat Sheet", Reachability Problems (RP 2010), Lecture Notes in Computer Science, pp. 51–75, 2010, <https://doi.org/10.1007/978-3-642-15349-5_4>; Section 4.3 (problem definitions, Theorem 4.5 and Corollary 4.6), Section 2.4 (semilinear sets), Lemma 4.1, and Section 7.1–7.2 (Proposition 7.1, Corollary 7.2), read in the open-access copy at <http://www.lsv.fr/Publis/PAPERS/PDF/phs-rp10.pdf>.
