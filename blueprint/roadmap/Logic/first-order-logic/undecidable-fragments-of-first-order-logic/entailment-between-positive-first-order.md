# Entailment between positive first-order sentences is undecidable

Given two first-order sentences without negation and without equality, it is undecidable whether the first logically implies the second; in contrast, entailment between positive Horn sentences, which also lack disjunction, is decidable.

**Positive sentences.** Over a finite relational signature, a first-order sentence is *positive* if it contains no negation; here it is also *equality-free*. Thus it is built from atoms $R(\bar{x})$ with $\wedge$, $\vee$, $\exists$ and $\forall$. It is *positive Horn* if, moreover, it contains no disjunction.

**Problem.** The *entailment problem for positive first-order logic* takes two positive equality-free sentences $\varphi$ and $\psi$ and asks whether $\models \varphi \to \psi$, that is, whether every structure (finite or infinite) satisfying $\varphi$ satisfies $\psi$.

**Theorem (Chen, Madelaine and Martin).** The entailment problem for positive equality-free first-order logic is undecidable (Theorem 4.12).

The source proves that the entailment problem for positive Horn sentences is decidable, so the result shows that adding disjunction already costs decidability.

## Depends on

None.

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

The reduction is from satisfiability of equality-free first-order sentences to the dual question "is $\varphi \wedge \neg\psi$ satisfiable?". For a sentence $\varphi$ with relation symbols $R_1, \dots, R_r$, add fresh symbols $S_1, \dots, S_r$ of the same arities, meant to denote the complements of the $R_i$. Push negations of $\varphi$ to the atoms and replace each $\neg R_i$ by $S_i$, obtaining a positive $\varphi'$. Let $\theta_1 = \bigwedge_i \forall \bar{x}\,(S_i(\bar{x}) \vee R_i(\bar{x}))$ and $\psi = \bigvee_i \exists \bar{x}\,(S_i(\bar{x}) \wedge R_i(\bar{x}))$. Then $\varphi$ is satisfiable iff $\varphi' \wedge \theta_1 \wedge \neg\psi$ is satisfiable, i.e. iff $\varphi' \wedge \theta_1$ does not entail $\psi$, and both sentences are positive and equality-free.

## Sources

- Hubie Chen, Florent Madelaine and Barnaby Martin, "Quantified constraints and containment problems", *Logical Methods in Computer Science* 11(3):9, 2015, doi:10.2168/LMCS-11(3:9)2015; read as arXiv:1310.1016v3, <https://arxiv.org/abs/1310.1016v3>: Section 2 (positive and positive Horn sentences), Section 4.3 (the problems and Theorem 4.12), Section 4.2 and the introduction (decidability of positive Horn entailment) of arXiv:1310.1016v3. The source credits the proof of Theorem 4.12 to Arnaud Durand.
