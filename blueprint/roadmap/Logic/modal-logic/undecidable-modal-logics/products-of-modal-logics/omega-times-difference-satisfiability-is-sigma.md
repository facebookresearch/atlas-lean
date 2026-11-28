# Satisfiability over products of ω with difference frames is Σ¹₁-complete

Deciding whether a bimodal formula is satisfiable in a product of the natural numbers $\langle\omega, <\rangle$ with a difference frame is $\Sigma^1_1$-complete, even though each component logic alone is decidable.

**Theorem (Hampson and Kurucz).** $\{\langle\omega, <\rangle\} \times \mathcal{C}_{\mathrm{diff}}$-satisfiability, whether a given bimodal formula is satisfied in some model based on the [product](products-of-linear-orders-and-difference-frames.md) of $\langle\omega, <\rangle$ with a difference frame $(W, \neq)$, is $\Sigma^1_1$-complete.

As a consequence the source obtains (Corollary 3.4) that satisfiability of one-variable first-order linear temporal logic with the counting quantifier "there are at least two" and only the temporal operator "eventually" is $\Sigma^1_1$-complete over $\langle\omega, <\rangle$, in models with constant or with decreasing domains. Over the class of all linear orders the corresponding first-order temporal logic is undecidable but co-r.e., in constant domain models (Corollary 4.3) and in decreasing domain models (Corollary 4.18).

## Depends on

- [Products of linear orders and difference frames](products-of-linear-orders-and-difference-frames.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The lower bound reduces counter machine recurrence (does a machine have a run from a given state with zero counters visiting a given state infinitely often), which is $\Sigma^1_1$-hard by Alur and Henzinger. In a model on $\omega \times W$ a formula forces a forward-going infinite diagonal staircase of points; the value of counter $i$ at step $m$ is the number of points in the $m$-th column carrying a proposition $c_i$. The difference modality can say that a proposition holds at exactly one point of a column ($\Diamond_1^+(\phi \wedge \Box_1\neg\phi)$), which lets the formula control increments and decrements by one, and the linear order carries the run forward in time; recurrence is a $\Box_0\Diamond_0$ condition. The upper bound holds because satisfiability over $\omega \times W$ can be written as a $\Sigma^1_1$ formula over $\omega$, quantifying over the valuation of the finitely many propositions on a countable model. A good expansion links the $\Sigma^1_1$ upper bound. A good expansion also needs, as a statement prerequisite, the analytical hierarchy ($\Sigma^1_1$ and $\Pi^1_1$ sets) and hardness under many-one reductions, which the statement uses.

## Sources

- C. Hampson and A. Kurucz, "Undecidable propositional bimodal logics and one-variable first-order linear temporal logics with counting", *ACM Transactions on Computational Logic* 16(3):1–36, 2015, doi:10.1145/2757285; read as arXiv:1407.1386v3, <https://arxiv.org/abs/1407.1386v3>: Theorem 3.1 of arXiv:1407.1386v3 and its proof in Section 3, with Corollary 3.4, and Corollaries 4.3 and 4.18.
