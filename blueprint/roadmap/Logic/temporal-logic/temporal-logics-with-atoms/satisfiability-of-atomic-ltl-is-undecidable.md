# Satisfiability of atomic LTL is undecidable

LTL with disjunctions over orbit-finite sets of formulas mentioning atoms has an undecidable satisfiability problem, for equality atoms and for ordered atoms alike.

**Theorem (Klin and Łełyk).** It is undecidable whether a given formula of [atomic LTL](atomic-ltl.md) is satisfiable, that is, holds at some state of some deterministic atomic Kripke model. This holds both for equality atoms and for ordered atoms.

Instances are finite presentations: orbit-finite sets, and hence orbit-finite disjunctions, formulas and models, are written as set-builder expressions $\{e \mid v_1, \ldots, v_n \in \mathbb A, \phi\}$ with $\phi$ a first-order formula over the atoms, and the set $P$ of basic propositions is equivariant and given in the same way. This is Theorem 9.1 of the source, proved by reducing acceptance of the empty word by a Turing machine, following the undecidability of universality for register automata; the reduction uses a special marker proposition and the basic propositions $\mathit{atom}_a$ ($a \in \mathbb A$), $\mathit{tape}_\gamma$ and $\mathit{head}_q$. Classical LTL satisfiability is decidable (PSPACE-complete).

## Depends on

- [Atomic LTL](atomic-ltl.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Acceptance is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-accepts.md)

## Expansion

The proof follows the undecidability of universality for register automata (Neven, Schwentick and Vianu). For a Turing machine $M$ one builds an atomic LTL formula satisfiable iff $M$ accepts the empty word, using basic predicates $\#$, $\mathit{atom}_a$ ($a \in \mathbb A$), $\mathit{tape}_\gamma$ and $\mathit{head}_q$. Conjuncts force a model of the form $\#w\#w\#w\cdots$, where each block $w$ lists distinct atoms in a fixed order, so that an atom names a tape cell across consecutive blocks; each block holds one configuration, with exactly one head position. Orbit-finite conjunctions over $a \in \mathbb A$ then express that unchanged cells keep their letters and that the cell under the head changes according to a transition, by statements such as $\mathbf G(\mathit{atom}_a \wedge \mathit{tape}_\gamma \wedge \neg\psi \to \mathbf X(\neg\mathit{atom}_a\,\mathbf U\,(\mathit{atom}_a \wedge \mathit{tape}_\gamma)))$. Initial and accepting conditions complete the formula; its models correspond to accepting runs of $M$ on the empty word. A good expansion links a page for the finite presentation of orbit-finite sets by set-builder expressions (Section 3 of the source, (3.1)), which the statement uses for its instances.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 9: Theorem 9.1 and its proof.
