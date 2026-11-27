# Termination and boundedness of well behaved transition systems are undecidable

Well behaved transition systems relax well-structured ones by asking only that the ordering have no infinite antichain. Unlike for well-structured systems, termination and boundedness are undecidable for them, even for a class with finite branching, strong and strict monotonicity, a partial order and computable successor sets.

**Setting (Blondin, Finkel and McKenzie).** An *ordered transition system* $\mathcal{S} = (X, \to, \le)$ has a set of states $X$, a transition relation $\to$ and a quasi-ordering $\le$. It is *strongly monotone* if $x \to y$ and $x' \ge x$ imply $x' \to y'$ for some $y' \ge y$, and *strictly* so if moreover $x' > x$ gives such a $y' > y$. It is a *well behaved transition system* (WBTS) if it is monotone and $(X, \le)$ has no infinite antichain. A countable class of ordered transition systems, with states encoded by natural numbers, is *effective* if Turing machines decide, uniformly in the index of the system, its transition relation and its ordering, and *post-effective* if moreover a Turing machine computes the number $|\mathrm{Post}(x)| \in \mathbb{N} \cup \{\infty\}$ of successors of a state. *Termination* from $x$ asks whether there is no infinite run $x \to x_1 \to x_2 \to \cdots$; *boundedness* from $x$ asks whether the set of states reachable from $x$ is finite.

**Theorem (Blondin, Finkel and McKenzie).** There is a post-effective class of finitely branching WBTS with strong and strict monotonicity and a partial ordering for which termination and boundedness are undecidable.

Under the analogous monotonicity and effectiveness hypotheses both problems are decidable for well-structured transition systems; the same paper identifies a subclass of WBTS, defined through an antichain tree, for which they are decidable.

## Depends on

- [Well-structured transition systems](../../../../../Logic/temporal-logic/timed-and-infinite-state-verification/well-structured-transition-systems.md)

## Proof depends on

- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

For the $i$-th Turing machine $T_i$, take states $X = \{0, -1, -2, \dots\}$ with the usual order of $\mathbb{Z}$, which has no infinite antichain, and transitions $x \to x - 1$ exactly when $T_i$ does not halt on its own encoding within $|x|$ steps. Each state has at most one successor, the relation is decidable by running $T_i$ for finitely many steps, and monotonicity holds because larger states have smaller absolute value. From $0$ there is an infinite run, equivalently infinitely many reachable states, exactly when $T_i$ does not halt on its encoding.

## Sources

- Michael Blondin, Alain Finkel and Pierre McKenzie, *Well Behaved Transition Systems*, Logical Methods in Computer Science 13(3), 2017, https://doi.org/10.23638/LMCS-13(3:24)2017; the definitions of effective classes, monotonicity and WBTS in Sections 2 and 3, and the undecidability lemma for termination and boundedness, read in arXiv:1608.02636v3. Locators in arXiv:1608.02636v3: Lemma 5.1.
