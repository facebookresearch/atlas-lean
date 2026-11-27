# Stable model existence for DatalogMTL with negation over the rationals is undecidable

Adding negation as failure under a stable model semantics to DatalogMTL destroys decidability over the rational timeline: for a suitable fixed propositional forward-propagating program, no algorithm decides, given a dataset whose intervals are all bounded, whether the program and the dataset have a stable model.

**Setting (Wałęga, Tena Cucala, Cuenca Grau and Kostylev).** The timeline is the set $\mathbb{Q}$ of rationals. An *interval* is a nonempty convex subset $\varrho \subseteq \mathbb{Q}$ whose endpoints lie in $\mathbb{Q} \cup \{-\infty, \infty\}$; it is *bounded* if both endpoints are rational, and *non-negative* if it contains no negative number. Rational endpoints are written as fractions with numerator and denominator in binary. Over a function-free vocabulary, a *relational atom* is $P(\mathbf{s})$ with $\mathbf{s}$ a tuple of constants and variables, and *metric atoms* are given by

$$
M ::= \top \mid \bot \mid P(\mathbf{s}) \mid \diamondminus_\varrho M \mid \diamondplus_\varrho M \mid \boxminus_\varrho M \mid \boxplus_\varrho M \mid M \,\mathcal{S}_\varrho\, M \mid M \,\mathcal{U}_\varrho\, M,
$$

where $\varrho$ ranges over non-negative intervals. An *interpretation* $\mathfrak{I}$ assigns to each $t \in \mathbb{Q}$ a set of ground relational atoms. Satisfaction of ground metric atoms is: $\diamondminus_\varrho M$ holds at $t$ if $M$ holds at some $t'$ with $t - t' \in \varrho$; $\diamondplus_\varrho M$ if at some $t'$ with $t' - t \in \varrho$; $\boxminus_\varrho M$ and $\boxplus_\varrho M$ likewise with "every" in place of "some"; $M_1 \,\mathcal{S}_\varrho\, M_2$ holds at $t$ if $M_2$ holds at some $t'$ with $t - t' \in \varrho$ and $M_1$ holds throughout the open interval $(t', t)$; and $M_1 \,\mathcal{U}_\varrho\, M_2$ symmetrically towards the future. A *dataset* is a finite set of facts $P(\mathbf{c})@\varrho$, each requiring the ground relational atom $P(\mathbf{c})$ to hold at every point of the interval $\varrho$; it is *bounded* if every interval in it is bounded.

A *rule* has the form

$$
M \leftarrow M_1 \wedge \dots \wedge M_k \wedge \mathsf{not}\, M_{k+1} \wedge \dots \wedge \mathsf{not}\, M_m \qquad (m \ge k \ge 0),
$$

where $M_1, \dots, M_m$ are metric atoms and the head $M$ is built from $\top$, $\bot$ and relational atoms using only $\boxminus_\varrho$ and $\boxplus_\varrho$. A rule is *safe* if each head variable occurs in a positive body atom outside a left operand of $\mathcal{S}$ or $\mathcal{U}$; a *program* is a finite set of safe rules. It is *propositional* if all its predicates are nullary, and *forward-propagating* if no rule body mentions $\diamondplus$, $\boxplus$ or $\mathcal{U}$ and no rule head mentions $\boxminus$.

Stable models are defined through here-and-there interpretations. An *HT-interpretation* is a pair $(\mathfrak{H}, \mathfrak{T})$ of interpretations with $\mathfrak{H} \subseteq \mathfrak{T}$ pointwise. It is an *HT-model* of a dataset $\mathcal{D}$ if $\mathfrak{H}$ satisfies every fact of $\mathcal{D}$, and of a program $\Pi$ if, for every ground instance of a rule of $\Pi$ as above and every $t \in \mathbb{Q}$: (1) if $\mathfrak{H}$ satisfies $M_1, \dots, M_k$ at $t$ and $\mathfrak{T}$ satisfies none of $M_{k+1}, \dots, M_m$ at $t$, then $\mathfrak{H}$ satisfies $M$ at $t$; and (2) the same with $\mathfrak{T}$ in place of $\mathfrak{H}$ in the positive part and the head. If $(\mathfrak{T}, \mathfrak{T})$ is an HT-model of $\Pi$ and $\mathcal{D}$, the set of all $\mathfrak{H}$ such that $(\mathfrak{H}, \mathfrak{T})$ is an HT-model of $\Pi$ and $\mathcal{D}$ has a least element $\mathfrak{H}^{\mathfrak{T}}_{\Pi,\mathcal{D}}$. An interpretation $\mathfrak{T}$ is a *stable model* of $\Pi$ and $\mathcal{D}$ if $(\mathfrak{T}, \mathfrak{T})$ is an HT-model of $\Pi$ and $\mathcal{D}$ and $\mathfrak{H}^{\mathfrak{T}}_{\Pi,\mathcal{D}} = \mathfrak{T}$. For programs without negated body atoms the stable models are exactly the least models.

**Theorem (Wałęga, Tena Cucala, Cuenca Grau and Kostylev).** Checking whether a propositional forward-propagating DatalogMTL program with negation and a bounded dataset have a stable model over the rational timeline is undecidable with respect to data complexity: there is a fixed propositional forward-propagating program $\Pi$ such that no algorithm decides, given a bounded dataset $\mathcal{D}$, whether $\Pi$ and $\mathcal{D}$ have a stable model over $\mathbb{Q}$.

Over the rational timeline the same reasoning problems are PSPACE-complete in data complexity for programs without negation and for stratified negation. Over the integer timeline existence of a stable model is decidable in EXPSPACE in data complexity, and PSPACE-complete in data complexity for forward-propagating programs and bounded datasets (Theorems 5.14 and 5.18 of the copy read).

## Depends on

- [Datalog programs and the immediate consequence operator](../../datalog-programs-and-the-immediate-consequence-operator.md)
- [Stable models of a normal logic program](../../../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The reduction is from halting of a fixed deterministic single-tape Turing machine $M$ on input words, where $M$ is chosen with an undecidable halting problem and, without loss of generality, never moves left of its first cell. A fixed propositional forward-propagating program $\Pi_M$ is built, and each input word $w$ is mapped (in $\mathrm{AC}^0$) to a bounded dataset $\mathcal{D}_w$ such that $M$ halts on $w$ if and only if $\Pi_M$ and $\mathcal{D}_w$ have no stable model. The $i$-th configuration occupies the interval $[2i, 2i+2)$: a proposition $S_q$ at a point of $[2i, 2i+1]$ records the state $q$, and $|w| + i$ points of $(2i+1, 2i+2)$ carry propositions $C_s$ for the cell contents and $H$ for the head position. A proposition $N$ holds at a single new point of $(2i+1, 2i+2)$ beyond the last encoded cell, which lets the number of encoded cells grow by one per configuration; propositions $\overline{N}$ and $\overline{H}$ simulate the negations of $N$ and $H$, $\overline{C}$ marks points not used for cells, and $L$ serves left-moving transitions. The rules copy each configuration to the next one according to the transition function, and the construction ensures that a stable model exists exactly when the computation never reaches the halting state.

## Sources

- Przemysław A. Wałęga, David J. Tena Cucala, Bernardo Cuenca Grau and Egor V. Kostylev, "The Stable Model Semantics of Datalog with Metric Temporal Operators", Theory and Practice of Logic Programming 24(1), pp. 22–56, 2024, <https://doi.org/10.1017/S1471068423000315>; read in arXiv:2306.07625v1, <https://arxiv.org/abs/2306.07625v1>: Section 2 (timelines, intervals, metric atoms and their semantics), Definitions 3.1, 3.2 and 3.5 (rules and forward-propagating programs, HT-models, stable models), Theorem 3.4 (least interpretation), Theorem 4.1 (main statement) and Theorems 5.14 and 5.18 (integer timeline), numbered as in arXiv:2306.07625v1.
