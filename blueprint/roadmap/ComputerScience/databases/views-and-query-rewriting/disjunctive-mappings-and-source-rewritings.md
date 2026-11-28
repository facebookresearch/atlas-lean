# Disjunctive mappings and UCQ rewritings over the source

A disjunctive mapping is a finite set of disjunctive existential rules whose bodies use source predicates and whose heads use disjoint target predicates. A union of conjunctive queries over the target has a UCQ rewriting over the source if a finite union of conjunctive queries over the source has the same certain answers on every source fact base.

**Disjunctive existential rules.** Atoms are built from predicates, constants and variables. A disjunctive existential rule is a closed formula

$$
\forall \vec{x}\, \forall \vec{y}\, \Big( B[\vec{x}, \vec{y}] \rightarrow \bigvee_{i=1}^{n} \exists \vec{z}_i\, H_i[\vec{x}_i, \vec{z}_i] \Big)
$$

with $n \ge 1$, where the body $B$ and the head disjuncts $H_i$ are nonempty finite conjunctions of atoms, the variables of $B$ are $\vec{x} \cup \vec{y}$, those of $H_i$ are $\vec{x}_i \cup \vec{z}_i$, $\vec{x} = \bigcup_i \vec{x}_i$ (the frontier), and $\vec{x}$, $\vec{y}$ and the $\vec{z}_i$ are pairwise disjoint. The rule is conjunctive if $n = 1$ (a tuple-generating dependency) and datalog if it has no existential variables. A fact base is a finite set of atoms, read as an existentially closed conjunction; $F, \mathcal{R} \models Q$ is classical entailment from the fact base $F$ together with the rules $\mathcal{R}$.

**Queries and rewritings.** Queries are Boolean conjunctive queries (CQs) and unions of them (UCQs), viewed as sets of CQs. A rewriting of a UCQ $\mathcal{Q}$ with a rule set $\mathcal{R}$ is a possibly infinite set $\mathcal{Q}'$ of CQs such that $F \models \mathcal{Q}'$ implies $F, \mathcal{R} \models \mathcal{Q}$ for every fact base $F$; it is complete if, conversely, $F, \mathcal{R} \models \mathcal{Q}$ implies $F \models \mathcal{Q}'$ for every fact base $F$. A finite complete rewriting is a UCQ-rewriting, and $(\mathcal{Q}, \mathcal{R})$ is UCQ-rewritable if it has one.

**Mappings.** For disjoint finite sets $\mathcal{S}$ (source) and $\mathcal{T}$ (target) of predicates, an $\mathcal{S}$-to-$\mathcal{T}$ rule has its body over $\mathcal{S}$ and its head over $\mathcal{T}$, and a disjunctive mapping $\mathcal{M}$ on $(\mathcal{S}, \mathcal{T})$ is a finite set of disjunctive $\mathcal{S}$-to-$\mathcal{T}$ rules. For a UCQ $\mathcal{Q}$ over $\mathcal{T}$, an $\mathcal{S}$-rewriting is a rewriting whose CQs use only predicates of $\mathcal{S}$; it is complete if $F, \mathcal{M} \models \mathcal{Q}$ implies $F \models \mathcal{Q}'$ for every fact base $F$ over $\mathcal{S}$, and a finite complete $\mathcal{S}$-rewriting is a UCQ-$\mathcal{S}$-rewriting.

**Disjunctive mapping rewritability.** Given a disjunctive mapping $\mathcal{M}$ on $(\mathcal{S}, \mathcal{T})$ and a UCQ $\mathcal{Q}$ over $\mathcal{T}$, decide whether $(\mathcal{Q}, \mathcal{M})$ has a UCQ-$\mathcal{S}$-rewriting.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

The chase of a fact base with a mapping is always finite. Rewritings over the source can exist where rewritings over all predicates do not: for the rule $p(x, y) \rightarrow t_1(x) \vee t_2(y)$ and the CQ $t_1(u) \wedge t_2(u)$ the empty set is a UCQ-$\mathcal{S}$-rewriting, while the pair has no UCQ-rewriting over $\mathcal{S} \cup \mathcal{T}$. With the mapping $e(x, y) \rightarrow \hat{e}(x, y)$, $v(x) \rightarrow g(x) \vee r(x)$ and the UCQ asking for two adjacent vertices of the same color, every complete $\mathcal{S}$-rewriting contains CQs describing all cycles of odd length, that is, it defines non-2-colorability.

## Sources

- Michel Leclère, Marie-Laure Mugnier and Guillaume Pérution-Kihli, "Query Rewriting with Disjunctive Existential Rules and Mappings", in *Proceedings of the 20th International Conference on Principles of Knowledge Representation and Reasoning (KR 2023)*, pp. 429–439, 2023, <https://doi.org/10.24963/kr.2023/42>; read in arXiv:2306.05973v1, <https://arxiv.org/abs/2306.05973v1>: Section 2 (rules, knowledge bases, UCQ rewritability, mappings) and Section 5 (mapping rewritings and the decision problem, with the two examples there), in the section order of that version.
