# Regular path query entailment under existential rules

An existential rule derives a new atom, possibly with fresh existentially quantified values, from a conjunction of atoms. A Boolean regular path query asks for a path between two terms whose edge labels form a word of a regular language. Entailment asks whether every model of a database and a ruleset satisfies the query.

**Rules and rulesets (Ostropolski-Nalewaja and Rudolph).** An *existential rule* is a first-order sentence $\forall \bar{x} \bar{y}\, (\alpha(\bar{x}, \bar{y}) \to \exists \bar{z}\, \beta(\bar{y}, \bar{z}))$ with $\alpha$ a conjunction of atoms (the body) and $\beta$ a single atom (the head); a *ruleset* is a finite set of rules. A database is a finite set of facts; an instance $I$ is a *model* of a database $D$ and a ruleset $\mathcal{R}$ if $D \subseteq I$ and $I$ satisfies every rule. A query $Q$ is *entailed* by $(D, \mathcal{R})$ if every model satisfies $Q$.

- $\mathcal{R}$ is a *finite unification set* (fus) if every union of conjunctive queries $Q$ has a UCQ rewriting $Q'$ under $\mathcal{R}$: for every database $D$ and tuple $\bar{a}$ of its constants, $(D, \mathcal{R})$ entails $Q(\bar{a})$ exactly when $D$ satisfies $Q'(\bar{a})$.
- $\mathcal{R}$ over a signature $\Sigma$ is *sticky* (following Calì, Gottlob and Pieris) if there is a marking assigning to each predicate a set of marked positions such that, in every rule, each join variable (a variable occurring more than once in the body) and each variable at a marked position of a body atom occurs at a marked position of the head atom.

**Path queries.** For a regular language $L$ over binary predicates, the atom $L(s, t)$ is true in an instance when there is a directed path from $s$ to $t$ whose sequence of edge labels is a word of $L$; a *Boolean regular path query* (RPQ) is $\exists x\, y\, L(x, y)$ with $x$ and $y$ distinct variables and $L$ given by a regular expression. A path may have length $0$, so if $L$ contains the empty word, $L(s, s)$ holds for every term $s$ and the query holds in every nonempty instance. A *higher-arity regular path query* (HRPQ) also lets the regular expression use predicates of higher arity, of which only the first two positions form the path edges.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Language denoted by a regular expression](../../../../TheoryOfComputation/regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md)

## Proof depends on

None.

## Expansion

Sticky rulesets are fus, and fus coincides with the class of rulesets with the bounded derivation-depth property. For conjunctive queries, entailment under fus rulesets is decidable by rewriting; regular path queries are not first-order, so rewritability does not settle them.

## Sources

- Piotr Ostropolski-Nalewaja and Sebastian Rudolph, "The Sticky Path to Expressive Querying: Decidability of Navigational Queries under Existential Rules", Proceedings of the 21st International Conference on Principles of Knowledge Representation and Reasoning (KR 2024), pp. 574–584, 2024, <https://doi.org/10.24963/kr.2024/54>; Section 2 (preliminaries: Definition 2 of UCQ rewritings, Lemma 3 on fus and bdd rulesets, Definition 4 of sticky rulesets) and the definition of higher-arity regular path queries in Section 5 of arXiv:2407.14384v1 (the copy read), <https://arxiv.org/abs/2407.14384v1>.
