# Chase termination and bts membership are undecidable in a class with decidable query entailment

Decidable entailment of Boolean conjunctive queries does not make chase termination decidable: a concrete, linear-time recognizable class of existential rule sets has decidable query entailment, yet termination of the oblivious, semi-oblivious, restricted and core chases and membership in the bounded-treewidth class bts are undecidable in it.

**Setting (Larroque and Manière).** An *existential rule* is a first-order sentence $\forall \bar{x}\, \forall \bar{y}\, (B[\bar{x}, \bar{y}] \to \exists \bar{z}\, H[\bar{y}, \bar{z}])$ with conjunctions of atoms $B$ (body) and $H$ (head) without constants; $\bar{y}$ is its frontier. An *instance* is an existentially closed conjunction of atoms, identified with a set of atoms; a Boolean conjunctive query (BCQ) has the same form. A knowledge base $\langle \mathcal{R}, \mathcal{I} \rangle$ pairs a finite rule set with an instance, and *BCQ entailment* asks, given a knowledge base and a BCQ $q$, whether $\langle \mathcal{R}, \mathcal{I} \rangle \models q$; it is undecidable for arbitrary rule sets.

A *trigger* on an instance $\mathcal{I}$ is a pair of a rule $B \to \exists \bar{z}\, H$ and a homomorphism $\pi$ from $B$ to $\mathcal{I}$; its output is $\pi(H)$ with each $z \in \bar{z}$ replaced by a fresh variable. A derivation applies triggers one at a time, each adding atoms not yet present. A trigger is *oblivious-applicable* if its output is not contained in $\mathcal{I}$; *semi-oblivious-applicable* if no trigger for the same rule agreeing with it on the frontier has its output in $\mathcal{I}$; *restricted-applicable* if there is no retraction from $\mathcal{I}$ plus the output to $\mathcal{I}$; and *equivalent-applicable* if there is no homomorphism from $\mathcal{I}$ plus the output to $\mathcal{I}$. For each variant $\mathbb{X}$, an $\mathbb{X}$-derivation uses only $\mathbb{X}$-applicable triggers, it is *fair* if every trigger applicable at some step stops being applicable later, and it is *terminating* if it is fair and finite. $\mathrm{CT}^{\mathbb{X}}_{\forall}$ (resp. $\mathrm{CT}^{\mathbb{X}}_{\exists}$) is the class of rule sets $\mathcal{R}$ such that every (resp. some) fair $\mathbb{X}$-derivation from every knowledge base $\langle \mathcal{R}, \mathcal{I} \rangle$ is finite. The equivalent chase halts exactly when the knowledge base has a finite universal model, as the core chase does. A rule set is *bts* (bounded treewidth set) if, for every instance, the universal model produced by the chase has bounded treewidth; bts contains every class $\mathrm{CT}^{\mathbb{X}}_{Q}$. A class of rule sets is *concrete* if membership in it is decidable.

**Theorem (Larroque and Manière).** There is a concrete class $\mathcal{C}$ of sets of existential rules such that:

1. chase termination is undecidable in $\mathcal{C}$ for the oblivious, semi-oblivious, restricted and core chases;
2. bts membership is undecidable in $\mathcal{C}$;
3. BCQ entailment is decidable in $\mathcal{C}$.

The class consists of one rule set $\mathcal{R}_{\mathcal{M}}$ for each three-counter machine $\mathcal{M}$ and is recognizable in linear time. If $\mathcal{M}$ halts, the $\mathbb{X}$-chase terminates on $\langle \mathcal{I}, \mathcal{R}_{\mathcal{M}} \rangle$ for every instance $\mathcal{I}$ and every variant $\mathbb{X}$; if $\mathcal{M}$ does not halt, no $\mathbb{X}$-chase sequence from $\langle \{\mathsf{End}(w)\}, \mathcal{R}_{\mathcal{M}} \rangle$ terminates (Theorems 16 and 14 of the copy read). Hence membership of $\mathcal{R}_{\mathcal{M}}$ in $\mathrm{CT}^{\mathbb{X}}_{\forall}$ and in $\mathrm{CT}^{\mathbb{X}}_{\exists}$ is undecidable for each variant, and $\mathcal{R}_{\mathcal{M}}$ is bts if and only if $\mathcal{M}$ halts (Theorem 17). For finite unification sets the analogous question was already settled negatively by the undecidability of Datalog boundedness.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Chase variants and their termination classes](chase-variants-and-termination-classes.md)
- [Restricted chase sequences and their termination](restricted-chase-sequences.md)
- [Treewidth of a conjunctive query](../../tractable-conjunctive-queries/treewidth-of-a-conjunctive-query.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

A three-counter machine is a two-counter machine with an extra counter that increases at every step, and its halting problem is undecidable. Following Gogacz and Marcinkowski, configurations are coded by natural numbers through prime factorizations, so that one step multiplies the code by a fixed fraction depending on the code modulo a fixed number. The rule set builds a chain of elements linked by a successor predicate and ending in a "well of positivity" $w$; each element simulates $\mathcal{M}$ from its own point of view with Datalog rules, and the single existential rule lets an element create a predecessor only when its simulation reaches $w$. The chain is infinite exactly when $\mathcal{M}$ never halts. A predicate $\mathsf{S}_0$ without a self-loop at $w$ blocks the homomorphisms that would let the restricted and equivalent chases stop early, and a flooding mechanism connects every element whose simulation reaches $w$ to all its successors. Termination when $\mathcal{M}$ halts goes through the critical instance; non-termination gives an infinite clique in the graph of one binary predicate, which excludes bts. A good expansion links pages for: termination of the oblivious chase on the critical instance implies termination on all instances (Marnette); the equivalent and core chases halt exactly when a finite universal model exists; the inclusions among the classes $\mathrm{CT}^{\mathbb{X}}_{Q}$ (Proposition 8 of the copy read); and an infinite clique in the graph of a binary predicate in a chase result rules out bts (Proposition 9, after Calì, Gottlob and Kifer).

## Sources

- Lucas Larroque and Quentin Manière, "Will My Favorite Chases Terminate If Evaluating Conjunctive Queries Does? One Does Not Simply Decide This", Proceedings of the Thirty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2026), pp. 3935–3942, 2026, <https://doi.org/10.24963/ijcai.2026/438>; read in arXiv:2605.12349v1, <https://arxiv.org/abs/2605.12349v1>: Theorem 1 (main statement), Definitions 2–5 and 7 (rules, triggers, derivations, applicability, chase variants, chase-terminating sets), Propositions 8 and 9, Theorems 14, 16 and 17, numbered as in arXiv:2605.12349v1.
