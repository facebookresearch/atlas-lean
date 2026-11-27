# Description logics with abstraction and refinement

The description logic ALCHI^abs describes a domain at several levels of abstraction organized in a tree: each level carries an ordinary interpretation, and refinement and abstraction statements relate an object on a coarser level to an ensemble of objects on a finer level described by a conjunctive query.

**Ontologies.** Fix a countable set $\mathbb A$ of abstraction levels. An $\mathcal{ALCHI}^{abs}$-ontology is a finite set of statements of the forms

- labeled concept inclusions $C \sqsubseteq_L D$ and labeled role inclusions $R \sqsubseteq_L S$;
- concept refinements $L{:}q(\bar x)\ \underline{\mathrm{refines}}\ L'{:}C$ and concept abstractions $L'{:}C\ \underline{\mathrm{abstracts}}\ L{:}q(\bar x)$;
- role refinements $L{:}q(\bar x, \bar y)\ \underline{\mathrm{refines}}\ L'{:}q_R(x, y)$ and role abstractions $L'{:}R\ \underline{\mathrm{abstracts}}\ L{:}q(\bar x, \bar y)$,

where $L, L' \in \mathbb A$, $C, D$ are ALCI concepts, $R, S$ are roles, $q$ ranges over *full* conjunctive queries (without quantified variables), connected in abstraction statements, and $q_R$ over full queries of the form $C_1(x) \wedge R(x, y) \wedge C_2(y)$. Fragments are named by the admitted statements: $[cr]$, $[ca]$, $[rr]$, $[ra]$ for concept refinement, concept abstraction, role refinement and role abstraction; $\mathcal{ALC}^{abs}$, $\mathcal{ALCI}^{abs}$ and $\mathcal{EL}^{abs}$ are defined analogously from ALC, ALCI and EL.

**Semantics.** An *$\mathbb A$-interpretation* $\mathcal I = (\mathbb A_{\mathcal I}, \prec, (\mathcal I_L)_{L \in \mathbb A_{\mathcal I}}, \rho)$ consists of a set $\mathbb A_{\mathcal I} \subseteq \mathbb A$ of levels with a relation $\prec$ such that $(\mathbb A_{\mathcal I}, \{(L', L) \mid L \prec L'\})$ is a tree ($L \prec L'$: $L$ is finer than $L'$), interpretations $\mathcal I_L$ with pairwise disjoint domains, and a partial *refinement function* $\rho$ mapping an object $d$ of level $L(d)$ and a level $L \prec L(d)$ to an *$L$-ensemble* $\rho_L(d)$, a nonempty tuple of objects of level $L$, such that every object occurs in at most one ensemble of its level. $\mathcal I$ satisfies $C \sqsubseteq_L D$ if $C^{\mathcal I_L} \subseteq D^{\mathcal I_L}$; it satisfies $L{:}q(\bar x)\ \underline{\mathrm{refines}}\ L'{:}C$ if $L \prec L'$ and every $d \in C^{\mathcal I_{L'}}$ has $\rho_L(d) \in q(\mathcal I_L)$; it satisfies $L'{:}C\ \underline{\mathrm{abstracts}}\ L{:}q(\bar x)$ if $L \prec L'$ and every answer $\bar e \in q(\mathcal I_L)$ is $\rho_L(d)$ for some $d \in C^{\mathcal I_{L'}}$; role refinements and abstractions are analogous for the ensembles of the two related objects. *Satisfiability* asks, given an ontology $\mathcal O$, an ALCI concept $C$ and a level $L$, whether some model $\mathcal I$ of $\mathcal O$ has $C^{\mathcal I_L} \neq \emptyset$.

**Variations.** Under the *repetition-free semantics* ensembles are tuples without repeated elements; under the *DAG semantics* the levels may form a directed acyclic graph instead of a tree; the *extension with quantified variables* admits conjunctive queries with quantified variables in refinement and abstraction statements.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

None.

## Expansion

A concept refinement says that every instance of $C$ on the coarser level $L'$ refines into an ensemble of $|\bar x|$ objects on level $L$ satisfying $q$; a concept abstraction says conversely that every such ensemble abstracts into an instance of $C$. Because ensembles may not overlap, abstraction statements can express inconsistency: $\top \sqsubseteq_{L_2} \exists r.\exists r.\top$ together with $L_1{:}\top\ \underline{\mathrm{abstracts}}\ L_2{:}r(x, y)$ has no model. Satisfiability in $\mathcal{ALCHI}^{abs}$ is decidable in 2EXPTIME, and in its fragment with concept refinement only it is EXPTIME-complete.

## Sources

- C. Lutz and L. Schulze, "Description logics with abstraction and refinement", in *Proceedings of the 20th International Conference on Principles of Knowledge Representation and Reasoning (KR 2023)*, 2023, pp. 492–501, <https://doi.org/10.24963/kr.2023/48>; read as arXiv:2306.03717v3, <https://arxiv.org/abs/2306.03717v3>: Section 2 (base DLs and conjunctive queries), Section 3 (ontologies, $\mathbb A$-interpretations, satisfiability), Theorems 1 and 2, and Sections 6.2 to 6.4 (the three variations).
