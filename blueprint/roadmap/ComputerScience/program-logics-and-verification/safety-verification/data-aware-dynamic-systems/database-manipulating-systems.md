# Database-manipulating systems

A database-manipulating system evolves a relational database by guarded actions: each step queries the current database, deletes some facts about the retrieved values and adds facts that may contain values never seen before in the run.

Fix a countably infinite domain $\Delta$ of data values and a relational schema $\mathcal R$, a finite set of relation names with arities; nullary relations are *propositions*. A database instance is a finite set of facts $R(e_1, \dots, e_a)$ over $\mathcal R$ and $\Delta$; a proposition $p$ is true in $I$ if $p() \in I$. The active domain $\mathrm{adom}(I)$ is the set of values occurring in $I$.

**Systems.** A *database-manipulating system* (DMS) over $\Delta$ and $\mathcal R$ is a pair $S = \langle I_0, \mathcal A \rangle$ where $I_0$ is an initial instance with empty active domain (it only fixes the truth values of the propositions) and $\mathcal A$ is a finite set of actions. An action $\alpha = \langle \vec u, \vec v, Q, \mathrm{Del}, \mathrm{Add} \rangle$ consists of disjoint finite sets $\vec u$ (parameters) and $\vec v$ (fresh-input variables) of variables, a *guard* $Q$, which is a first-order query with equality over $\mathcal R$ whose free variables are exactly $\vec u$ (as in the source, its quantifiers range over the active domain $\mathrm{adom}(I)$ of the current instance $I$: $I, \sigma \models \exists u.\, Q$ iff $I, \sigma[u \mapsto e] \models Q$ for some $e \in \mathrm{adom}(I)$, Appendix A), an instance $\mathrm{Del}$ over $\mathcal R$ whose values are variables from $\vec u$, and an instance $\mathrm{Add}$ whose values are variables from $\vec u \cup \vec v$ and in which every variable of $\vec v$ occurs.

**Runs.** A configuration is a pair $\langle I, H \rangle$ of an instance and a *history set* $H \subseteq \Delta$. A substitution $\sigma$ on $\vec u \cup \vec v$ instantiates $\alpha$ at $\langle I, H \rangle$ if $\sigma(\vec u) \subseteq \mathrm{adom}(I)$, $I, \sigma|_{\vec u} \models Q$, the values $\sigma(v)$ for $v \in \vec v$ are pairwise distinct and not in $H$; the step is then

$$
\langle I, H \rangle \xrightarrow{\alpha : \sigma} \langle (I \setminus \sigma(\mathrm{Del})) \cup \sigma(\mathrm{Add}),\ H \cup \sigma(\vec v) \rangle .
$$

Runs start from $\langle I_0, \emptyset \rangle$; as in the source, a run is an infinite sequence of steps, and a finite path is a prefix of a run when it can be extended. The *propositional reachability* problem asks, given a DMS $S$ and a proposition $p$ of its schema, whether some run reaches an instance in which $p$ is true. The two readings, finite paths or infinite runs, differ only at configurations with no successor, and adding an action with guard $\mathit{true}$ and empty $\mathrm{Del}$ and $\mathrm{Add}$, which is always enabled and changes nothing, removes that difference without changing which instances are reachable.

## Depends on

- [Relational schema](../../../databases/dependencies-and-the-chase/relational-schema.md)
- [Database instance](../../../databases/dependencies-and-the-chase/instance.md)
- [Active domain of a database instance](../../../databases/dependencies-and-the-chase/active-domain.md)
- [Relational calculus and domain independence](../../../databases/relational-calculus/relational-calculus-and-domain-independence.md)

## Proof depends on

None.

## Expansion

Fresh values are fresh with respect to everything seen so far in the run, not only the current active domain, so the system can create unboundedly many distinct objects; deletion lets it forget them. Guards may be restricted to unions of conjunctive queries. The source also defines a monadic second-order logic over runs, $\mathrm{MSO}$-$\mathrm{FO}$, and its model-checking problem, of which the complement of propositional reachability is a special case.

## Sources

- Parosh Aziz Abdulla, C. Aiswarya, Mohamed Faouzi Atig, Marco Montali and Othmane Rezine, "Recency-Bounded Verification of Dynamic Database-Driven Systems", in *Proceedings of the 35th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2016)*, ACM, 2016, pp. 195–210, <https://doi.org/10.1145/2902251.2902300>; read as the extended version arXiv:1604.03413v1, <https://arxiv.org/abs/1604.03413v1>: Sections 2 (Preliminaries) and 3 (Framework) and the example on propositional reachability in Section 4 of that version.
