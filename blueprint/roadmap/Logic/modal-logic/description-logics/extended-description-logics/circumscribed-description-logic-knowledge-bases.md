# Circumscribed description logic knowledge bases

A circumscribed knowledge base keeps only those models of a TBox and an ABox in which designated concept and role names are minimal, given fixed and varying predicates and a priority order on the minimized ones; reasoning then ranges over these preferred models only.

**Circumscription patterns.** A *circumscription pattern* is a tuple $CP = ({\prec}, M, F, V)$ in which $M$, $F$ and $V$ are mutually disjoint sets of concept and role names, the *minimized*, *fixed* and *varying* predicates, and $\prec$ is a strict partial order on $M$. For interpretations $\mathcal I, \mathcal J$, put $\mathcal I <_{CP} \mathcal J$ iff

1. $\Delta^{\mathcal I} = \Delta^{\mathcal J}$ and $a^{\mathcal I} = a^{\mathcal J}$ for every individual name $a$;
2. $p^{\mathcal I} = p^{\mathcal J}$ for every $p \in F$;
3. for every $p \in M$ with $p^{\mathcal I} \not\subseteq p^{\mathcal J}$ there is $q \in M$ with $q \prec p$ and $q^{\mathcal I} \subsetneq q^{\mathcal J}$;
4. there is $p \in M$ with $p^{\mathcal I} \subsetneq p^{\mathcal J}$ such that $q^{\mathcal I} = q^{\mathcal J}$ for all $q \in M$ with $q \prec p$.

**Circumscribed knowledge bases.** A *circumscribed knowledge base* (cKB) is an expression $\mathrm{Circ}_{CP}(\mathcal T, \mathcal A)$ with $\mathcal T$ a TBox, $\mathcal A$ an ABox and $CP = ({\prec}, M, F, V)$ a circumscription pattern such that $M$, $F$ and $V$ partition the predicates used in $\mathcal T$ and $\mathcal A$. An interpretation $\mathcal I$ is a *model* of the cKB if it is a model of $\mathcal T$ and $\mathcal A$ and no model $\mathcal I'$ of $\mathcal T$ and $\mathcal A$ satisfies $\mathcal I' <_{CP} \mathcal I$. A concept $C$ is *satisfiable* with respect to the cKB if some model $\mathcal I$ of it has $C^{\mathcal I} \neq \emptyset$, and an individual $a$ is an *instance* of $C$ if $a^{\mathcal I} \in C^{\mathcal I}$ in every model. The cKB is *role-fixing* if $M$ contains no role names, and *role-minimizing* if $F$ contains no role names; it is *concept-circumscribed* if $M \cup F$ contains only concept names.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)
- [Partially ordered set](../../../../Order/ordered-sets/partial-order.md)

## Proof depends on

None.

## Expansion

With the empty order $\prec$ this is parallel circumscription; a total order gives prioritized circumscription. Satisfiability, subsumption and instance checking with respect to cKBs reduce to one another in polynomial time.

## Sources

- P. A. Bonatti, C. Lutz and F. Wolter, "The complexity of circumscription in DLs", *Journal of Artificial Intelligence Research* 35:717–773, 2009, <https://doi.org/10.1613/jair.2763>; read as arXiv:1401.3476v1, <https://arxiv.org/abs/1401.3476v1>: Section 2.2 (Definitions 1, 2 and 3), Definition 19 and Definition 23.
