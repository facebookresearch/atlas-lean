# The description logic ALCSCC

ALCSCC extends the description logic ALC with successor restrictions succ(con), in which con is a constraint of the logic QFBAPA (Boolean algebra with Presburger arithmetic) over the sets of role successors of an individual, so that cardinalities of successor sets can be compared.

**Definition.** *QFBAPA.* Set terms are built from set variables and the constants $\emptyset$, $\mathcal U$ by $\cap$, $\cup$ and complement; set constraints are $s \subseteq t$ and $s = t$; Presburger expressions are $n_0 + n_1 t_1 + \cdots + n_k t_k$ with $n_i \in \mathbb N$ and each $t_i$ a cardinality $|s_i|$ of a set term or an integer variable, and numerical constraints are $\ell = \ell'$, $\ell < \ell'$ and $n \mid \ell$. A QFBAPA formula is a Boolean combination of set and numerical constraints, and a solution assigns a finite set to $\mathcal U$, subsets of it to set variables and integers to integer variables.

*ALCSCC.* Given disjoint sets $N_C$, $N_R$ of concept and role names, concepts are built from concept names by $\neg$, $\sqcap$ and *successor restrictions* $\mathrm{succ}(\mathit{con})$, where $\mathit{con}$ is a QFBAPA set or numerical constraint, without integer variables, whose set variables are role names and concepts. An interpretation $\mathcal I$ has a nonempty domain $\Delta^{\mathcal I}$, sets $A^{\mathcal I}$ and relations $r^{\mathcal I}$, and must be *finitely branching*: the set $\mathrm{ars}^{\mathcal I}(d) = \bigcup_{r \in N_R} r^{\mathcal I}(d)$ of all role successors of each $d$ is finite. Each $d$ induces the QFBAPA assignment $\sigma_d(\mathcal U) = \mathrm{ars}^{\mathcal I}(d)$, $\sigma_d(r) = r^{\mathcal I}(d)$ and $\sigma_d(C) = C^{\mathcal I} \cap \mathrm{ars}^{\mathcal I}(d)$, and $d \in \mathrm{succ}(\mathit{con})^{\mathcal I}$ iff $\sigma_d$ is a solution of $\mathit{con}$. A *TBox* is a finite set of concept inclusions $C \sqsubseteq D$; it is *consistent* if some finitely branching interpretation satisfies $C^{\mathcal I} \subseteq D^{\mathcal I}$ for all its inclusions.

*Extensions.* $\mathcal{SSCC}$ adds *transitivity axioms* $\mathrm{trans}(r)$ requiring $r^{\mathcal I}$ to be transitive. $\mathcal{ALCSCC}^{++}$ is [the description logic ALCSCC++ with global and local cardinality constraints](alcscc-with-global-and-local-cardinality.md): it replaces successor restrictions by $\mathrm{sat}(\mathit{con})$, interpreted with $\sigma(\mathcal U) = \Delta^{\mathcal I}$ and $\sigma(r) = r^{\mathcal I}(d)$ over finite interpretations. With a concrete domain $\mathcal D = (D, P_1^{\mathcal D}, \ldots)$ and feature names $f$ interpreted as partial functions into $D$, *feature roles* $P(\alpha_1, \ldots, \alpha_k)$, with pointers $\alpha_i$ of the form $f$ or $\mathit{next}\,f$, relate $d$ to $e$ iff the values of the features at $d$ (for $f$) and at $e$ (for $\mathit{next}\,f$) satisfy $P$; in $\mathcal{ALCSCC}^{++}(\mathcal D)$ they may occur as set variables in sat-restrictions. A concrete domain is *JD* if equality on $D$ is definable by a quantifier-free, equality-free first-order formula over its signature.

## Depends on

- [The description logic ALCSCC++ with global and local cardinality constraints](alcscc-with-global-and-local-cardinality.md)
- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

None.

## Expansion

Existential restrictions are expressible: $\exists r.C = \mathrm{succ}(|r \cap C| \ge 1)$, and $\mathrm{succ}(|\mathit{own} \cap \mathit{Car}| = |\mathit{child} \cap \mathit{Human}|)$ describes individuals owning as many cars as they have children, which full first-order logic cannot express. Satisfiability of QFBAPA is NP-complete, consistency of ALCSCC TBoxes is EXPTIME-complete like ALC, and consistency of $\mathcal{ALCSCC}^{++}$ TBoxes is NEXPTIME-complete.

## Sources

- F. Baader, S. Borgwardt, F. De Bortoli and P. Koopmann, "Concrete Domains Meet Expressive Cardinality Restrictions in Description Logics", in *Automated Deduction – CADE 30*, Lecture Notes in Computer Science 15943, Springer, 2025, pp. 676–695, <https://doi.org/10.1007/978-3-031-99984-0_35>; numbers from the extended version arXiv:2505.21103v1, <https://arxiv.org/abs/2505.21103v1>: Section 2 (concrete domains, JD, QFBAPA), Section 3 (ALCO, ALCOSCC, feature roles, TBoxes, consistency) and Section 6 (sat-restrictions, ALCSCC++(D), transitivity axioms).
