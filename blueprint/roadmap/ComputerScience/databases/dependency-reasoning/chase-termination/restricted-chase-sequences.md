# Restricted chase sequences and their termination

A restricted chase sequence for a knowledge base starts from its database and repeatedly applies a loaded trigger that is not yet satisfied, subject to fairness; the knowledge base terminates universally when every such sequence is finite, and a rule set does when every knowledge base built from it does.

**Rules and knowledge bases.** Fix disjoint countably infinite sets of predicates (each with an arity), variables, constants and nulls; terms are variables, constants and nulls. An atom is $P(\vec t)$ with $P$ of arity $|\vec t|$, and a fact is a variable-free atom. An *(existential) rule* $\rho$ is a closed formula

$$
\forall \vec x\, \vec y.\ B[\vec x, \vec y] \to \exists \vec z.\ H[\vec y, \vec z],
$$

where $\vec x, \vec y, \vec z$ are pairwise disjoint lists of variables and $B$, $H$ are null-free conjunctions of atoms whose variables are exactly those of $\vec x, \vec y$ and of $\vec y, \vec z$ respectively, with $H$ non-empty; $\vec y$ is the *frontier* of $\rho$. Bodies may be empty. A *database* is a finite set of facts without nulls, and a *knowledge base* (KB) is a pair $\langle R, D \rangle$ of a finite rule set $R$ and a database $D$.

**Triggers.** A trigger is a pair $\langle \rho, \sigma \rangle$ of a rule and a substitution defined exactly on the universally quantified variables of $\rho$. It is *loaded* for a fact set $F$ if $\sigma(B) \subseteq F$, and *obsolete* for $F$ if some extension $\sigma'$ of $\sigma$ to the existential variables satisfies $\sigma'(H) \subseteq F$. If it is not obsolete, its *output* is $\sigma'(H)$ for an extension $\sigma'$ mapping each existential variable to a fresh null.

**Chase sequences.** A *(restricted) chase derivation* for $\langle R, D \rangle$ is a finite or infinite sequence $F_0, F_1, \dots$ with $F_0 = D$ and, for each $i$ with $F_{i+1}$ defined, $F_{i+1} = F_i \cup \mathrm{output}(\lambda)$ for an $R$-trigger $\lambda$ that is loaded and not obsolete for $F_i$; if no such trigger exists for $F_i$, the sequence ends at $F_i$. It is a *(restricted) chase sequence* if it is also *fair*: for every $R$-trigger $\lambda$ and every $i$ such that $\lambda$ is loaded for $F_i$, there is $j \ge i$ such that $\lambda$ is obsolete for $F_j$. A chase sequence *terminates* if it is finite.

**Termination classes.** A KB *existentially terminates* if it admits a terminating chase sequence and *universally terminates* if all its chase sequences terminate. A rule set $R$ existentially (universally) terminates if every KB $\langle R, D \rangle$ does. The classes of universally terminating KBs and rule sets are written $\mathsf{CT}^{\mathrm{rest}}_{\mathrm{KB}\,\forall}$ and $\mathsf{CT}^{\mathrm{rest}}_{R\,\forall}$.

Rules are tuple-generating dependencies without equality. Fairness matters only for infinite sequences: without it an infinite derivation can starve a trigger forever, its result need not be a model of the KB, and the termination classes change. The result of any chase sequence is a universal model of the KB. Each step applies a restricted chase step in the sense of [tuple-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md). This is the standard chase of Grahne and Onet: their class $\mathsf{CT}^{\mathsf{std}}_{\forall\forall}$ is $\mathsf{CT}^{\mathrm{rest}}_{R\,\forall}$, and their $\mathsf{CT}^{\mathsf{std}}_{\forall\exists}$ is the class of existentially terminating rule sets (Section 3 of the source). The source compares these classes with the earlier notation, where a rule set is classified for one fixed database at a time, and shows by a many-one reduction in each direction that fixing the database changes nothing up to reducibility.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)

## Proof depends on

None.


## Sources

- David Carral, Lukas Gerlach, Lucas Larroque and Michaël Thomazo, "Restricted Chase Termination: You Want More than Fairness", *Proceedings of the ACM on Management of Data* 3(2) (PODS 2025), 1–17, 2025, <https://doi.org/10.1145/3725246>; read as arXiv:2505.16551v1, <https://arxiv.org/abs/2505.16551v1>: Section 2 (Preliminaries) with Definition 3 (chase derivations and sequences), and Proposition 8 on fixed databases in Section 3 ("Related Work"), in the numbering of that version.
