# Universal restricted chase termination of knowledge bases is Π¹₁-complete

Deciding whether every fair restricted chase sequence of a given knowledge base is finite is complete for the class $\Pi^1_1$ of the analytical hierarchy, so the problem is not even arithmetical.

**Theorem.** The class $\mathsf{CT}^{\mathrm{rest}}_{\mathrm{KB}\,\forall}$ of knowledge bases $\langle R, D \rangle$ (a finite set $R$ of existential rules and a database $D$) all of whose [restricted chase sequences](restricted-chase-sequences.md) are finite is $\Pi^1_1$-complete.

## Depends on

- [Restricted chase sequences and their termination](restricted-chase-sequences.md)

## Proof depends on

None.

## Expansion

*Membership.* From a rule set $R$ one builds a nondeterministic Turing machine $\mathcal M_R$ that, started on an encoding of a database, guesses a chase derivation $F_0, F_1, \dots$ trigger by trigger and keeps a checkpoint $j$: whenever every trigger that was loaded and not obsolete for $F_j$ has become obsolete, it advances $j$ and visits a designated state $q_r$. A run visits $q_r$ infinitely often exactly when it builds an infinite fair derivation, that is, an infinite chase sequence. Prefixing a step that writes $D$ reduces membership to *non-recurrence through $q_r$ on the empty word*: every run of the machine on the empty word visits $q_r$ only finitely often. That problem is $\Pi^1_1$-complete, by a reduction to and from well-foundedness of computable $\omega$-trees (Harel's classical $\Pi^1_1$-complete problem).

*Hardness.* Conversely, from a machine $M$ the source builds a database $D_\varepsilon$ and a rule set $R_M$ whose restricted chase simulates the runs of $M$ on the empty word, so that a non-terminating chase sequence exists exactly when some run visits $q_r$ infinitely often. The difficulty is that runs visiting $q_r$ finitely often, including non-halting ones, must yield terminating chase sequences although no computable bound on their length exists. The construction uses "emergency brakes" (a technique of Krötzsch, Marx and Rudolph): every new term is linked to a special brake term that is not yet marked as real; fairness eventually marks the brake real, after which all existential requirements are satisfied and the chase stops. The source stacks such brakes, each one responsible for stopping the simulation of runs that do not go on through $q_r$, so that only runs with infinitely many $q_r$-visits keep the chase growing forever.

The source notes that the "sometimes" variant (some chase sequence terminates) is recursively enumerable and complete for it, a result of Deutsch, Nash and Remmel.

## Sources

- David Carral, Lukas Gerlach, Lucas Larroque and Michaël Thomazo, "Restricted Chase Termination: You Want More than Fairness", *Proceedings of the ACM on Management of Data* 3(2) (PODS 2025), 1–17, 2025, <https://doi.org/10.1145/3725246>; read as arXiv:2505.16551v1, <https://arxiv.org/abs/2505.16551v1>: the theorem opening Section 5 (Knowledge base termination) and its two lemmas, and the propositions of Section 3 on non-recurrence of Turing machines.
