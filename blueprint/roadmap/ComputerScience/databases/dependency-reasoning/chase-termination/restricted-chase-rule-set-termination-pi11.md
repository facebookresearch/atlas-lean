# Universal restricted chase termination of rule sets is Π¹₁-complete

Deciding whether a finite set of existential rules has only finite fair restricted chase sequences on every database is $\Pi^1_1$-complete, which settles an open upper bound and corrects an earlier claim that the problem is $\Pi^0_2$-complete.

**Theorem.** The class $\mathsf{CT}^{\mathrm{rest}}_{R\,\forall}$ of finite rule sets $R$ such that, for every database $D$, every [restricted chase sequence](restricted-chase-sequences.md) of $\langle R, D \rangle$ is finite, is $\Pi^1_1$-complete.

## Depends on

- [Restricted chase sequences and their termination](restricted-chase-sequences.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [Universal restricted chase termination of knowledge bases is Π¹₁-complete](restricted-chase-kb-termination-is-pi11-complete.md)

## Expansion

*Membership.* The machine $\mathcal M_R$ of the knowledge-base case halts at once on inputs that do not encode a database and otherwise guesses a restricted chase derivation, visiting $q_r$ each time all triggers pending at its current checkpoint have become obsolete. Then $R \in \mathsf{CT}^{\mathrm{rest}}_{R\,\forall}$ exactly when $\mathcal M_R$ is *universally non-recurring through $q_r$* (on every input every run visits $q_r$ finitely often), a $\Pi^1_1$-complete property.

*Hardness.* The reduction is from *robust non-recurrence through $q_r$*: every run from every configuration, reachable or not, visits $q_r$ finitely often; it is $\Pi^1_1$-complete by a reduction from non-recurrence on the empty word that checks, after every step, that the current configuration is reachable from the empty input. The rule set $R_M$ of the knowledge-base reduction is reused, with an argument that arbitrary databases only encode (possibly unreachable) configurations together with harmless junk.

Earlier work had claimed that the problem is $\Pi^0_2$-complete; the source shows that the $\Pi^0_2$ upper bound holds only when fairness is replaced by its breadth-first variant, and that with fairness the problem is not arithmetical.

## Sources

- David Carral, Lukas Gerlach, Lucas Larroque and Michaël Thomazo, "Restricted Chase Termination: You Want More than Fairness", *Proceedings of the ACM on Management of Data* 3(2) (PODS 2025), 1–17, 2025, <https://doi.org/10.1145/3725246>; read as arXiv:2505.16551v1, <https://arxiv.org/abs/2505.16551v1>: Theorem 23 in Section 5 ("Rule set termination") with Lemmas 24 and 25, robust non-recurrence in Section 2, and the discussion in Section 3 ("Related Work"), in the numbering of that version.
