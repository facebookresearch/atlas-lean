# Recursively enumerable logics between action logic and infinitary action logic are Σ⁰₁-complete

If a set of sequents lies between action logic and infinitary action logic and is recursively enumerable, it is $\Sigma^0_1$-complete. In particular action logic is $\Sigma^0_1$-complete.

**Theorem (Kuznetsov).** Let $\mathcal{L}$ be a set of sequents in the language of [action logic](action-logic-and-infinitary-action-logic.md) with $\mathbf{ACT} \subseteq \mathcal{L} \subseteq \mathbf{ACT}_\omega$. If $\mathcal{L}$ is recursively enumerable, then $\mathcal{L}$ is [$\Sigma^0_1$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)-complete: every recursively enumerable set many-one reduces to it. In particular $\mathbf{ACT}$ is $\Sigma^0_1$-complete.

Since $\mathbf{ACT}_\omega$ is $\Pi^0_1$-complete (Buszkowski and Palka), the hypothesis that $\mathcal{L}$ is recursively enumerable cannot be dropped.

## Depends on

- [Action logic and infinitary action logic](action-logic-and-infinitary-action-logic.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Logics between action logic and infinitary action logic are undecidable](logics-between-act-and-act-omega-are-undecidable.md)
- [Myhill's characterization of creative sets](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/myhill-s-characterization-of-creative-sets.md)

## Expansion

The proof strengthens the recursive inseparability used for undecidability to effective inseparability: the set $\mathcal{C}$ of machine-input pairs that trivially cycle and the set $\mathcal{H}$ of pairs that halt are effectively inseparable (Proposition 3 of the source, by diagonalization). With $S(M, x)$ the sequent from the undecidability proof, the set $A = \{(M, x) : S(M, x) \in \mathcal{L}\}$ contains $\mathcal{C}$ and is disjoint from $\mathcal{H}$, so $A$ and $\mathcal{H}$ are effectively inseparable; if $\mathcal{L}$ is recursively enumerable then so is $A$, and two recursively enumerable effectively inseparable sets are creative, hence $\Sigma^0_1$-complete by Myhill's theorem. As $A$ many-one reduces to $\mathcal{L}$ via $(M, x) \mapsto S(M, x)$, the set $\mathcal{L}$ is $\Sigma^0_1$-complete. A good expansion links pages for the effective inseparability of $\mathcal{C}$ and $\mathcal{H}$ (Proposition 3 of the source) and for the creativity of recursively enumerable effectively inseparable sets.

## Sources

- S. Kuznetsov, "Action logic is undecidable", *ACM Transactions on Computational Logic* 22(2):1–26, 2021, doi:10.1145/3445810; read as arXiv:1912.11273v1, <https://arxiv.org/abs/1912.11273v1>: Theorem 4 of arXiv:1912.11273v1 and Section 3.
