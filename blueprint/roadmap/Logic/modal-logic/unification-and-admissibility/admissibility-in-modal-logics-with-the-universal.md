# Admissibility in modal logics with the universal modality is undecidable

For every normal modal logic $L$ with $\mathbf{K}_u \subseteq L \subseteq \mathbf{K4}_u$, there is no algorithm that decides whether a given inference rule $\varphi_1, \dots, \varphi_n / \varphi$ in the language with $\Box$ and the universal modality is admissible in $L$.

**Theorem (Wolter and Zakharyaschev).** Let $L$ be a [normal modal logic with the universal modality](normal-modal-logics-with-the-universal-modality.md) such that $\mathbf{K}_u \subseteq L \subseteq \mathbf{K4}_u$. Then the [admissibility problem for inference rules](admissibility-problem-for-inference-rules.md) of $L$ is undecidable: no algorithm decides, given formulas $\varphi_1, \dots, \varphi_n, \varphi$ of the language with $\Box$ and $\forall$, whether every substitution $\sigma$ with $\sigma(\varphi_1), \dots, \sigma(\varphi_n) \in L$ also has $\sigma(\varphi) \in L$.

## Depends on

- [Normal modal logics with the universal modality](normal-modal-logics-with-the-universal-modality.md)
- [Admissibility problem for inference rules](admissibility-problem-for-inference-rules.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Unification in modal logics with the universal modality is undecidable](unification-in-modal-logics-with-the-universal.md)

## Expansion

The source states this as an immediate consequence of the undecidability of unification: a formula $\varphi$ is not unifiable in $L$ iff the rule $\varphi / \bot$ is admissible in $L$, because $\bot \notin L$. A decision procedure for admissibility would therefore decide unification.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: Theorem 2.8 of arXiv:cs/0609052v1 and the observation in Section 1 that $\varphi / \bot$ is not admissible iff $\varphi$ is unifiable.
