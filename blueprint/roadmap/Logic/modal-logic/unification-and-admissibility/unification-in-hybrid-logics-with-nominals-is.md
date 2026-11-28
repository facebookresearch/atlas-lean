# Unification in hybrid logics with nominals is undecidable

For every logic $L$ with $\mathbf{K}_{\mathcal{H}_2} \subseteq L \subseteq \mathbf{K}_{\mathcal{H}_2} \oplus 45$, in the language with two boxes and nominals, both the unification problem and the admissibility problem for inference rules are undecidable.

**Theorem (Wolter and Zakharyaschev).** Let $L$ be a logic in the language $\mathcal{H}_2$ of [hybrid logic with two boxes and nominals](hybrid-logics-with-two-boxes-and-nominals.md) such that $\mathbf{K}_{\mathcal{H}_2} \subseteq L \subseteq \mathbf{K}_{\mathcal{H}_2} \oplus 45$. Then the [unification problem](unification-problem-for-a-modal-logic.md) for $L$ is undecidable and, therefore, so is the [admissibility problem](admissibility-problem-for-inference-rules.md) for $L$. Substitutions replace propositional variables by $\mathcal{H}_2$-formulas and leave nominals unchanged; the source notes that allowing nominals to be replaced by nominals does not affect the result.

The theorem needs two boxes: with the universal modality available instead of nominals, the corresponding result holds already for one relational box.

## Depends on

- [Hybrid logics with two boxes and nominals](hybrid-logics-with-two-boxes-and-nominals.md)
- [Unification problem for a modal logic](unification-problem-for-a-modal-logic.md)
- [Admissibility problem for inference rules](admissibility-problem-for-inference-rules.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof follows the encoding of Minsky machine computations used for logics with the universal modality. Without $\forall$ the formula cannot refer to all points of a model, so one nominal $n$ is used as a surrogate: if $n$ is accessible from a point $x$ via $R$ and $S$, the formula forces it to be accessible from every point within a fixed distance of $x$, which gives a local substitute for the universal modality on the part of the model the encoding uses. Admissibility follows as before, since $\varphi$ is not unifiable iff $\varphi / \bot$ is admissible.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: Theorem 4.2 of arXiv:cs/0609052v1 and its proof in Section 4.
