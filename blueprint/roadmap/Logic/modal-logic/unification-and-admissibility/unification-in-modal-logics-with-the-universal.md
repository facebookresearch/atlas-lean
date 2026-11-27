# Unification in modal logics with the universal modality is undecidable

For every normal modal logic $L$ with $\mathbf{K}_u \subseteq L \subseteq \mathbf{K4}_u$, there is no algorithm that decides, given a formula $\varphi$ of the language with $\Box$ and the universal modality $\forall$, whether some substitution $\sigma$ satisfies $\sigma(\varphi) \in L$.

**Theorem (Wolter and Zakharyaschev).** Let $L$ be a [normal modal logic with the universal modality](normal-modal-logics-with-the-universal-modality.md) such that $\mathbf{K}_u \subseteq L \subseteq \mathbf{K4}_u$. Then the [unification problem](unification-problem-for-a-modal-logic.md) for $L$ is undecidable. The input is a single formula of the language $\mathcal{L}$ with one relational box $\Box$ and the universal box $\forall$; substitutions replace propositional variables by $\mathcal{L}$-formulas.

The source remarks that the same proof works for the multimodal versions of $\mathbf{K}_u$ and $\mathbf{K4}_u$ (the extra boxes interpreted by the empty relation) and adapts to some logics above $\mathbf{K4}_u$ such as $\mathbf{GL}_u$, and to propositional dynamic logic with converse, where the universal modality is definable; these are remarks, not part of the theorem. By contrast, $\mathbf{K}_u$ and $\mathbf{K4}_u$ themselves are decidable (satisfiability is EXPTIME-complete and PSPACE-complete respectively).

## Depends on

- [Normal modal logics with the universal modality](normal-modal-logics-with-the-universal-modality.md)
- [Unification problem for a modal logic](unification-problem-for-a-modal-logic.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces a configuration reachability problem for deterministic Minsky (two-register) machines: there is a fixed program $P$ and a fixed configuration $\mathfrak{a}$ such that no algorithm decides, given a configuration $\mathfrak{b}$, whether $P$ reaches $\mathfrak{b}$ from $\mathfrak{a}$ (recalled from Chagrov and Zakharyaschev). Chagrov's transitive frame $\mathfrak{F}$ has points $e(t, k, l)$ for the configurations $\langle t, k, l \rangle$ reachable from $\mathfrak{a}$, each seeing points that code $t$, $k$ and $l$; variable-free formulas pick out each point of $\mathfrak{F}$. Each instruction of $P$ becomes a formula $AxI$ using the existential modality $\exists$, their conjunction $AxP$ is valid in $\mathfrak{F}$, and for $\mathfrak{b} = \langle t, k, l \rangle$ one sets

$$
\psi(\mathfrak{b}) = \big(AxP \wedge \exists\varepsilon(\mathfrak{a})\big) \to \exists\varepsilon(\mathfrak{b}),
$$

where $\varepsilon(\cdot)$ describes the point coding a configuration. The key lemma (Lemma 2.3) says that, for every $L$ in the interval, $P$ reaches $\mathfrak{b}$ from $\mathfrak{a}$ iff $\psi(\mathfrak{b})$ is unifiable in $L$. If $\mathfrak{b}$ is unreachable, every substitution instance of $\psi(\mathfrak{b})$ is refuted in $\mathfrak{F}$ (its consequent is variable-free and false there), so no substitution instance of $\psi(\mathfrak{b})$ belongs to a logic contained in $\mathbf{K4}_u$. If $\mathfrak{b}$ is reachable, an explicit substitution for the two variables, built from formulas saying where the simulation of the computation first breaks down, puts $\sigma(\psi(\mathfrak{b}))$ into $\mathbf{K}_u$.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: Theorem 2.3 of arXiv:cs/0609052v1 and its proof in Section 2.
