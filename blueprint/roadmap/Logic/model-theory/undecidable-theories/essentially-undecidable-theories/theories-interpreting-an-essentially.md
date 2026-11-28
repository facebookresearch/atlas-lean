# Theories interpreting an essentially undecidable theory are undecidable

A theory is essentially undecidable exactly when every consistent theory that interprets it is undecidable; consequently essential undecidability passes to every theory interpreting an essentially undecidable one, and to disjunctions of two essentially undecidable theories.

**Setting.** Theories are first-order theories with recursively enumerable axiom sets. A first-order theory $U$ is *essentially undecidable* if every consistent extension of $U$ in the same language is undecidable. $V \rhd U$ means that $V$ interprets $U$: there is a translation of the language of $U$ into that of $V$ under which every theorem of $U$ becomes a theorem of $V$. The source uses the most inclusive notion of interpretation (piecewise, multidimensional, relativized, not necessarily identity-preserving, with parameters) and notes that the results hold for every choice of the notion. For theories $U$ and $V$, $U \ovee V$ is the theory in the disjoint union of their languages plus a fresh $0$-ary predicate $P$, axiomatized by $P \to \varphi$ for the axioms $\varphi$ of $U$ and $\neg P \to \psi$ for the axioms $\psi$ of $V$.

**Theorem.**

1. $U$ is essentially undecidable iff every consistent theory $V$ with $V \rhd U$ is undecidable (Theorem 2.1).
2. If $U$ is essentially undecidable and $V \rhd U$, then $V$ is essentially undecidable (Theorem 2.2(i)).
3. If $U$ and $V$ are essentially undecidable, then so is $U \ovee V$ (Theorem 2.2(ii)).

In particular every consistent theory that interprets [Robinson arithmetic Q](robinson-arithmetic-q-is-essentially-undecidable.md) or [Robinson's theory R](robinson-s-theory-r-is-essentially-undecidable.md) is undecidable.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Consistent set of formulas](../../../first-order-logic/g-del-s-completeness-theorem/consistent.md)

## Proof depends on

None.

## Expansion

For clause 1, if $V$ is consistent and decidable and $\iota$ is an interpretation of $U$ in $V$, the sentences of the language of $U$ whose $\iota$-translations $V$ proves form a consistent decidable extension of $U$; the converse holds because every extension of $U$ interprets $U$. Clause 2 follows by transitivity of interpretability. For clause 3, a consistent decidable extension $T$ of $U \ovee V$ is consistent with $P$ or with $\neg P$, and then $T + P$ interprets $U$ or $T + \neg P$ interprets $V$, contradicting clause 1. The method of proving undecidability by interpretation goes back to Tarski, Mostowski and Robinson.

## Sources

- J. Murwanashyaka, F. Pakhomov and A. Visser, "There are no minimal essentially undecidable theories", *Journal of Logic and Computation* 34(6):1159–1171, 2024, doi:10.1093/logcom/exad005; read as arXiv:2207.08174v2, <https://arxiv.org/abs/2207.08174v2>: Section 2 (the definitions of essential undecidability, interpretability and $\ovee$, Theorems 2.1 and 2.2 with their proofs).
