# There is no interpretability-minimal essentially hereditarily undecidable theory

Among recursively enumerable theories that are essentially hereditarily undecidable, no theory is minimal with respect to interpretability; moreover, every essentially undecidable theory is avoided by some essentially hereditarily undecidable theory that does not interpret it.

**Theorem (Visser).** Theories are consistent, recursively enumerable (RE) theories of classical predicate logic in a finite signature. For a property $\mathcal P$ of theories, $U$ is *essentially $\mathcal P$* if all consistent RE extensions of $U$ in the same language are $\mathcal P$, and *hereditarily $\mathcal P$* if all consistent RE subtheories of $U$ in the same language are $\mathcal P$; thus $U$ is *essentially hereditarily undecidable* if every consistent RE extension of $U$ is hereditarily undecidable, equivalently if every theory $W$ in the language of $U$ such that $U + W$ is consistent is undecidable (Theorem 3.1). Write $U \lhd V$ if $U$ is interpretable in $V$. Then:

1. there is no interpretability minimal essentially hereditarily undecidable RE theory (Theorem 7.1 of the source);
2. for every essentially undecidable RE theory $U$ one can effectively find an essentially hereditarily undecidable RE theory $V$, which can moreover be taken effectively inseparable, such that $V$ does not interpret $U$ (Theorem 7.2).

Examples of essentially hereditarily undecidable theories are Robinson's theory $\mathsf R$ (Cobham), finitely axiomatized theories of every nonzero RE Turing degree (Hanf), and some theories strictly below $\mathsf R$ in interpretability (Corollary 3.1 of the source). If a theory tolerates an essentially hereditarily undecidable theory, that is, has a consistent extension in the same language that interprets it, then it is hereditarily undecidable (Theorem 3.5), which makes the notion a tool for undecidability proofs.

## Depends on

- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Consistent set of formulas](../../../first-order-logic/g-del-s-completeness-theorem/consistent.md)

## Proof depends on

None.

## Expansion

Related results: [theories interpreting an essentially undecidable theory are undecidable](theories-interpreting-an-essentially.md), and [Robinson's theory R is essentially undecidable](robinson-s-theory-r-is-essentially-undecidable.md), which Cobham strengthened to essential hereditary undecidability.

*Part 1.* Essentially hereditarily undecidable theories are closed under the disjoint sum $U_0 \ovee U_1$, a theory that chooses by a $0$-ary predicate between $U_0$ and $U_1$ and is interpretable in both (Theorem 3.3); so a minimal such theory would be a minimum, and it suffices to exclude a minimum $U^\star$. By Shoenfield, from an index $i$ of an RE set $W_i$ one effectively finds a theory $\mathsf{sh}(i)$ that is essentially undecidable iff $W_i$ is not recursive, and by Peretyat'kin a finitely axiomatized theory $\mathsf{shpe}(i)$ recursively Boolean isomorphic to it; a finitely axiomatized essentially undecidable theory is essentially hereditarily undecidable. If $U^\star$ were a minimum, then $W_i$ would be non-recursive iff $\mathsf{shpe}(i)$ interprets $U^\star$, a $\Sigma^0_3$ condition, whereas the set of indices of non-recursive RE sets is $\Pi^0_3$-complete (Rogers; Mostowski), a contradiction.

*Part 2.* The construction starts from Janiczak's theory $\mathsf{Jan}$ of an equivalence relation, over which every sentence is equivalent to a Boolean combination of the sentences $A_n$ ("some class has exactly $n + 1$ elements"), extended by the axioms $A_n$ for $n$ in a fixed RE set; it passes to a finitely axiomatized theory recursively Boolean isomorphic to it (Peretyat'kin) and then chooses Boolean combinations of the images of the $A_n$ against an effective enumeration of the candidate interpretations of $U$.

## Sources

- A. Visser, "Essential hereditary undecidability", *Archive for Mathematical Logic* 63(5–6):529–562, 2024, <https://doi.org/10.1007/s00153-024-00911-y>; read as arXiv:2212.03565v2, <https://arxiv.org/abs/2212.03565v2>: Section 2 (essential and hereditary properties, Janiczak's theory, Theorem 2.12), Section 3 (Theorems 3.1, 3.3, 3.5, 3.10, 3.11, Corollary 3.1) and Section 7 (Theorems 7.1 and 7.2 with proofs).
