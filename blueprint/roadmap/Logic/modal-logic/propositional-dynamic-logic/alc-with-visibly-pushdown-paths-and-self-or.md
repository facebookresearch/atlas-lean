# ALC with visibly pushdown paths and Self or nominals is undecidable

Concept satisfiability, decidable for ALC with visibly pushdown path expressions, becomes undecidable when the Self operator is added, and also when nominals are added, already with the single non-regular language {rⁿsⁿ}.

**Theorem (Bednarczyk).** For the logics of the page on [ALC with visibly pushdown path expressions](alc-with-visibly-pushdown-path-expressions.md):

1. the concept satisfiability problem for $\mathcal{ALC}^{\mathsf{Self}}_{vpl}$ is undecidable, even if only visibly pushdown languages that are encodings of languages of deterministic one-counter automata are allowed in concepts (Theorem 3.5 of the source);
2. the concept satisfiability problem for $\mathcal{ALCO}_{vpl}$ is undecidable, even if the languages allowed in concepts are restricted to $r, s, r^+, s^+, r^*, s^*, (r + s)^*, (r + s)^+$ and $r^\# s^\#$ (Theorem 4.15).

Without Self and nominals, concept satisfiability for $\mathcal{ALC}_{vpl}$ is 2EXPTIME-complete. The source also recalls that $\mathcal{ALC}_{vpl}$ with inverse roles, and with role hierarchies, is undecidable (its Corollaries 2.3 and 2.4), and shows that entailment of queries with atoms using $r^\# s^\#$ over ALC TBoxes is undecidable.

## Depends on

- [ALC with visibly pushdown path expressions](alc-with-visibly-pushdown-path-expressions.md)

## Proof depends on

None.

## Expansion

*Part 1.* For deterministic one-counter automata $\mathcal A_1, \mathcal A_2$ the proof builds concepts $C_{\mathcal A_1}, C_{\mathcal A_2}$ such that $C_{\mathcal A_1} \sqcap C_{\mathcal A_2} \sqcap \exists x^*.(\mathit{Acc}_{\mathcal A_1} \sqcap \mathit{Acc}_{\mathcal A_2})$ is satisfiable iff $L(\mathcal A_1) \cap L(\mathcal A_2) \neq \emptyset$ (Lemma 3.4); non-emptiness of the intersection of two deterministic one-counter languages is undecidable (Valiant).

*Part 2.* The proof reduces the solvability of domino tiling systems: for a domino system $\mathcal D$ a concept $C_{\mathcal D}$ is built whose models contain a structure from which a solution of $\mathcal D$ is read off, and conversely (Lemmas 4.4, 4.11 and 4.13).

A good expansion links the undecidability of non-emptiness of the intersection of deterministic one-counter languages and of the domino tiling problem used, which have no pages yet.

## Sources

- B. Bednarczyk, "Exploring non-regular extensions of propositional dynamic logic with description-logics features", *Logical Methods in Computer Science* 20(2), paper 7, 2024, <https://doi.org/10.46298/lmcs-20(2:7)2024>; read as arXiv:2307.09913v5, <https://arxiv.org/abs/2307.09913v5>: Section 2 (Corollaries 2.3 and 2.4), Section 3 (Lemma 3.4, Theorem 3.5) and Section 4 (Lemmas 4.4, 4.11 and 4.13, Theorem 4.15).
