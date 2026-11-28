# Satisfiability of ∀∃ HyperLTL is undecidable

Whether a HyperLTL sentence with one universal trace quantifier followed by an existential one has a model, a nonempty set of traces, is undecidable, while satisfiability of the alternation-free and the $\exists^*\forall^*$ fragments is decidable.

**Setting (Finkbeiner and Hahn).** Formulas are those of [HyperLTL](../hyperltl.md): LTL formulas over atomic propositions indexed by trace variables, $a_\pi$, preceded by a prefix of trace quantifiers $\exists \pi$ and $\forall \pi$. A sentence $\psi$ is evaluated on a set $T \subseteq (2^{AP})^\omega$ of traces, the quantifiers ranging over $T$. *HyperLTL-SAT* asks, given a sentence $\psi$, whether some nonempty set of traces $T$ satisfies $T \models \psi$. The *$\forall\exists$ fragment* consists of the sentences whose quantifier prefix is $\forall\pi\,\exists\pi'$ (more generally $\forall^*\exists^*$).

**Theorem (Finkbeiner and Hahn).** $\forall\exists$ HyperLTL-SAT is undecidable (Theorem 5 of arXiv:1606.07047v1).

By contrast, HyperLTL-SAT is PSPACE-complete for the alternation-free fragment (Theorem 2 of the source) and EXPSPACE-complete for the $\exists^*\forall^*$ fragment (Theorem 3), so $\forall\exists$ is the smallest quantifier prefix with undecidable satisfiability: a block of existential quantifiers can be merged into one by taking product traces. For full HyperLTL, satisfiability was later shown to be $\Sigma^1_1$-complete ([HyperLTL satisfiability is Σ¹₁-complete](hyperltl-satisfiability-is-sigma-1-1-complete.md)).

## Depends on

- [HyperLTL](../hyperltl.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof is a many-one reduction from the Post correspondence problem. Given lists $\alpha_1, \dots, \alpha_n$ and $\beta_1, \dots, \beta_n$ over $\Sigma$, the atomic propositions are the pairs in $(\Sigma \cup \dot\Sigma \cup \{\#\})^2$, where a stone $(\alpha_i, \beta_i)$ is written as a sequence of pairs carrying the letters of $\alpha_i$ in the first and those of $\beta_i$ in the second component, padded with $\#$, and dotted letters mark where a stone begins. The sentence has the shape $\forall\pi\,\exists\pi_s\,\exists\pi'$: some trace $\pi_s$ spells a stone sequence whose two components agree letter by letter and ends in $(\#,\#)^\omega$; every trace $\pi$ is eventually $(\#,\#)^\omega$ and either is $(\#,\#)^\omega$ or starts with a valid stone $i$; and then there is a trace $\pi'$ equal to $\pi$ with that first stone deleted, the two components shifted by $|\alpha_i|$ and $|\beta_i|$. A model thus contains a trace for a solution and all its suffixes down to $(\#,\#)^\omega$, so the sentence is satisfiable exactly when the instance has a solution; the two existential quantifiers merge into one.

## Sources

- B. Finkbeiner and C. Hahn, "Deciding Hyperproperties", in *27th International Conference on Concurrency Theory (CONCUR 2016)*, Leibniz International Proceedings in Informatics 59, Schloss Dagstuhl, 2016, pp. 13:1–13:14, doi:[10.4230/LIPIcs.CONCUR.2016.13](https://doi.org/10.4230/LIPIcs.CONCUR.2016.13); read as arXiv:1606.07047v1 ([arXiv](https://arxiv.org/abs/1606.07047v1)), whose numbering is used (theorems numbered separately): the definition of HyperLTL-SAT in Section 2, Theorems 2 and 3, and Theorem 5 with its proof in Section 5.
