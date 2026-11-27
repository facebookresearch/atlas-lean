# Divergence is infinite reduction

In the [call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md), [coinductive divergence](coinductive-divergence.md) coincides with infinite
reduction: $a \Rightarrow^\infty$ if and only if $a \to^\infty$. Moreover:

- every term either reduces infinitely or reduces in finitely many steps to a term that cannot reduce;
- $a \overset{co*}{\to} b$ holds exactly when $a \to^* b$ or $a \to^\infty$.

These proofs use the law of excluded middle.

## Depends on

- [Coinductive divergence](coinductive-divergence.md)

## Proof depends on

- [Big-step evaluation is finite reduction to a value](evaluation-is-finite-reduction-to-a-value.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Section 4, Lemma 8, Lemma 10 and Theorem 11, each marked there as using classical logic.
- X. Leroy and H. Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009, <https://doi.org/10.1016/j.ic.2007.12.004>: the published version, with the same numbering: Section 4, Lemma 8, Lemma 10 and Theorem 11, each marked there as using classical logic.
