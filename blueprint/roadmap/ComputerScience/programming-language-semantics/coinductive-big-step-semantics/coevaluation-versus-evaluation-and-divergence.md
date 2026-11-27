# Coevaluation versus evaluation and divergence

In the [call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md), [coevaluation](coevaluation.md) relates to evaluation, divergence and
reduction as follows.

1. If $a \Rightarrow v$ then $a \overset{co}{\Rightarrow} v$.
2. If $a \overset{co}{\Rightarrow} v$ then $a \Rightarrow v$ or $a \Rightarrow^\infty$ (classically).
3. The converse of 2 fails: $\omega\, (0\, 0)$ diverges but coevaluates to nothing, since $0\, 0$ coevaluates to nothing.
4. Coevaluation is deterministic on terminating terms: $a \Rightarrow v$ and $a \overset{co}{\Rightarrow} v'$ imply $v' = v$; and the diverging term $(\lambda x.\, 0)\, \omega$ coevaluates to $0$ only.
5. If $a \overset{co}{\Rightarrow} v$ then $a \overset{co*}{\to} v$, provably without classical logic; the converse fails for terms that diverge but do not coevaluate.

## Depends on

- [Coevaluation](coevaluation.md)
- [Coinductive divergence](coinductive-divergence.md)

## Proof depends on

- [Divergence is infinite reduction](divergence-is-infinite-reduction.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Section 7, Lemmas 32, 34, 35 and 36, with the examples $\omega\,(0\,0)$ and $(\lambda x.\, 0)\, \omega$ in the text between them.
- X. Leroy and H. Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009, <https://doi.org/10.1016/j.ic.2007.12.004>: the published version, with the same numbering: Section 7, Lemmas 32, 34, 35 and 36, with the examples $\omega\,(0\,0)$ and $(\lambda x.\, 0)\, \omega$ in the text between them.
