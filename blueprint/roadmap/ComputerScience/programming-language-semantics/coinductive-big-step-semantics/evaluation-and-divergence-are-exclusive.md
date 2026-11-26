# Evaluation and divergence are deterministic and exclusive

In the [call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md):

1. if $a \Rightarrow v$ then $v$ is a value;
2. evaluation is deterministic: $a \Rightarrow v$ and $a \Rightarrow v'$ imply $v = v'$;
3. reduction is deterministic: $a \to a'$ and $a \to a''$ imply $a' = a''$;
4. $a \Rightarrow v$ and [$a \Rightarrow^\infty$](coinductive-divergence.md) never both hold.

## Depends on

- [Coinductive divergence](coinductive-divergence.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Lemma 2, Lemma 3, Lemma 6 and Lemma 7.
- X. Leroy and H. Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009, <https://doi.org/10.1016/j.ic.2007.12.004>: the published version, with the same numbering: Lemma 2, Lemma 3, Lemma 6 and Lemma 7.
