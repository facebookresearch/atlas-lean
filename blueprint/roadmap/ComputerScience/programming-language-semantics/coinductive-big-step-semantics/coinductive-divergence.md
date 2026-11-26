# Coinductive divergence

For the [call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md), *divergence* $a \Rightarrow^\infty$ is the coinductive interpretation, the
greatest fixed point of the associated inference operator, of the rules

- $a_1\, a_2 \Rightarrow^\infty$ if $a_1 \Rightarrow^\infty$;
- $a_1\, a_2 \Rightarrow^\infty$ if $a_1 \Rightarrow v$ and $a_2 \Rightarrow^\infty$;
- $a_1\, a_2 \Rightarrow^\infty$ if $a_1 \Rightarrow \lambda x.\, b$, $a_2 \Rightarrow v$ and $b[x \leftarrow v] \Rightarrow^\infty$.

Derivations of $a \Rightarrow^\infty$ may be infinite. For example $\omega = (\lambda x.\, x\, x)(\lambda x.\, x\, x) \Rightarrow^\infty$: the set $\{\omega\}$ is consistent for the operator, by the third
rule with $\omega$ itself as the third premise; on the other hand $\omega \Rightarrow v$ holds for no $v$.

## Depends on

- [The call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Section 3, the rules for $\Rightarrow^\infty$, Lemma 4 ($\omega$ does not evaluate) and Lemma 5 ($\omega$ diverges, with its proof as a greatest fixed point, as a guarded system of equations and as a corecursive proof term).
- X. Leroy and H. Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009, <https://doi.org/10.1016/j.ic.2007.12.004>: the published version, with the same numbering: Section 3, the rules for $\Rightarrow^\infty$, Lemma 4 ($\omega$ does not evaluate) and Lemma 5 ($\omega$ diverges, with its proof as a greatest fixed point, as a guarded system of equations and as a corecursive proof term).
