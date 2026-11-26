# Coevaluation

For the [call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md), *coevaluation* $a \overset{co}{\Rightarrow} b$ is the coinductive interpretation of
the evaluation rules: $c \overset{co}{\Rightarrow} c$, $\lambda x.\, a \overset{co}{\Rightarrow} \lambda x.\, a$, and $a_1\, a_2 \overset{co}{\Rightarrow} v$ whenever $a_1 \overset{co}{\Rightarrow} \lambda x.\, b$,
$a_2 \overset{co}{\Rightarrow} v_2$ and $b[x \leftarrow v_2] \overset{co}{\Rightarrow} v$. It describes terminating and diverging evaluations with one set of rules, but it is not
deterministic: $\omega \overset{co}{\Rightarrow} v$ holds for every term $v$, by coinduction.

## Depends on

- [The call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Section 7.1, the rules for $\overset{co}{\Rightarrow}$ and Lemma 33.
