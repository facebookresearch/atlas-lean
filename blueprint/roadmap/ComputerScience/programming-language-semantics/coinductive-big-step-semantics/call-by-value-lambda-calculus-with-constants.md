# The call-by-value λ-calculus with constants

Terms are $a, b, v ::= x \mid c \mid \lambda x.\, a \mid a\, b$, with constants $c ::= 0 \mid 1 \mid \dots$; $a[x \leftarrow b]$ is capture-avoiding substitution, and the *values* are the
constants and the abstractions. Write $\delta = \lambda x.\, x\, x$ and $\omega = \delta\, \delta$.

- **Big-step evaluation** $a \Rightarrow v$ is defined inductively by $c \Rightarrow c$, $\lambda x.\, a \Rightarrow \lambda x.\, a$, and $a_1\, a_2 \Rightarrow v$ whenever $a_1 \Rightarrow \lambda x.\, b$,
  $a_2 \Rightarrow v_2$ and $b[x \leftarrow v_2] \Rightarrow v$ (left-to-right order).
- **Small-step reduction** $a \to b$ is defined inductively by $(\lambda x.\, a)\, v \to a[x \leftarrow v]$ for a value $v$, $a_1\, b \to a_2\, b$ if $a_1 \to a_2$, and $a\, b_1 \to a\, b_2$
  if $a$ is a value and $b_1 \to b_2$.
- **Reduction sequences.** Consider the two rules "$R(a, a)$" and "$a \to a'$ and $R(a', b)$ imply $R(a, b)$". Finite reduction $a \to^* b$ is their least fixed point
  (the rules read inductively) and *finite or infinite reduction* $a \overset{co*}{\to} b$ their greatest fixed point (the rules read coinductively). *Infinite reduction*
  $a \to^\infty$ is the greatest fixed point of the single rule "$a \to a'$ and $a' \to^\infty$ imply $a \to^\infty$". The choice of rules matters for the greatest fixed point:
  the least fixed points of these rules and of the presentation with reflexivity, single steps and a separate transitivity rule coincide, but read coinductively the
  transitivity rule justifies every pair by itself, so that greatest fixed point is the total relation.

A term that neither evaluates nor diverges *goes wrong*; for example $0\, 0$.

## Depends on

- [Named, de Bruijn and locally nameless lambda terms](../../type-systems-and-lambda-calculi/syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Section 3 (syntax, values and the rules for $\Rightarrow$), Section 4 (the rules for $\to$, and the two rules for $\to^*$ and $\overset{co*}{\to}$ and the rule for $\to^\infty$, after Lemma 7) and Section 2 (inductive and coinductive interpretations of inference rules, Theorem 1).
- X. Leroy and H. Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009, <https://doi.org/10.1016/j.ic.2007.12.004>: the published version, with the same numbering: Section 3 (syntax, values and the rules for $\Rightarrow$), Section 4 (the rules for $\to$, and the two rules for $\to^*$ and $\overset{co*}{\to}$ and the rule for $\to^\infty$, after Lemma 7) and Section 2 (inductive and coinductive interpretations of inference rules, Theorem 1).
