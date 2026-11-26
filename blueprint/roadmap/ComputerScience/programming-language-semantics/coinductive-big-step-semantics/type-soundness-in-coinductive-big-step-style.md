# Type soundness in coinductive big-step style

Type the [call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md) with simple types $\tau ::= \mathrm{int} \mid \tau_1 \to \tau_2$ read coinductively, so
that recursive types such as $\sigma = \sigma \to \tau \to \tau'$ are allowed, by the rules $E \vdash x : E(x)$, $E \vdash c : \mathrm{int}$, abstraction and application. The system is
not normalizing: the call-by-value fixed-point operator $\lambda f.\, (\lambda x.\, f\, (x\, x))(\lambda x.\, f\, (\lambda y.\, (x\, x)\, y))$ has type
$((\tau \to \tau') \to \tau \to \tau') \to \tau \to \tau'$. For a closed term $a$ with $\emptyset \vdash a : \tau$:

1. (big-step preservation) if $a \Rightarrow v$ then $\emptyset \vdash v : \tau$;
2. (big-step soundness) $a \Rightarrow^\infty$, or $a \Rightarrow v$ for some $v$; equivalently, $a \to^\infty$ or $a \to^* v$ for a value $v$;
3. $a$ *reduces safely*, in the coinductive sense that every reduct of $a$ is a value or reduces further, a formulation provable without classical logic.

So well-typed closed terms never go wrong, stated directly in terms of big-step evaluation and divergence rather than with extra rules for erroneous
evaluations.

## Depends on

- [Coinductive divergence](coinductive-divergence.md)
- [Call-by-value λ-calculus with constants](call-by-value-lambda-calculus-with-constants.md)

## Proof depends on

- [Divergence is infinite reduction](divergence-is-infinite-reduction.md)

## Sources

- X. Leroy and H. Grall, "Coinductive big-step operational semantics", arXiv:0808.0586v1, 2008, <https://arxiv.org/abs/0808.0586v1>: Section 8, the typing rules and the fixed-point example, Lemmas 42–43, Theorems 45 and 47 (soundness with infinite reduction and safe reduction), Lemma 48 (big-step preservation), Theorem 49 and Lemma 50 (big-step progress).
- X. Leroy and H. Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009, <https://doi.org/10.1016/j.ic.2007.12.004>: the published version, with the same numbering: Section 8, the typing rules and the fixed-point example, Lemmas 42–43, Theorems 45 and 47 (soundness with infinite reduction and safe reduction), Lemma 48 (big-step preservation), Theorem 49 and Lemma 50 (big-step progress).
