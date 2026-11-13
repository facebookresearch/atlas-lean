# Subject reduction

Let $\Gamma$ be a context and $t$, $t'$, $A$ terms of the calculus
of constructions with universes. If $t$ has type $A$ in $\Gamma$, that is
$\Gamma \vdash t : A$, and $t$ reduces to $t'$ in one step of beta reduction (anywhere
inside $t$), then $\Gamma \vdash t' : A$.

## Sources

- Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Problem `coc_strong_normalization` of the lean-eval benchmark.
