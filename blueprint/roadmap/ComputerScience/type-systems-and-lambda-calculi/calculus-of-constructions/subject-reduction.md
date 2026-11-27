# Subject reduction

Let $\Gamma$ be a context and $t$, $t'$, $A$ terms of the calculus
of constructions with universes. If $t$ has type $A$ in $\Gamma$, that is
$\Gamma \vdash t : A$, and $t$ reduces to $t'$ in one step of beta reduction (anywhere
inside $t$), then $\Gamma \vdash t' : A$.

## Sources

- T. Coquand, G. Huet, *The calculus of constructions*, Information and Computation 76(2–3), 1988, 95–120.
- Z. Luo, *An Extended Calculus of Constructions*, PhD thesis, University of Edinburgh, 1990.
- B. Barras, *Sets in Coq, Coq in Sets*, Journal of Formalized Reasoning 3(1), 2010, 29–48.
- Problem `coc_strong_normalization` of the lean-eval benchmark.
