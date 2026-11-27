# Compiling generic-group programs to oracle computations

Let $L$ be a type of labels with decidable equality and $\mathit{env} : \{0, \dots, n-1\} \to L$ an environment. Compilation translates a generic-group program over $n$ indices into an oracle computation with queries in $\mathrm{Query}(L)$ and answers in $L$, returning a label:

- $\mathrm{ret}\ i$ returns $\mathit{env}(i)$;
- $\mathrm{mul}\ i\ j\ k$ queries the product of $\mathit{env}(i)$ and $\mathit{env}(j)$, and $\mathrm{inv}\ i\ k$ queries the inverse of $\mathit{env}(i)$; on answer $a$ each compiles the continuation $k$ in the [environment extended by $a$](snoc-env.md);
- $\mathrm{eqTest}\ i\ j\ k_t\ k_f$ compiles $k_t$ if $\mathit{env}(i) = \mathit{env}(j)$ and $k_f$ otherwise, without a query.

The environment is arbitrary and supplied by the evaluator. The syntax itself cannot manufacture a literal label: every label in the compiled computation is an initial input from $\mathit{env}$ or a previous oracle answer.
