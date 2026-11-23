# Typing the polymorphic identity

In the empty context, the polymorphic identity
$\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ has type
$\Pi (A : \mathrm{Prop}).\, \Pi (x : A).\, A$.

This is typable only because $\mathrm{Prop}$ is impredicative: a product over
$A : \mathrm{Prop}$ whose codomain is a proposition is again a proposition.

## Sources

- T. Coquand, G. Huet, *The calculus of constructions*, Information and Computation 76(2–3), 1988, 95–120.
- Z. Luo, *An Extended Calculus of Constructions*, PhD thesis, University of Edinburgh, 1990.
- B. Barras, *Sets in Coq, Coq in Sets*, Journal of Formalized Reasoning 3(1), 2010, 29–48.
- Problem `coc_strong_normalization` of the lean-eval benchmark.
