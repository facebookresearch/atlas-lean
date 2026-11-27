# Beta step of the applied polymorphic identity

The polymorphic identity
$\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ applied to
$\bot = \Pi (P : \mathrm{Prop}).\, P$ reduces in one beta step to $\lambda (x : \bot).\, x$.

This is an anti-vacuity guard: it pins down beta reduction and substitution.

## Sources

- T. Coquand, G. Huet, *The calculus of constructions*, Information and Computation 76(2–3), 1988, 95–120.
- Z. Luo, *An Extended Calculus of Constructions*, PhD thesis, University of Edinburgh, 1990.
- B. Barras, *Sets in Coq, Coq in Sets*, Journal of Formalized Reasoning 3(1), 2010, 29–48.
- Problem `coc_strong_normalization` of the lean-eval benchmark.
