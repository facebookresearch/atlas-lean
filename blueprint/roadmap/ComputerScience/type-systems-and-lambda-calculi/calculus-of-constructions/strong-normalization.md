# Strong normalization of CCω

Every well-typed term is strongly normalizing: if
$\Gamma \vdash t : A$ for some context $\Gamma$ and some term $A$, then $t$ is strongly
normalizing.

## Sources

- T. Coquand, G. Huet, *The calculus of constructions*, Information and Computation 76(2–3), 1988, 95–120.
- Z. Luo, *An Extended Calculus of Constructions*, PhD thesis, University of Edinburgh, 1990.
- B. Barras, *Sets in Coq, Coq in Sets*, Journal of Formalized Reasoning 3(1), 2010, 29–48.
- Problem `coc_strong_normalization` of the lean-eval benchmark.
