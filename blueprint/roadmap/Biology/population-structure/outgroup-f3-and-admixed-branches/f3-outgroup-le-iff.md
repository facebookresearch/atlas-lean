# Outgroup f3 ranks populations by shared drift

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) with [binary loadings](../patterson-s-f-statistics/has-binary-loadings.md) and drift lengths $\ell$, and let $O, A, B, B'$ be populations whose [lineages](../patterson-s-f-statistics/lineage.md) satisfy $L_O \cap L_A = L_O \cap L_B = L_O \cap L_{B'} = \varnothing$. Then

$$f_3(O; A, B) \le f_3(O; A, B') \iff \sum_{e \in L_A \cap L_B} \ell_e \le \sum_{e \in L_A \cap L_{B'}} \ell_e,$$

where $f_3$ is the [f3 statistic](../patterson-s-f-statistics/f3.md) of the population frequencies.
