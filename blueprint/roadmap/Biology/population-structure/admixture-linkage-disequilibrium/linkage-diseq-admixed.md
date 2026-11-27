# Decay of admixture linkage disequilibrium over generations

For all real numbers $\alpha, p_A, q_A, p_B, q_B, r$ and every natural number $n$,

$$D\bigl(R_r^n(x)\bigr) = (1 - r)^n\, \alpha (1 - \alpha)\, (p_A - p_B)(q_A - q_B),$$

where $x$ are the [pulse gamete frequencies](source-mix.md), $D(y) = y_{11} y_{00} - y_{10} y_{01}$, and $R_r^n$ is $n$ generations of the random-mating recursion with recombination fraction $r$, $R_r(y)_g = (1 - r)\, y_g + r\, p_{g_1}(y)\, q_{g_2}(y)$, where $p_a(y) = \sum_b y_{(a, b)}$ and $q_b(y) = \sum_a y_{(a, b)}$ are the allele frequencies at the two loci.

For $0 \le \alpha \le 1$, allele frequencies in $[0, 1]$ and $0 \le r \le 1$, this is the decay of admixture linkage disequilibrium over $n$ generations of random mating after the pulse.
