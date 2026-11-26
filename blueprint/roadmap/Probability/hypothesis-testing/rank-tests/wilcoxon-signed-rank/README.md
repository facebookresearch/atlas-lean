# Wilcoxon signed-rank test

Wilcoxon's (1945) signed-rank test compares a symmetric location with $0$ through the ranks of absolute values. For independent observations $Z_1, \dots, Z_n$, rank $|Z_1|, \dots, |Z_n|$ and let $T^+$ be the sum of the ranks of the positive $Z_i$. Under the null hypothesis that each $Z_i$ has a continuous law symmetric about $0$, the law of $T^+$ does not depend on these laws.

## Expansion

1. The model: independent symmetric continuous observations, the ranks of the absolute values, and the statistic $T^+$.
2. Independence of the signs from the absolute values, and of the signs from each other, for symmetric continuous laws.
3. The exact null law: $T^+$ has the law of $\sum_{i=1}^n i\, B_i$ with $B_1, \dots, B_n$ independent Bernoulli$(1/2)$, so $P(T^+ = w) = c_n(w)/2^n$ with $c_n(w)$ the number of subsets of $\{1, \dots, n\}$ with sum $w$, and the probability generating function is $\prod_{i=1}^n (1 + x^i)/2$.
4. The symmetry of the null law about $n(n+1)/4$ and the null moments $E[T^+] = n(n+1)/4$ and $\operatorname{Var}(T^+) = n(n+1)(2n+1)/24$.
5. The normal approximation and its Edgeworth refinement as $n \to \infty$, and the treatment of zeros and ties.

## Sources

- F. Wilcoxon, Individual comparisons by ranking methods, Biometrics Bull. 1 (1945), 80–83. <https://doi.org/10.2307/3001968>
- Wilcoxon signed-rank test, Wikipedia, section on the null distribution. <https://en.wikipedia.org/wiki/Wilcoxon_signed-rank_test>
