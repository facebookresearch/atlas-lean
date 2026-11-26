# Null distribution of the Wilcoxon signed-rank statistic

Let $Z_1, \dots, Z_n$, $n \ge 1$, be independent, each with a continuous law symmetric about $0$, and let $T^+$ be the [signed-rank statistic](README.md), the sum of the ranks of $|Z_1|, \dots, |Z_n|$ belonging to positive $Z_i$ (ties have probability $0$). Then $T^+$ has the law of $\sum_{i=1}^n i\, B_i$ with $B_1, \dots, B_n$ i.i.d. Bernoulli$(1/2)$: $P(T^+ = w) = c_n(w)/2^n$, where $c_n(w)$ is the number of subsets of $\{1, \dots, n\}$ with sum $w$, and the probability generating function is $\prod_{i=1}^n (1 + x^i)/2$. Hence the law is symmetric about $n(n+1)/4$ and

$$E[T^+] = \frac{n(n+1)}{4}, \qquad \operatorname{Var}(T^+) = \frac{n(n+1)(2n+1)}{24}.$$

## Expansion

1. The model: independent symmetric continuous observations, the ranks of the absolute values, and the statistic $T^+$.
2. Independence of the signs from the absolute values, and of the signs from each other, for symmetric continuous laws.
3. The exact null law: $T^+$ has the law of $\sum_{i=1}^n i\, B_i$ with $B_1, \dots, B_n$ independent Bernoulli$(1/2)$, so $P(T^+ = w) = c_n(w)/2^n$ with $c_n(w)$ the number of subsets of $\{1, \dots, n\}$ with sum $w$, and the probability generating function is $\prod_{i=1}^n (1 + x^i)/2$.
4. The symmetry of the null law about $n(n+1)/4$ and the null moments $E[T^+] = n(n+1)/4$ and $\operatorname{Var}(T^+) = n(n+1)(2n+1)/24$.
5. The normal approximation and its Edgeworth refinement as $n \to \infty$, and the treatment of zeros and ties.

## Sources

- F. Wilcoxon, Individual comparisons by ranking methods, Biometrics Bull. 1 (1945), 80–83. <https://doi.org/10.2307/3001968>
- Wilcoxon signed-rank test, Wikipedia, section on the null distribution. <https://en.wikipedia.org/wiki/Wilcoxon_signed-rank_test>
