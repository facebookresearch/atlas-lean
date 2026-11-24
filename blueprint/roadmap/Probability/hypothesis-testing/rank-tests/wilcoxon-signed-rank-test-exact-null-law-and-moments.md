# Wilcoxon signed-rank statistic: exact null law and moments

Let $Z_1, \dots, Z_n$ be independent, each with a continuous law symmetric about $0$. Rank $|Z_1|, \dots, |Z_n|$ (ties have probability $0$) and let $T^+$ be the sum of the ranks of the positive $Z_i$, the statistic of Wilcoxon's (1945) signed-rank test. Under symmetry the signs are independent of each other and of the absolute values, so $T^+$ has the law of $\sum_{i=1}^n i\, B_i$ with $B_1, \dots, B_n$ independent Bernoulli$(1/2)$: $P(T^+ = w) = c_n(w)/2^n$, where $c_n(w)$ is the number of subsets of $\{1, \dots, n\}$ with sum $w$, and the probability generating function is $\prod_{i=1}^n (1 + x^i)/2$. Hence the law is symmetric about $n(n+1)/4$ and

$$E[T^+] = \frac{n(n+1)}{4}, \qquad \operatorname{Var}(T^+) = \frac{n(n+1)(2n+1)}{24},$$

which are the null mean and variance stated in Wilcoxon signed-rank test, Wikipedia (null distribution section), where the moment generating function of the signed-rank sum is given as $2^{-n}\prod_{j=1}^n (1 + e^{jt})$.

## Expansion

1. The model: independent symmetric continuous observations, the ranks of the absolute values, and the statistic.
2. Independence of the signs from the absolute values, and of the signs from each other, for symmetric continuous laws.
3. The representation $\sum_i i B_i$ and the generating function.
4. Mean, variance and symmetry of the law, from $\sum_i i/2$ and $\sum_i i^2/4$.
5. The normal approximation and its Edgeworth refinement as $n \to \infty$, and the treatment of zeros and ties, as separate statements.

## Sources

- F. Wilcoxon, Individual comparisons by ranking methods, Biometrics Bull. 1 (1945), 80–83. <https://doi.org/10.2307/3001968>
- Wilcoxon signed-rank test, Wikipedia, section on the null distribution. <https://en.wikipedia.org/wiki/Wilcoxon_signed-rank_test>
