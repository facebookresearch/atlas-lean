# Concentration of conditional information in independent samples

Let $I$ be a finite index set and for each $i$ let $P_i$ be a joint law of $(Y_i, X_i)$ on finite sets with every positive mass at least $2^{-B}$, $B \ge 0$. Draw the pairs independently and let $s_i = -\log_2\Pr[X_i = x_i \mid Y_i = y_i]$ be the conditional surprisal. Then for every $\varepsilon \ge 0$,

$$
\Pr\Big[\sum_{i} s_i \le \sum_i H(X_i \mid Y_i) - \varepsilon\Big] \le \exp\Big(-\frac{2\varepsilon^2}{|I|\,B^2}\Big).
$$

Equivalently, except with that probability the conditional mass of the whole tuple given all observations is at most $2^{-(\sum_i H(X_i\mid Y_i) - \varepsilon)}$. Images of a uniform seed on a finite set $\Sigma$ satisfy the mass hypothesis with $B = \log_2|\Sigma|$.

## Proof sketch

Each $s_i$ lies in $[0, B]$ by the mass bound, has mean $H(X_i \mid Y_i)$, and the $s_i$ are independent; Hoeffding's inequality gives the tail. Surprisal adds over independent coordinates, so the sum equals the surprisal of the tuple.

## Depends on

- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006.
