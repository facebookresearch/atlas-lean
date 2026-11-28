# Concentration of conditional information in independent samples

Let $P_{XY}$ be a joint law on finite sets $\mathcal{X} \times \mathcal{Y}$, and let $(X_1, Y_1), \dots, (X_k, Y_k)$ be i.i.d. according to $P_{XY}$. Write $H(X \mid Y)$ for the conditional Shannon entropy, $H_\infty(X) = -\log_2 \max_x P_X(x)$ for the min-entropy, $H_\infty(X \mid Y) = \min_y H_\infty(X \mid Y = y)$ for the conditional min-entropy, and $\delta$ for statistical distance. Then for every $\varepsilon \in (0, 1)$ there is a distribution $P_{\bar X \bar Y}$ on $\mathcal{X}^k \times \mathcal{Y}^k$ with

$$
\delta\big(P_{\bar X \bar Y},\ P_{X_1 \cdots X_k Y_1 \cdots Y_k}\big) \le 2\varepsilon
\qquad\text{and}\qquad
H_\infty(\bar X \mid \bar Y) \ge k\,H(X \mid Y) - 6\sqrt{k \log_2(1/\varepsilon)}\,\log_2|\mathcal{X}|.
$$

## Proof sketch

The conditional surprisal $-\log_2 P_{X^k \mid Y^k}(x \mid y)$ of the tuple is the sum of the per-coordinate surprisals, which are independent with mean $H(X \mid Y)$. A tail bound shows that, except with probability about $\varepsilon$, this sum is at least $kH(X \mid Y)$ minus the stated deviation; cutting off the outcomes in the exceptional event and renormalizing gives a nearby distribution whose conditional masses are all small. The source writes $\log$ for the logarithm used in bit lengths, that is, base $2$.

The following Hoeffding form is derived here and is not stated in the cited source. If the pairs $(X_i, Y_i)$, $i \in I$, are independent but not necessarily identically distributed, and every positive mass of each joint law is at least $2^{-B}$ with $B \ge 0$, then each surprisal $s_i = -\log_2 \Pr[X_i = x_i \mid Y_i = y_i]$ lies in $[0, B]$ and has mean $H(X_i \mid Y_i)$, so Hoeffding's inequality gives, for every $\varepsilon \ge 0$,

$$
\Pr\Big[\sum_{i} s_i \le \sum_i H(X_i \mid Y_i) - \varepsilon\Big] \le \exp\Big(-\frac{2\varepsilon^2}{|I|\,B^2}\Big).
$$

Images of a uniform seed on a finite set $\Sigma$ satisfy the mass hypothesis with $B = \log_2|\Sigma|$.

## Depends on

- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006, Section 3.1 (definitions of statistical distance and conditional min-entropy) and Section 3.3, Proposition 1.
