# Quotient combiner of an independent p-value and e-value

For a null hypothesis $H$, a p-value is a random variable $P$ that is [valid](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md) under $H$, $\Pr(P \le t) \le t$ for all $t \in [0, 1]$, and an e-value is a random variable $E \ge 0$ with $\mathbb{E}[E] \le 1$ under $H$. Define the quotient combiner

$$Q(p, e) = \frac{p}{e} \wedge 1$$

(with $0/0 = 0$ and $p/0 = \infty$ for $p > 0$, so $Q(0, 0) = 0$; setting $Q(0, 0) = 1$ would make $Q$ inadmissible since replacing $Q(0, 0)$ by $0$ preserves validity because $\Pr(P = 0) = 0$ for every valid p-value $P$). **Theorem.** If $P$ and $E$ are independent under $H$, then $Q(P, E)$ is a valid p-value, and $Q$ is admissible among combiners of independent p- and e-values that return p-values.

## Depends on

- [Valid p-value](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)

## Expansion

Conditional on $E = e > 0$, $\Pr(P/e \le t \mid E = e) = \Pr(P \le te) \le \min(te, 1) \le te$ by independence; taking expectations, $\Pr(Q(P, E) \le t) \le t\, \mathbb{E}[E] \le t$. A consequence noted in the paper: with $U \sim U(0, 1)$ independent of $E$, $Q(U, E)$ is a valid p-value that is never larger and sometimes strictly smaller than the e-to-p calibration $(1/E) \wedge 1$, so that calibration is dominated by a randomized one.

## Sources

- N. Ignatiadis, R. Wang and A. Ramdas, *E-values as unnormalized weights in multiple testing*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad057> Section 3, Theorem 3.1 and Remark 3.2; proof in the supplement, Section S1.1.
