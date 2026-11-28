# Quotient combiner of an independent p-value and e-value

For a null hypothesis $H$, a p-value is a random variable $P$ with values in $[0, 1]$ that is [valid](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md) under $H$, $\Pr(P \le t) \le t$ for all $t \in [0, 1]$, and an e-value is a random variable $E$ with values in $[0, \infty]$ and $\mathbb{E}[E] \le 1$ under $H$. Define the quotient combiner $Q : [0, 1] \times [0, \infty] \to [0, 1]$,

$$Q(p, e) = \frac{p}{e} \wedge 1$$

(with $0/0 = 0$, $p/0 = \infty$ for $p > 0$ and $p/\infty = 0$, so $Q(0, 0) = 0$; setting $Q(0, 0) = 1$ would make $Q$ inadmissible since replacing $Q(0, 0)$ by $0$ preserves validity because $\Pr(P = 0) = 0$ for every valid p-value $P$). **Theorem.** If $P$ and $E$ are independent under $H$, then $Q(P, E)$ is a valid p-value, and $Q$ is admissible in the source's class: no function $F : [0, 1] \times [0, \infty] \to [0, 1]$ that is nondecreasing in $p$, nonincreasing in $e$, and returns a valid p-value $F(P, E)$ for every independent valid p-value $P$ and e-value $E$ satisfies $F \le Q$ pointwise with $F(p, e) < Q(p, e)$ for some $(p, e)$.

## Depends on

- [Valid p-value](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)

## Expansion

Fix $0 < t < 1$. Conditional on $E = e \in (0, \infty)$, $\Pr(P/e \le t \mid E = e) = \Pr(P \le te) \le te$ by independence; on $\{E = 0\}$, $Q(P, 0) \le t$ forces $P = 0$, which has probability $0$; and $\Pr(E = \infty) = 0$ since $\mathbb E[E] \le 1$. Taking expectations, $\Pr(Q(P, E) \le t) \le t\, \mathbb{E}[E] \le t$ (supplement, Section S1.1(ii)). At $t = 1$ validity is automatic because $Q \le 1$, and at $t = 0$, $\Pr(Q(P, E) = 0) \le \Pr(P = 0) + \Pr(E = \infty) = 0$. A consequence noted in the paper: with $U \sim U(0, 1)$ independent of $E$, $Q(U, E)$ is a valid p-value with $Q(U, E) \le (1/E) \wedge 1$ for every $E$ (weakly better than the e-to-p calibration), strictly smaller with positive probability whenever $\Pr(E > 0) > 0$; for $E \equiv 0$ both equal $1$ almost surely.

## Sources

- N. Ignatiadis, R. Wang and A. Ramdas, *E-values as unnormalized weights in multiple testing*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad057> Section 3.1, Theorem 3.1 and Remark 3.2; proof in the supplement, Section S1.1(ii). Section numbering follows the authors' manuscript; the journal's numbering may differ.
