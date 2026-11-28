# Chebyshev bound on the defect probability

Let $X$ be a real random variable with finite variance, mean $\mu$ and standard deviation $\sigma > 0$, and let the specification
limits have $C_{pk} > 0$, so that $\mathrm{LSL} < \mu < \mathrm{USL}$. Every value outside the limits satisfies
$\lvert X - \mu\rvert > 3\sigma C_{pk}$, so by Chebyshev's inequality

$$P(X < \mathrm{LSL} \text{ or } X > \mathrm{USL}) \le \frac{1}{9 C_{pk}^2} .$$

The indices do not determine the defect probability: for limits $[7, 13]$, the law with mass $15/16$ at $10$ and $1/32$ at each of
$6$ and $14$ has mean $10$, variance $1$ and defect probability $1/16$, while the law with mass $1/2$ at each of $9$ and $11$ has
the same moments and no defects. Defect rates in parts per million computed from $C_{pk}$ assume a normal law and are not
distribution-free. One-sided bounds are a different result.

## Depends on

- [Process capability indices](process-capability-indices.md)

## Proof depends on

- [Chebyshev's inequality](../../moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Sources

- NIST/SEMATECH *e-Handbook of Statistical Methods*, Section 6.1.6, process capability indices $C_p$ and $C_{pk}$ and $C_{pk} = C_p(1 - k)$, <https://www.itl.nist.gov/div898/handbook/pmc/section1/pmc16.htm>.
