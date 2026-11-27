# Tail bound for the centered binomial distribution

Let $\eta \ge 1$ and let $X = \sum_{i=1}^{\eta} a_i - \sum_{i=1}^{\eta} b_i$ where all $a_i, b_i$ are independent uniform bits (the centered binomial distribution with parameter $\eta$, as in FIPS 203, Section 4.2.2). Then for every $B > 0$,

$$\Pr[|X| \ge B] \le 4\exp\!\left(-\frac{B^2}{2\eta}\right).$$

## Proof sketch

If $|X| \ge B$ then one of the two counts deviates from its mean $\eta/2$ by at least $B/2$ in the appropriate direction. Hoeffding's inequality (Hoeffding, Theorem 2) bounds each of the four one-sided deviations by $\exp(-2(B/2)^2/\eta)$, and a union bound gives the constant $4$.

## Depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Wassily Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association 58(301), 1963.
- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
