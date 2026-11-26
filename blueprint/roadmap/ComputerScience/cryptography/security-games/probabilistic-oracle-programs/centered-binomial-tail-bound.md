# Tail bound for the centered binomial distribution

Let $\eta \ge 1$ and let $X = \sum_{i=1}^{\eta} a_i - \sum_{i=1}^{\eta} b_i$ where all $a_i, b_i$ are independent uniform bits (the centered binomial distribution with parameter $\eta$). Then for every $B > 0$,

$$\Pr[|X| \ge B] \le 4\exp\!\left(-\frac{B^2}{2\eta}\right).$$

## Proof sketch

If $|X| \ge B$ then one of the two counts deviates from its mean $\eta/2$ by at least $B/2$ in the appropriate direction. Hoeffding's inequality bounds each of the four one-sided deviations by $\exp(-2(B/2)^2/\eta)$, and a union bound gives the constant $4$.

## Depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- C. Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science 10(4), 2016.
