# Direct product lemma for statistical distance

Let $\mu, \nu$ be distributions on a finite set with $\delta = \delta(\mu, \nu)$, and let $k \ge 1$. Then

$$
1 - 2\exp\Big(-\frac{k\delta^2}{2}\Big) \le \delta\big(\mu^{\otimes k}, \nu^{\otimes k}\big) \le k\,\delta.
$$

## Proof sketch

The upper bound is the hybrid bound for products. For the lower bound, let $S = \{x : \mu(x) > \nu(x)\}$, so $\mu(S) - \nu(S) = \delta$, and distinguish by counting coordinates in $S$ against the midpoint threshold $k(\mu(S) + \nu(S))/2$. Hoeffding's inequality bounds the probability of crossing the threshold under either distribution by $e^{-k\delta^2/2}$, so this test has advantage at least $1 - 2e^{-k\delta^2/2}$.

## Depends on

- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Statistical distance of products and with shared public samples](statistical-distance-products-and-shared-samples.md)
- [Hoeffding's inequality for averages of bounded variables](../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- A. Sahai and S. Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003.
- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association 58(301), 1963.
