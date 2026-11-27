# Max-min fairness is the limit of utility fairness

Let $(f_m)_{m \in \mathbb R_+}$ be increasing, differentiable, strictly concave functions on $[0, \infty)$ such that $\lim_{m \to \infty} f_m'(x + \delta)/f_m'(x) = 0$ for all $x \ge 0$ and $\delta > 0$ (for example $f_m(x) = 1 - (1 + x)^{-m}$, for which the ratio is $((1 + x)/(1 + x + \delta))^{m+1}$), and let $x^m$ be the unique feasible allocation in the [network model](network-model-and-feasible-rate-allocations.md) maximizing $\sum_s f_m(x_s)$, every source using at least one link. Then $x^m$ converges to the [max-min fair](max-min-fair-rate-allocations.md) allocation as $m \to \infty$. So max-min fairness is a limiting case of utility fairness.

**Proof.** The $x^m$ lie in the compact feasible set, so they have accumulation points; each is the max-min fair allocation, which is unique, so the whole family converges to it.

## Depends on

- [Utility-fair rate allocations](utility-fair-rate-allocations.md)
- [Max-min fair rate allocations](max-min-fair-rate-allocations.md)

## Proof depends on

- [Accumulation points of utility-fair allocations are max-min fair](accumulation-points-of-utility-fair-allocations-are-max-min-fair.md)
- [Uniqueness of the max-min fair allocation](uniqueness-of-the-max-min-fair-allocation.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.4, Theorem 1.2.7 with its proof.
