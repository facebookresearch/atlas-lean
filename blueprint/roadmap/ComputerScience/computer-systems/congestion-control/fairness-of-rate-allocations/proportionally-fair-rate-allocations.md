# Proportionally fair rate allocations

A feasible allocation $x$ in the [network model](network-model-and-feasible-rate-allocations.md) is *proportionally fair* if all its rates are positive and every feasible $y$ satisfies

$$
\sum_{s=1}^{S} \frac{y_s - x_s}{x_s} \le 0 :
$$

any change of allocation has a nonpositive aggregate of proportional changes. In the parking-lot network of four links of capacity $c$ in series, one long source crossing all four and one short source on each link, the max-min fair allocation gives every source $c/2$, while the proportionally fair one gives the long source $c/5$ and each short source $4c/5$.

## Depends on

- [Network model and feasible rate allocations](network-model-and-feasible-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.2, Definition 1.2.3, the parking-lot example of Figure 1.6 and the example after Theorem 1.2.6.
- F. P. Kelly, "Charging and rate control for elastic traffic", *European Transactions on Telecommunications* 8(1):33–37, 1997, where proportional fairness is introduced for rate control.
