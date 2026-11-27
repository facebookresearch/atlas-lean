# Proportionally fair allocations are Pareto-efficient

Every [proportionally fair](proportionally-fair-rate-allocations.md) allocation is [Pareto-efficient](pareto-efficient-rate-allocations.md). If $y$ is feasible with $y_i > x_i$, then $(y_i - x_i)/x_i > 0$ and the proportional changes sum to at most $0$, so some term $(y_s - x_s)/x_s$ is negative, that is $y_s < x_s$.

## Depends on

- [Proportionally fair rate allocations](proportionally-fair-rate-allocations.md)
- [Pareto-efficient rate allocations](pareto-efficient-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.2, Theorem 1.2.5 with its proof.
