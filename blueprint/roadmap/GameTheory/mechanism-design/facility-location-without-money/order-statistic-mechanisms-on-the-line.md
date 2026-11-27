# Order-statistic mechanisms on the line

On $\mathbb{R}$ with sum-of-distances cost, every mechanism placing the facility at a fixed order statistic $x_{(k)}$ of the reports is group strategyproof (in the strong sense). Both the lower and upper medians minimize social cost, so the median mechanism is optimal and strategyproof, whereas the mean is not strategyproof. For the maximum-cost objective every point between the extreme reports gives a $2$-approximation, no deterministic strategyproof mechanism does better than $2$, the randomized left-right-middle mechanism (each extreme with probability $1/4$, the midpoint with probability $1/2$) is strategyproof with ratio $3/2$, and no randomized strategyproof mechanism does better than $3/2$.

## Proof sketch

A coalition can move the $k$-th order statistic only by having members cross it, which moves it away from them. The median balances left and right counts, minimizing the sum of distances. For maximum cost, the extreme agents control the bounds, and lower bounds follow from two-agent profiles.

## Depends on

- [Facility-location mechanism on a metric space](facility-location-mechanism-on-a-metric-space.md)
- [The median mechanism is group strategyproof](../../not-yet-classified/part-01/facility-location/median-is-group-strategyproof.md)

## Sources

- Ariel D. Procaccia and Moshe Tennenholtz, "Approximate Mechanism Design without Money", ACM Transactions on Economics and Computation, 2013.
- Herve Moulin, "On Strategy-Proofness and Single Peakedness", Public Choice, 1980.
