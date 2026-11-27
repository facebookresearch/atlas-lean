# Order-statistic mechanisms on the line

On $\mathbb{R}$ with sum-of-distances cost, both the lower and upper medians minimize social cost, so the median mechanism is optimal and strategyproof, whereas the mean is not strategyproof. For the maximum-cost objective every point between the extreme reports gives a $2$-approximation, no deterministic strategyproof mechanism does better than $2$, the randomized left-right-middle mechanism (each extreme with probability $1/4$, the midpoint with probability $1/2$) is strategyproof with ratio $3/2$, and no randomized strategyproof mechanism does better than $3/2$.

## Proof sketch

Every mechanism placing the facility at a fixed order statistic $x_{(k)}$ of the reports is group strategyproof in the strong sense: any joint misreport by a coalition that changes the outcome makes some member strictly worse off. Let $a = x_{(k)}$ at the true locations. If the coalition moves the outcome to $a' > a$ while every member is located above $a$, the at least $k$ reports at or below $a$ all come from non-members and are unchanged, so the new $k$-th smallest report is still at most $a$, a contradiction; hence some member is located at or below $a < a'$ and is strictly worse off. The case $a' < a$ is symmetric, using the at least $n - k + 1$ reports at or above $a$. The median balances left and right counts, minimizing the sum of distances. For maximum cost, the extreme agents control the bounds, and lower bounds follow from two-agent profiles.

## Depends on

- [Facility-location mechanism on a metric space](facility-location-mechanism-on-a-metric-space.md)
- [The median mechanism is group strategyproof](strategyproof-facility-location-on-the-line/median-is-group-strategyproof.md)

## Sources

- Ariel D. Procaccia and Moshe Tennenholtz, "Approximate Mechanism Design without Money", ACM Transactions on Economics and Computation, 2013.
- Herve Moulin, "On Strategy-Proofness and Single Peakedness", Public Choice, 1980.
