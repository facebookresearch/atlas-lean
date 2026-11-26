# Random dictatorship is strategyproof and (2 − 2/n)-approximate

On any pseudometric space with $n \ge 1$ agents, the random dictatorship mechanism, placing the facility at a uniformly random agent's reported location, is strategyproof and has social-cost approximation ratio $2 - 2/n$ (hence at most $2$). Weak group strategyproofness fails on a three-leaf star.

## Proof sketch

An agent affects only the outcome in which it is the dictator, where truth gives it cost $0$. For the ratio, with optimal location $y^*$, the triangle inequality bounds $\sum_{i,j} d(x_i, x_j) \le 2(n-1) \sum_i d(x_i, y^*)$, and the expected cost is this sum divided by $n$.

## Depends on

- [Facility-location mechanism on a metric space](facility-location-mechanism-on-a-metric-space.md)

## Sources

- Noga Alon, Michal Feldman, Ariel D. Procaccia and Moshe Tennenholtz, "Strategyproof Approximation of the Minimax on Networks", Mathematics of Operations Research, 2010.
