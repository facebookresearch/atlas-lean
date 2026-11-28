# Minimum-cost flow in almost-linear time with high probability

There is a randomized algorithm that, on a directed graph $G$ with $m$ edges, integral vertex demands, integral lower and upper edge capacities bounded by $U$ in absolute value and integral edge costs bounded by $C$ in absolute value, computes an exact minimum-cost flow, or reports infeasibility, in time

$$
m^{1+o(1)}\log U\log C
$$

with high probability, that is with probability at least $1 - n^{-c}$ for any fixed constant $c$.

## Proof sketch

By capacity and cost scaling it suffices to treat $U, C \le \mathrm{poly}(m)$, at the price of the $\log U\log C$ factor. Combine the reduction *The l1 IPM reduces min-cost flow to an approximate dynamic min-ratio cycle problem* with $\kappa = m^{-o(1)}$ and the randomized data structure *Randomized dynamic min-ratio cycle data structure under hidden stable flow chasing*, whose total time over $m^{1+o(1)}$ updates is $m^{1+o(1)}$, started from *An initial IPM point with polynomially bounded potential* (which also detects infeasibility), to obtain a flow of cost within $(mU)^{-10}$ of optimal on a randomly perturbed instance. Rounding by *Random cost perturbation makes a near-optimal flow round to an optimal integral flow* yields an exact optimum with probability at least $1/2$; running $O(\log n)$ independent repetitions and returning the cheapest feasible rounded flow fails only with probability $n^{-c}$.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Proof depends on

- [The l1 IPM reduces min-cost flow to an approximate dynamic min-ratio cycle problem](ipm-reduces-to-dynamic-min-ratio-cycle.md)
- [Randomized dynamic min-ratio cycle data structure under hidden stable flow chasing](../dynamic-min-ratio-cycle-data-structures/randomized-dynamic-min-ratio-cycle.md)
- [Random cost perturbation makes a near-optimal flow round to an optimal integral flow](isolation-perturbation-rounding.md)
- [An initial IPM point with polynomially bounded potential](ipm-initial-point-construction.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
