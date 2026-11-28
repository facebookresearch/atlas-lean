# Oligopoly pricing on parallel links achieves at least 5/6 of the optimal surplus

Let profit-maximizing providers own disjoint sets of parallel links with smooth convex nondecreasing latencies satisfying $\ell_i(0) = 0$ (zero latency at zero flow) and set per-unit prices anticipating users' priced Wardrop routing (with reservation utility). At every pure-strategy oligopoly equilibrium at which each link carrying positive flow with zero latency is the only link its owner owns (automatic when latencies are strictly increasing or each provider owns one link), the social surplus is at least $5/6$ of the optimal social surplus, for any number of links and any ownership structure. The bound is tight: for every number $I \ge 2$ of links there is an instance, with each link owned by a different provider, attaining exactly $5/6$.

## Proof sketch

At equilibrium each provider charges its Pigovian cost plus a markup bounded by the competing links' slopes; replacing latencies by their linearizations at equilibrium only lowers the ratio, and a quadratic weak-duality envelope link by link bounds the surplus loss by $1/6$ of the optimum.

## Depends on

- [Priced Wardrop equilibrium with reservation utility](priced-wardrop-equilibrium-with-reservation-utility.md)

## Proof depends on

- [Existence of priced Wardrop equilibria and efficiency of Pigovian and monopoly prices](existence-of-priced-wardrop-equilibria-and-efficiency-of-pigovian-and-monopoly-p.md)

## Sources

- Daron Acemoglu and Asuman Ozdaglar, "Competition and Efficiency in Congested Markets", Mathematics of Operations Research, 2007.
- Asuman Ozdaglar and R. Srikant, "Incentives and Pricing in Communications Networks", Algorithmic Game Theory, Cambridge University Press, 2007.
