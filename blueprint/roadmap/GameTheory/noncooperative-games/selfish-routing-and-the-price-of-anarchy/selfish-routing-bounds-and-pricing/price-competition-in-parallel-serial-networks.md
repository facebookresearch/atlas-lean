# Price competition in parallel-serial networks

In a parallel-serial network, traffic routes over parallel paths each consisting of serial links owned by distinct profit-maximizing providers, with path latency and price equal to the sums over the path's links. Weak pure-strategy oligopoly equilibria can have arbitrarily small efficiency because of double marginalization. Every strict oligopoly equilibrium (in which each provider's price is its unique best response) at which all traffic is transmitted, with smooth convex nondecreasing latencies satisfying $\ell(0) = 0$ on every link, achieves at least half of the optimal social surplus, and the bound $1/2$ is tight.

## Proof sketch

On each path, serial providers jointly over-price relative to a single owner; at a strict equilibrium each provider's markup is bounded by the path latency derivative, which yields a surplus bound of one half via the same envelope argument as for parallel links.

## Depends on

- [Priced Wardrop equilibrium with reservation utility](priced-wardrop-equilibrium-with-reservation-utility.md)

## Proof depends on

- [Oligopoly pricing on parallel links achieves at least 5/6 of the optimal surplus](oligopoly-pricing-on-parallel-links-achieves-at-least-5-6-of-the-optimal-surplus.md)

## Sources

- Daron Acemoglu and Asuman Ozdaglar, "Competition in Parallel-Serial Networks", IEEE Journal on Selected Areas in Communications, 2007.
- Asuman Ozdaglar and R. Srikant, "Incentives and Pricing in Communications Networks", Algorithmic Game Theory, Cambridge University Press, 2007.
