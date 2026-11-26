# The arrival theorem for closed product-form networks

In the closed network of [the Gordon–Newell product form](gordon-newell-networks.md), with $N$ single-server first-come first-served exponential stations and $K \ge 1$ customers, consider the stationary regime. When a customer leaves a station, the joint distribution of the numbers of customers at all stations at that jump epoch, not counting the jumping customer, equals the stationary distribution of the same network with $K - 1$ customers. The jumping customer thus sees the rest of the network in equilibrium as if it were not there, the counterpart for closed networks of Poisson arrivals seeing time averages in open ones.

## Depends on

- [Product-form stationary distribution of a Gordon–Newell network](gordon-newell-networks.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- the Palm distribution of a stationary continuous-time Markov chain at the epochs of a given class of transitions, here the jumps of one customer from one station to the next;
- the computation, from the product form, of the rate of such jumps out of each state, which is proportional to the product-form weight of the network with one customer fewer.

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, Section 7.8 (the arrival theorem of Lavenberg and Reiser, also due to Sevcik and Mitrani, and Remark 7.14).
