# Mean value analysis for closed product-form networks

In the closed network of [the Gordon–Newell product form](gordon-newell-networks.md), with $N$ stations of service rates $\mu_i$ and fixed throughput ratios $\lambda_j/\lambda_i$ given by a positive solution $\lambda$ of the traffic equations, let $EL_i(K)$, $\Lambda_i(K)$ and $ES_i(K)$ be the stationary mean number of customers at station $i$, its throughput and the mean sojourn time of a visit to it, when the network holds $K$ customers. Then $EL_i(0) = 0$ and for $K \ge 1$

$$
ES_i(K) = \frac{1}{\mu_i}\bigl( EL_i(K - 1) + 1 \bigr), \qquad
\Lambda_i(K) = \frac{K}{\sum_{j=1}^{N} \frac{\lambda_j}{\lambda_i} ES_j(K)}, \qquad
EL_i(K) = \Lambda_i(K)\, ES_i(K).
$$

These three relations, the arrival theorem, Little's law for the whole network and Little's law for station $i$, determine the exact stationary means for $K = 1, 2, \dots$ in turn, starting from $ES_i(1) = 1/\mu_i$, without computing the normalizing constant of the product form; each population costs $O(N)$ operations.

## Depends on

- [Product-form stationary distribution of a Gordon–Newell network](gordon-newell-networks.md)

## Proof depends on

- [The arrival theorem for closed product-form networks](the-arrival-theorem-for-closed-product-form-networks.md): an arriving customer finds on average $EL_i(K-1)$ customers at station $i$.
- [Little's law](../littles-law/littles-law.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Little's law in the stationary regime of a closed network, for a single station and for the whole network, with throughputs in the ratios $\lambda_j/\lambda_i$.

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, Section 7.8, equations (7.18)–(7.21) and the iteration that follows.
- E. D. Lazowska, J. Zahorjan, G. S. Graham and K. C. Sevcik, *Quantitative System Performance: Computer System Analysis Using Queueing Network Models*, Prentice-Hall, 1984, online edition <https://homes.cs.washington.edu/~lazowska/qsp/>, Chapter 6, Section 6.4.2.1, equations (6.1)–(6.4) and Algorithm 6.2 (the same recursion with service demands and think time).
