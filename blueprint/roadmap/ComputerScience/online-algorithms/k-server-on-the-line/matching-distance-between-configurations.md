# Matching distance between server configurations

For configurations $s, s' : [k] \to M$ of $k$ servers in a metric space $(M, d)$, the *matching distance* is

$$
d_{\mathrm{match}}(s, s') = \min_{\pi \in S_k} \sum_{i=1}^k d\left(s_i, s'_{\pi(i)}\right),
$$

the cheapest cost of moving the servers of $s$ onto those of $s'$ when relabelling is free. It is a pseudometric on configurations and lower-bounds the cost of any schedule from $s$ that ends in $s'$.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- M. S. Manasse, L. A. McGeoch and D. D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2), 1990.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
