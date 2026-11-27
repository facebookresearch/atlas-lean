# Ctr Fresh

For query counters $\rho \in (\mathbb{Z}/N)^q$ and a challenge counter $r_s \in \mathbb{Z}/N$, the challenge counter range is fresh when

$$
\rho_j + i' \ne r_s + i \quad \text{in } \mathbb{Z}/N \text{ for every } j < q \text{ and all } i, i' < \ell.
$$

The test is against all $q$ pre-sampled counter ranges, including those of tape entries the adversary never uses, not only the queries it actually issues. The predicate is decidable.
