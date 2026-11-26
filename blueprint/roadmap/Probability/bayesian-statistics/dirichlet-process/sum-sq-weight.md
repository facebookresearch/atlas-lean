# Expected sum of squared stick-breaking weights

For a [stick-breaking process](stick-breaking-process.md) on $(\Omega, \mu)$ with random weights $\pi_k$, the quantity

$$s = \sum_{k \ge 0} \int \max(\pi_k, 0)^2\, d\mu \in [0, \infty].$$

Given $G$, two independent draws from $G$ pick the same piece with probability $\sum_k \pi_k^2$, so $s$ is the probability that two draws pick the same piece. For an atomless base measure the atoms are almost surely distinct, so $s$ is also the probability that the two draws coincide.
