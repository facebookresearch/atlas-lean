# Preferential round robin with predicted sizes

For every $\lambda \in (0, 1)$, the *preferential round-robin* algorithm, which runs shortest-predicted-job-first at rate $\lambda$ and round robin at rate $1 - \lambda$ simultaneously, has competitive ratio at most $\min\left\{\frac{1}{\lambda}\left(1 + \frac{2\eta}{n}\right),\; \frac{2}{1 - \lambda}\right\}$ for total completion time. Hence it is $\frac{1}{\lambda}$-consistent and $\frac{2}{1-\lambda}$-robust.

## Proof sketch

Running two algorithms in parallel at rates $\lambda$ and $1 - \lambda$ makes each job complete no later than it would under either algorithm slowed by the corresponding factor. Round robin slowed by $1/(1-\lambda)$ gives the robustness bound by the round-robin lemma. Shortest-predicted-job-first slowed by $1/\lambda$ is compared with SPT: each misordered pair of jobs $i, j$ costs at most $|p_i - y_i| + |p_j - y_j|$, so its total cost is at most $\mathrm{OPT} + (n-1)\eta$; since all sizes are at least $1$, $\mathrm{OPT} \ge n(n+1)/2$ and $(n-1)\eta \le \frac{2\eta}{n}\mathrm{OPT}$.

## Depends on

- [Non-clairvoyant scheduling with predicted job sizes](nonclairvoyant-scheduling-with-predictions.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Round robin is 2-competitive for total completion time](round-robin-two-competitive.md)
- [Shortest processing time first minimizes total completion time](../../greedy-algorithms-and-matroids/single-machine-scheduling/shortest-processing-time-first-minimizes-total.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
