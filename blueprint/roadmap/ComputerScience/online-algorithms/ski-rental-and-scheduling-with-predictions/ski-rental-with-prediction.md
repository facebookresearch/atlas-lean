# Ski rental with a predicted number of days

In *ski rental with a prediction*, renting costs $1$ per day, buying costs $b \ge 1$ once, and the true number of skiing days $x \ge 1$ is unknown; the algorithm receives a prediction $y$ of $x$ before the first day. The offline optimum is $\mathrm{OPT} = \min\{x, b\}$, and the prediction error is $\eta = |x - y|$. A deterministic algorithm is described by the day on which it buys (if it is still skiing).

## Depends on

- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)
- [Cost of a ski-rental strategy](../ski-rental-problem/cost.md)
- [Offline optimum for ski rental](../ski-rental-problem/opt.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
