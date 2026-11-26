# Greedy influence maximization is a (1 − 1/e)-approximation

Whenever the influence function $\sigma$ is monotone and submodular with $\sigma(\emptyset) = 0$ (in particular in the independent cascade model, the linear threshold model, and general threshold models with submodular local thresholds), the greedy algorithm that adds $k$ seeds one at a time, each maximizing the marginal gain in $\sigma$, returns a set $S$ with $\sigma(S) \ge (1 - 1/e) \max_{|T| \le k} \sigma(T)$.

## Proof sketch

This is the Nemhauser–Wolsey–Fisher guarantee: each greedy step closes at least a $1/k$ fraction of the remaining gap to the optimum by submodularity, so after $k$ steps the gap is at most $(1 - 1/k)^k \le 1/e$ of the optimum.

## Depends on

- [General threshold, linear threshold and cascade models of influence](general-threshold-linear-threshold-and-cascade-models-of-influence.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [Influence in the independent cascade and linear threshold models is submodular](influence-in-the-independent-cascade-and-linear-threshold-models-is-submodular.md)
- [Mossel–Roch: local submodularity implies global submodularity](mossel-roch-local-submodularity-implies-global-submodularity.md)

## Sources

- George L. Nemhauser, Laurence A. Wolsey and Marshall L. Fisher, "An Analysis of Approximations for Maximizing Submodular Set Functions–-I", Mathematical Programming, 1978.
- David Kempe, Jon Kleinberg and Eva Tardos, "Maximizing the Spread of Influence through a Social Network", Proceedings of the Ninth ACM SIGKDD International Conference on Knowledge Discovery and Data Mining, 2003.
- Jon Kleinberg, "Cascading Behavior in Networks: Algorithmic and Economic Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
