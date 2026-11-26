# Nemhauser-Wolsey-Fisher: greedy is a (1 - 1/e)-approximation under a cardinality constraint

Let $f : 2^E \to \mathbb{R}$ be monotone submodular with $f(\emptyset) \ge 0$ and $k \ge 1$. The greedy algorithm that $k$ times adds an element of maximum marginal gain returns $G$ with $|G| \le k$ and

$$
f(G) \ge \Big(1 - \big(1 - \tfrac{1}{k}\big)^{k}\Big) f(O) \ge \Big(1 - \frac{1}{e}\Big) f(O)
$$

for every $O \subseteq E$ with $|O| \le k$. The factor $1 - (1 - 1/k)^k$ is exact for the greedy algorithm: for every $k \ge 1$ there is a nonnegative monotone submodular instance on $2k$ elements on which greedy attains exactly this ratio.

## Proof sketch

By diminishing returns, $f(O) - f(G_i) \le k\,(f(G_{i+1}) - f(G_i))$, so the gap shrinks by a factor $1 - 1/k$ per step.

## Depends on

- [Submodular set function](../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms/approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Diminishing marginal returns characterize submodularity](diminishing-marginal-returns.md)

## Sources

- G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, "An Analysis of Approximations for Maximizing Submodular Set Functions I", Mathematical Programming 14, 1978.
- G. L. Nemhauser and L. A. Wolsey, "Best Algorithms for Approximating the Maximum of a Submodular Set Function", Mathematics of Operations Research 3(3), 1978.
