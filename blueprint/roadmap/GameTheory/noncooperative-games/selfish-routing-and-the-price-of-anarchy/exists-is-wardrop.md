# Existence of Wardrop equilibria

Consider a nonatomic routing instance in which every latency function $\ell_e$ is continuous on
$[0, \infty)$ and every commodity has at least one path. Then for every demand vector $r$ with
$r_i \ge 0$ there is a flow feasible for $r$ that is a Wardrop equilibrium.

The proof is Beckmann's: the feasible flows form a nonempty compact set, so the Beckmann potential

$$\Phi(f) = \sum_{e \in E} \int_0^{f_e} \ell_e(x)\, dx$$

attains its minimum on it. At a minimiser $f$, if a path $P$ with $f_P > 0$ had larger latency than
a path $Q$ of the same commodity, moving a small amount $\delta$ of traffic from $P$ to $Q$ would
change $\Phi$ at rate $\ell_Q(f) - \ell_P(f) < 0$, a contradiction. Monotonicity of the latencies
is not needed for existence; it makes $\Phi$ convex, and then every Wardrop equilibrium minimises
$\Phi$ and all have the same cost.

The path hypothesis cannot be dropped: a commodity with positive demand and no path has no
feasible flow.

## Background

- [All Wardrop equilibria have the same cost](cost-eq.md): uniqueness of the equilibrium cost,
  the other half of Beckmann et al.'s result.

## Sources

- M. Beckmann, C. B. McGuire and C. B. Winsten, *Studies in the Economics of Transportation*,
  Yale University Press, 1956.
- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Lemma 2.9
  (§2.4; stated there for continuous nondecreasing latencies) and §2.3 (the convex program).
