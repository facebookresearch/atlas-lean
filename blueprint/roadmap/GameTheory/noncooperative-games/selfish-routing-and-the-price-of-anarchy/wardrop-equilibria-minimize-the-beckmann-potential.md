# Wardrop equilibria are the minimizers of the Beckmann potential

In a nonatomic routing instance with finitely many edges, finitely many commodities and finitely many allowed paths, nonnegative demands, no edge capacities, and edge latency functions $\ell_e$ that are continuous and nondecreasing on $[0, \infty)$, a feasible flow is a Wardrop equilibrium if and only if it is a global minimum of the Beckmann potential $\Phi(f) = \sum_e \int_0^{f_e} \ell_e(x)\,dx$ over feasible flows. Consequently, if every $\ell_e$ is strictly increasing, all equilibria have the same edge flows, since they have the same edge latencies; their path flows need not be unique.

Proof. $\Phi$ is convex in the edge flows because each $\ell_e$ is nondecreasing, so $\Phi(g) - \Phi(f) \ge \sum_e \ell_e(f_e)(g_e - f_e)$ for feasible $f, g$. If $f$ is an equilibrium, the variational inequality makes the right side nonnegative, so $f$ minimizes $\Phi$. Conversely, if $f$ minimizes $\Phi$ and some path $P$ with $f_P > 0$ had larger latency than a path $Q$ of the same commodity, moving a small amount of flow from $P$ to $Q$ keeps feasibility and changes $\Phi$ at rate $\ell_Q(f) - \ell_P(f) < 0$ by continuity of the latencies, a contradiction.

## Depends on

- [Nonatomic routing instance](routing-instance.md): nonatomic routing instances.
- [Wardrop equilibrium](is-wardrop.md): the equilibrium condition.

## Proof depends on

- [Variational inequality for Wardrop equilibria](cost-le-sum-latency-mul-edge-flow.md): the variational inequality of an equilibrium.
- [Wardrop equilibria have unique edge latencies](latency-edge-flow-eq.md): equilibria induce the same edge latencies.

## Background

- [Existence of Wardrop equilibria](exists-is-wardrop.md): existence of equilibria by minimizing the potential.

## Sources

- N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, chapter 18 (T. Roughgarden), Theorem 18.8 and Proposition 18.11
