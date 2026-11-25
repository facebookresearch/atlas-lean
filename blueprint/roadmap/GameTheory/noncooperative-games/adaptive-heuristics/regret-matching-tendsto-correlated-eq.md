# Regret matching leads to correlated equilibria

Let $|c_i| \le M$ and $\mu > 2M(|S_i| - 1)$ for every player $i$. If the first round is
arbitrary and, given the history, the players choose the next round's actions independently, each
according to regret matching, then almost surely the empirical distributions of play converge to
the set of correlated equilibria. Convergence is to the set, not to a point.

## Informally uses

- [No conditional regret characterises correlated equilibria](../correlated-equilibria/is-correlated-eq-empirical-iff.md):
  the positive parts of the average conditional regrets tending to zero is the same as convergence to
  the set (the Proposition of §3; Hart 2005,
  §4, describes the proof as these two steps).

## Background

- [Blackwell's condition for regret-invariant play](../correlated-equilibria/sum-mul-sub-eq-zero-of-is-regret-invaria.md):
  the approachability computation for the regret-eigenvector strategies of Theorem A, whose study
  inspired the procedure and its proof.
- [Blackwell's approachability theorem](../blackwell-approachability/blackwell-approachability.md):
  the tool that inspired the procedure.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, Main Theorem (§2), footnote 5; proof in the Appendix.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §4, Theorem 1.
