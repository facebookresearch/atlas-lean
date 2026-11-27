# Smooth mechanism

A single-parameter mechanism $M$ is *$(\lambda, \mu)$-smooth* with respect to feasible allocations $X$ if for every nonnegative valuation profile $v$ and every $x \in X$ each bidder $i$ has a finitely supported distribution $D_i$ over bids, depending only on $v$ and $x$, such that for every bid profile $b$, $\sum_i \mathbb{E}_{z \sim D_i}[u_i(v_i; z, b_{-i})] \ge \lambda \sum_i v_i x_i - \mu \sum_i p_i(b)$.

## Depends on

- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)
- [Smooth game](../../noncooperative-games/no-regret-dynamics/is-smooth.md)

## Sources

- Vasilis Syrgkanis and Eva Tardos, "Composable and Efficient Mechanisms", Proceedings of the 45th Annual ACM Symposium on Theory of Computing (STOC 2013), 2013.
- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015.
