# Classes with no infinite Littlestone tree are learnable at exponential rate

If $H \subseteq \{0,1\}^X$ has no infinite Littlestone tree, then $H$ is learnable at rate $R(n) = e^{-n}$: there is a learner such that for every realizable distribution $P$ there are constants $C, c > 0$ (depending on $P$) with

$$
\mathbb{E}\big[\mathrm{er}_P(\hat h_n)\big] \le C e^{-cn} \quad \text{for all } n \ge 1 .
$$

## Proof sketch

Feed i.i.d. examples to the eventually-correct online learner; with probability one it stops erring after a random finite time, so for $t$ large enough its current hypothesis has error at most $1/4$ with probability at least $3/4$. Split the sample into blocks of growing length, estimate from data a block length after which the online learner has stabilized, run independent copies on $\Theta(n)$ disjoint blocks and output the majority vote. Each copy fails independently with probability at most $1/4$, so by Hoeffding's inequality the majority fails with probability $e^{-\Omega(n)}$, which bounds the expected error.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Proof depends on

- [No infinite Littlestone tree gives an online learner with finitely many mistakes](eventually-correct-online-learner.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
