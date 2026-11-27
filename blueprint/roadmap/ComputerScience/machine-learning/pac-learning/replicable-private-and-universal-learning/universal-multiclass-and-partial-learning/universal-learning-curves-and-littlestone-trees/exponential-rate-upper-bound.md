# Classes with no infinite Littlestone tree are learnable at exponential rate

Let $X$ be a Polish space and $H \subseteq \{0,1\}^X$ a measurable class (in the sense of the source) with no infinite Littlestone tree. Then $H$ is learnable at rate $R(n) = e^{-n}$: there is a learner such that for every realizable distribution $P$ there are constants $C, c > 0$ (depending on $P$) with

$$
\mathbb{E}\big[\mathrm{er}_P(\hat h_n)\big] \le C e^{-cn} \quad \text{for all } n \ge 1 .
$$

## Proof sketch

Run the universally measurable online learner that makes finitely many mistakes on every realizable sequence on i.i.d. data; since $P$ is realizable, the probability that its hypothesis after $t$ examples has positive error tends to $0$ as $t \to \infty$. From part of the sample, estimate (by a rule not depending on $P$) a time $\hat t_n$ at which this failure probability is below a fixed constant, with the estimate correct except on an event of probability $e^{-\Omega(n)}$. Run independent copies of the online learner for $\hat t_n$ steps on $\Theta(n)$ disjoint batches of the remaining sample and output the majority vote; by Hoeffding's inequality more than half of the copies have zero error except with probability $e^{-\Omega(n)}$, and then the vote has zero error, which bounds the expected error.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Proof depends on

- [No infinite Littlestone tree gives an online learner with finitely many mistakes](eventually-correct-online-learner.md)
- [The learning game is determined, and the adversary wins exactly on an infinite Littlestone tree](gale-stewart-determinacy.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Theorem 4.1 (Lemmas 4.3 and 4.4, Corollary 4.5) and Corollary 3.5.
