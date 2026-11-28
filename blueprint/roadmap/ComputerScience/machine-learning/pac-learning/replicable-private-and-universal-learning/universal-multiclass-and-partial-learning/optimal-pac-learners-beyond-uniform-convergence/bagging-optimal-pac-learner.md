# Bagging with logarithmically many bootstrap samples is an optimal PAC learner

Let $H \subseteq \{0,1\}^X$ have VC dimension $d$. Consider the learner that, from a training sample $S$ of size $m$, draws $t \ge 18\ln(2m/\delta)$ bootstrap samples of a size $n$ with $0.02m \le n \le m$ (sampling with replacement from $S$), runs an arbitrary empirical risk minimizer for $H$ on each, and outputs the majority vote. Then there is a universal constant $a$ such that for every realizable $D$ and every $\delta \in (0,1)$, with probability at least $1-\delta$ over $S$ and the bootstrap draws,

$$
\mathrm{er}_D(\hat h) \le a\,\frac{d + \ln(1/\delta)}{m},
$$

matching the lower bound for all PAC learners. In contrast, an individual empirical risk minimizer can incur an extra $\log(1/\varepsilon)$ factor.

## Proof sketch

Following Hanneke's analysis of recursive subsample majorities, a point is misclassified by the majority only if a constant fraction of the voters err there. With $t \ge 18\ln(2m/\delta)$ draws, the empirical distribution of the bootstrap ERMs is, with probability $1 - \delta/2$, close to the distribution of an ERM on a random bootstrap sample, so it suffices to bound the mass of points where at least a constant fraction of random bootstrap ERMs err; this is done by a uniform convergence argument over the class of VC dimension $d$, applied to the regions where ERMs trained on random subsets disagree with the target, and gives mass $O((d + \ln(1/\delta))/m)$.

## Depends on

- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)
- [Fundamental theorem of statistical learning (binary, 0-1 loss)](../../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/fundamental-theorem-of-statistical-learning.md)

## Sources

- K. G. Larsen, "Bagging is an Optimal PAC Learner", COLT (2023), arXiv:2212.02264, Theorem 1 and Lemmas 1–6.
- S. Hanneke, "The Optimal Sample Complexity of PAC Learning", Journal of Machine Learning Research 17 (2016), arXiv:1507.00473.
