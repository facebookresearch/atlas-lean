# Hiding among the clones: nearly optimal amplification by shuffling

Let $A_s$ apply local randomizers $R^{(1)}, \dots, R^{(n)}$, each $\varepsilon_0$-differentially private for every value of the earlier reports, to the $n$ records taken in uniformly random order. For every $\delta \in [0,1]$ with $\varepsilon_0 \le \log\big(\frac{n}{16\log(2/\delta)}\big)$, the shuffled output $A_s$ is $(\varepsilon,\delta)$-differentially private with

$$
\varepsilon \le \log\left(1 + \frac{e^{\varepsilon_0} - 1}{e^{\varepsilon_0} + 1}\left(\frac{8\sqrt{e^{\varepsilon_0}\log(4/\delta)}}{\sqrt{n}} + \frac{8 e^{\varepsilon_0}}{n}\right)\right),
$$

and in particular, under the same condition on $\varepsilon_0$,

$$
\varepsilon = O\!\left((1 - e^{-\varepsilon_0})\sqrt{\frac{e^{\varepsilon_0}\log(4/\delta)}{n}}\right),
$$

which has the asymptotically optimal dependence on $\varepsilon_0$. The simplification keeps $\log(4/\delta)$: with $\log(1/\delta)$ it would vanish at $\delta = 1$, where the explicit bound is still positive (for $0 < \delta \le 1/2$ the two forms agree up to constants). It follows because the condition on $\varepsilon_0$ makes the second term $8e^{\varepsilon_0}/n$ at most a constant multiple of the first, and $\log(1 + x) \le x$. If each local randomizer is only $(\varepsilon_0, \delta_0)$-DP, the shuffled output is $\big(\varepsilon, \delta + (e^{\varepsilon} + 1)(1 + e^{-\varepsilon_0}/2) n\delta_0\big)$-DP with the same $\varepsilon$. The analysis also yields an efficient numerical procedure computing tighter bounds and Rényi guarantees, and an asymptotically optimal analysis of noisy SGD with sampling without replacement.

## Proof sketch

By the clone reduction and post-processing it suffices to bound the privacy of the pair of count vectors. The total number of clones $C$ concentrates around $(n-1)e^{-\varepsilon_0}$, and conditioned on $C$ the counts differ only through one Bernoulli shift of a symmetric binomial with $C$ trials, whose likelihood ratio is within $1 \pm O(\sqrt{\log(1/\delta)/C})$ except with probability $\delta$ by Hoeffding's inequality. Multiplying by the bias $(e^{\varepsilon_0}-1)/(e^{\varepsilon_0}+1)$ of $\Delta$ and substituting $C \approx n e^{-\varepsilon_0}$ gives the bound.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Shuffled local reports reduce to a binomial clone-counting problem](shuffle-clone-reduction.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803, Theorems 3.1 and 3.8.
